import GGMCollatz.Tao.Basic.Valuation
import GGMCollatz.Tao.Prob.Geometric

/-!
# The Syracuse random variable `𝒮_n` (modulo `q^n`) (counterpart of tao-collatz's node C4)

Derived from `TaoCollatz/Syracuse/SyracRV.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r). GGM (arXiv:2111.06170) §4, equations (4.1)-(4.3).

`𝒮 = Σ_{i≥1} q^{i-1} p^{-𝒢_{1,i}} 𝒰_i` (`q`-adic), `𝒮_n = 𝒮 mod q^n`. `𝒢` is an independent sequence of `G(μ)`,
`𝒰_i = r(j_i)` with `j_i` uniform on `{1, …, p-1}`, all independent. Here we define it as the pushforward of the
i.i.d. vector `v : Fin n → ℕ × ℕ` with the one-step law `stepLaw p` of the pair `(𝒢_i, j_i)` (the reversed form
of tao-collatz's (1.26); for `p = 2`, `q = 3`, `r(1) = 1` this is tao-collatz's `syracZ`). `p` is invertible modulo
`q^n` (condition (a)).

* `syracZ_map_cast`: compatibility with projections (GGM (4.4), tao-collatz's (1.22)).
* `syracZ_recursion`: the recursion (counterpart of tao-collatz's Lemma 1.12; the period of the valuation
  folding is `φ(q^{n+1})`).
* `syracZ_eq_rev_fint`: reversal of direction (GGM (4.3), `𝒮_n ≡ F_n(𝒢, 𝒰) mod q^n`).
* `syracZ_offset_split`: splitting of the offset (the modulo-`q^n` form of GGM (3.3), tao-collatz's
  `syracZ_offset_split`).
-/

open scoped ENNReal

namespace GGMCollatz

/-! ### Reading vectors at ℕ indices, and general lemmas on i.i.d. vectors -/

/-- Reading at an ℕ index (the default value `d` beyond the length). -/
def vget {α : Type*} {n : ℕ} (v : Fin n → α) (d : α) (i : ℕ) : α :=
  if h : i < n then v ⟨i, h⟩ else d

theorem vget_of_lt {α : Type*} {n : ℕ} (v : Fin n → α) (d : α) {i : ℕ} (h : i < n) :
    vget v d i = v ⟨i, h⟩ := by
  unfold vget; rw [dif_pos h]

theorem vget_castLE {α : Type*} {k n : ℕ} (h : k ≤ n) (v : Fin n → α) (d : α) {i : ℕ}
    (hi : i < k) : vget (v ∘ Fin.castLE h) d i = vget v d i := by
  unfold vget
  rw [dif_pos hi, dif_pos (lt_of_lt_of_le hi h)]
  rfl

theorem vget_zero {α : Type*} {n : ℕ} (v : Fin (n + 1) → α) (d : α) : vget v d 0 = v 0 := by
  unfold vget; rw [dif_pos (Nat.succ_pos n)]; rfl

theorem vget_succ_tail {α : Type*} {n : ℕ} (v : Fin (n + 1) → α) (d : α) (i : ℕ) :
    vget v d (i + 1) = vget (Fin.tail v) d i := by
  unfold vget
  by_cases hi : i < n
  · rw [dif_pos (by omega), dif_pos hi]; rfl
  · rw [dif_neg (by omega), dif_neg hi]

/-- Restricting to the first `k` components does not change the partial sums with `m ≤ k`. -/
theorem pre_castLE {k n : ℕ} (h : k ≤ n) (a : Fin n → ℕ) {m : ℕ} (hm : m ≤ k) :
    pre (a ∘ Fin.castLE h) m = pre a m := by
  unfold pre
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hik : i < k := lt_of_lt_of_le hi hm
  rw [dif_pos hik, dif_pos (lt_of_lt_of_le hik h)]
  rfl

/-- The marginal law of the first `k` components of an i.i.d. vector is again i.i.d. -/
theorem iid_map_castLE {α : Type*} (μ : PMF α) :
    ∀ (k n : ℕ) (h : k ≤ n),
      (μ.iid n).map (fun a : Fin n → α => a ∘ Fin.castLE h) = μ.iid k := by
  intro k
  induction k with
  | zero =>
      intro n _
      rw [show (fun a : Fin n → α => a ∘ Fin.castLE (Nat.zero_le n))
            = Function.const _ (fun i : Fin 0 => i.elim0) from by
          funext a; funext i; exact i.elim0]
      rw [PMF.map_const]
      rfl
  | succ k ih =>
      intro n h
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h' : k ≤ m := Nat.succ_le_succ_iff.mp h
      have hcons : ∀ (a0 : α) (w : Fin m → α),
          (Fin.cons a0 w : Fin (m + 1) → α) ∘ Fin.castLE h
            = Fin.cons a0 (w ∘ Fin.castLE h') := by
        intro a0 w
        funext i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · simp only [Function.comp_apply]
          rw [show Fin.castLE h (0 : Fin (k + 1)) = (0 : Fin (m + 1)) from by
            apply Fin.ext; simp, Fin.cons_zero, Fin.cons_zero]
        · simp only [Function.comp_apply]
          rw [show Fin.castLE h j.succ = (Fin.castLE h' j).succ from by
            apply Fin.ext; simp, Fin.cons_succ, Fin.cons_succ, Function.comp_apply]
      rw [show μ.iid (m + 1) = μ.bind fun a0 => (μ.iid m).map (Fin.cons a0) from rfl,
        PMF.map_bind, show μ.iid (k + 1) = μ.bind fun a0 => (μ.iid k).map (Fin.cons a0) from rfl]
      congr 1
      funext a0
      rw [PMF.map_comp, show (fun a : Fin (m + 1) → α => a ∘ Fin.castLE h) ∘ Fin.cons a0
          = Fin.cons a0 ∘ (fun w : Fin m → α => w ∘ Fin.castLE h') from by
        funext w; exact hcons a0 w, ← PMF.map_comp, ih m h']

/-- Reversal preserves the i.i.d. law (exchangeability). -/
theorem iid_map_rev {α : Type*} (μ : PMF α) (n : ℕ) :
    (μ.iid n).map (fun a => a ∘ Fin.rev) = μ.iid n := by
  classical
  ext v
  rw [PMF.map_apply, tsum_eq_single (v ∘ Fin.rev)]
  · rw [if_pos, PMF.iid_apply_eq_prod, PMF.iid_apply_eq_prod]
    · exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by
        rw [Function.comp_apply, Fin.revPerm_apply])
    · funext i; show v i = v (Fin.rev (Fin.rev i)); rw [Fin.rev_rev]
  · intro a ha
    rw [if_neg]
    intro heq
    apply ha
    funext i
    have := congrFun heq (Fin.rev i)
    simpa [Function.comp, Fin.rev_rev] using this.symm

/-- Folding a geometric series with periodic weights (tao-collatz's `geom_fold` generalized to base `r`). -/
theorem geom_fold {P : ℕ} (hP : 0 < P) (r : ℝ≥0∞) (g : ℕ → ℝ≥0∞)
    (hper : ∀ a, g (a + P) = g a) :
    ∑' a : ℕ, r ^ a * g a = (1 - r ^ P)⁻¹ * ∑ i ∈ Finset.range P, r ^ i * g i := by
  have : NeZero P := ⟨hP.ne'⟩
  have hperk : ∀ k i, g (k * P + i) = g i := by
    intro k i
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul, add_right_comm, hper, ih]
  rw [← (Nat.divModEquiv P).symm.tsum_eq (fun a => r ^ a * g a)]
  simp only [Nat.divModEquiv_symm_apply]
  rw [ENNReal.tsum_prod']
  have hinner : ∀ k : ℕ,
      (∑' i : Fin P, r ^ (k * P + (i : ℕ)) * g (k * P + (i : ℕ)))
        = (r ^ P) ^ k * ∑ i ∈ Finset.range P, r ^ i * g i := by
    intro k
    rw [tsum_fintype, ← Fin.sum_univ_eq_sum_range (fun i => r ^ i * g i) P, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hperk k i, pow_add, mul_comm k P, pow_mul]
    ring
  rw [tsum_congr hinner, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

/-- Folding periodic weights against `G(μ)`: `Σ_{a₀} G(a₀) f(a₀) = (1-p^{-P})⁻¹ Σ_{a=1}^{P} (p-1)p^{-a} f(a)`. -/
theorem geom_fold_geomP {p P : ℕ} (hp : 2 ≤ p) (hP : 0 < P) (f : ℕ → ℝ≥0∞)
    (hper : ∀ a, f (a + P) = f a) :
    ∑' a0 : ℕ, geomP p a0 * f a0
      = (1 - ((p : ℝ≥0∞)⁻¹) ^ P)⁻¹ *
          ∑ a ∈ Finset.Icc 1 P, ((p - 1 : ℕ) : ℝ≥0∞) * ((p : ℝ≥0∞)⁻¹) ^ a * f a := by
  set r : ℝ≥0∞ := (p : ℝ≥0∞)⁻¹ with hr
  set c : ℝ≥0∞ := ((p - 1 : ℕ) : ℝ≥0∞) with hc
  have hstep1 : (∑' a0 : ℕ, geomP p a0 * f a0) = ∑' b : ℕ, c * r ^ (b + 1) * f (b + 1) := by
    rw [← tsum_ite_zero_eq_succ (fun a => c * r ^ a * f a)]
    apply tsum_congr; intro a0
    rw [geomP_apply hp]
    by_cases h0 : a0 = 0
    · rw [if_pos h0, if_pos h0, zero_mul]
    · rw [if_neg h0, if_neg h0]
  have hstep2 : (∑' b : ℕ, c * r ^ (b + 1) * f (b + 1))
      = c * r * ∑' b : ℕ, r ^ b * f (b + 1) := by
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr; intro b
    rw [pow_succ]; ring
  rw [hstep1, hstep2,
    geom_fold hP r (fun b => f (b + 1)) (fun a => by rw [Nat.add_right_comm]; exact hper (a + 1))]
  rw [show c * r * ((1 - r ^ P)⁻¹ * ∑ i ∈ Finset.range P, r ^ i * f (i + 1))
      = (1 - r ^ P)⁻¹ * (c * r * ∑ i ∈ Finset.range P, r ^ i * f (i + 1)) by ring]
  congr 1
  have hmap : Finset.Icc 1 P
      = (Finset.range P).map ⟨fun i => i + 1, add_left_injective 1⟩ := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨a - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega
  rw [Finset.mul_sum, hmap, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.Embedding.coeFn_mk]
  rw [pow_succ]; ring

namespace Family

variable (F : Family)

/-! ### `p` is invertible modulo `q^e` -/

theorem isUnit_p_zmod (e : ℕ) : IsUnit (F.p : ZMod (F.q ^ e)) :=
  (ZMod.isUnit_iff_coprime F.p (F.q ^ e)).mpr (Nat.Coprime.pow_right e F.coprime)

theorem p_mul_inv_zmod (e : ℕ) : (F.p : ZMod (F.q ^ e)) * (F.p : ZMod (F.q ^ e))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (F.isUnit_p_zmod e)

theorem inv_mul_p_zmod (e : ℕ) : (F.p : ZMod (F.q ^ e))⁻¹ * (F.p : ZMod (F.q ^ e)) = 1 :=
  ZMod.inv_mul_of_unit _ (F.isUnit_p_zmod e)

theorem neZero_q_pow (e : ℕ) : NeZero (F.q ^ e) := ⟨pow_ne_zero _ F.q_pos.ne'⟩

/-- The projection sends `p⁻¹` to `p⁻¹`. -/
theorem castHom_p_inv {k n : ℕ} (h : k ≤ n) :
    ZMod.castHom (pow_dvd_pow F.q h) (ZMod (F.q ^ k)) ((F.p : ZMod (F.q ^ n))⁻¹)
      = (F.p : ZMod (F.q ^ k))⁻¹ := by
  set φ := ZMod.castHom (pow_dvd_pow F.q h) (ZMod (F.q ^ k)) with hφ
  have h1 : (F.p : ZMod (F.q ^ k)) * φ ((F.p : ZMod (F.q ^ n))⁻¹) = 1 := by
    rw [← map_natCast φ F.p, ← map_mul, F.p_mul_inv_zmod n, map_one]
  calc φ ((F.p : ZMod (F.q ^ n))⁻¹)
      = ((F.p : ZMod (F.q ^ k))⁻¹ * F.p) * φ ((F.p : ZMod (F.q ^ n))⁻¹) := by
        rw [F.inv_mul_p_zmod k, one_mul]
    _ = (F.p : ZMod (F.q ^ k))⁻¹ * ((F.p : ZMod (F.q ^ k)) * φ ((F.p : ZMod (F.q ^ n))⁻¹)) := by
        ring
    _ = (F.p : ZMod (F.q ^ k))⁻¹ := by rw [h1, mul_one]

/-! ### The Syracuse random variable -/

/-- The reversed form of the correction term `Σ_{j<n} q^j p^{-a_{[1,j+1]}} r(d_j)`, computed in `ZMod M`
(`v i = (a_i, d_i)`: the pair of valuation and digit). -/
noncomputable def offsetIn (M : ℕ) {n : ℕ} (v : Fin n → ℕ × ℕ) : ZMod M :=
  ∑ j ∈ Finset.range n, (F.q : ZMod M) ^ j * ((F.p : ZMod M)⁻¹) ^ pre (fun i => (v i).1) (j + 1)
    * (F.r (vget (fun i => (v i).2) 0 j) : ZMod M)

/-- **The Syracuse random variable `𝒮_n = 𝒮 mod q^n`** (GGM (4.1), (4.2)): the pushforward under
`offsetIn (q^n)` of the i.i.d. vector with one-step law `G(μ) ⊗ U(1..p-1)`. -/
noncomputable def syracZ (n : ℕ) : PMF (ZMod (F.q ^ n)) :=
  ((stepLaw F.p).iid n).map (F.offsetIn (F.q ^ n))

/-- The projection commutes with `offsetIn`. -/
theorem castHom_offsetIn {k n : ℕ} (h : k ≤ n) {l : ℕ} (v : Fin l → ℕ × ℕ) :
    ZMod.castHom (pow_dvd_pow F.q h) (ZMod (F.q ^ k)) (F.offsetIn (F.q ^ n) v)
      = F.offsetIn (F.q ^ k) v := by
  unfold offsetIn
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, F.castHom_p_inv h, map_intCast]

/-- Modulo `q^k`, only the first `k` components of a vector of length `n ≥ k` matter. -/
theorem offsetIn_truncate {k n : ℕ} (h : k ≤ n) (v : Fin n → ℕ × ℕ) :
    F.offsetIn (F.q ^ k) v = F.offsetIn (F.q ^ k) (v ∘ Fin.castLE h) := by
  unfold offsetIn
  have hqzero : ∀ j, k ≤ j → (F.q : ZMod (F.q ^ k)) ^ j = 0 := by
    intro j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [pow_add, show (F.q : ZMod (F.q ^ k)) ^ k = ((F.q ^ k : ℕ) : ZMod (F.q ^ k)) by push_cast; rfl,
      ZMod.natCast_self, zero_mul]
  rw [← Finset.sum_range_add_sum_Ico _ h]
  rw [Finset.sum_eq_zero (s := Finset.Ico k n) (fun j hj => by
    rw [Finset.mem_Ico] at hj
    rw [hqzero j hj.1, zero_mul, zero_mul]), add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hpre : pre (fun i => ((v ∘ Fin.castLE h) i).1) (j + 1) = pre (fun i => (v i).1) (j + 1) :=
    pre_castLE h (fun i => (v i).1) (by omega)
  have hvget : vget (fun i => ((v ∘ Fin.castLE h) i).2) 0 j = vget (fun i => (v i).2) 0 j :=
    vget_castLE h (fun i => (v i).2) 0 hj
  rw [hpre, hvget]

/-- **Compatibility with projections** (GGM (4.4), tao-collatz's (1.22)): `𝒮_n mod q^k = 𝒮_k` (`k ≤ n`). -/
theorem syracZ_map_cast {k n : ℕ} (hkn : k ≤ n) :
    (F.syracZ n).map (ZMod.castHom (pow_dvd_pow F.q hkn) (ZMod (F.q ^ k))) = F.syracZ k := by
  unfold syracZ
  rw [PMF.map_comp,
    show ((ZMod.castHom (pow_dvd_pow F.q hkn) (ZMod (F.q ^ k))) ∘ F.offsetIn (F.q ^ n))
        = F.offsetIn (F.q ^ k) ∘ (fun v : Fin n → ℕ × ℕ => v ∘ Fin.castLE hkn) from by
      funext v
      simp only [Function.comp_apply]
      rw [F.castHom_offsetIn hkn, F.offsetIn_truncate hkn],
    ← PMF.map_comp, iid_map_castLE]

/-! ### The recursion (counterpart of tao-collatz's Lemma 1.12) -/

/-- **Peeling off the head**: `offset(v) = p^{-a₀} (r(d₀) + q · offset(tail v))` (any modulus). -/
theorem offsetIn_peel (M : ℕ) {n : ℕ} (v : Fin (n + 1) → ℕ × ℕ) :
    F.offsetIn M v = ((F.p : ZMod M)⁻¹) ^ (v 0).1
      * ((F.r (v 0).2 : ZMod M) + (F.q : ZMod M) * F.offsetIn M (Fin.tail v)) := by
  unfold offsetIn
  rw [Finset.sum_range_succ']
  have hhead : (F.q : ZMod M) ^ 0 * ((F.p : ZMod M)⁻¹) ^ pre (fun i => (v i).1) (0 + 1)
      * (F.r (vget (fun i => (v i).2) 0 0) : ZMod M)
      = ((F.p : ZMod M)⁻¹) ^ (v 0).1 * (F.r (v 0).2 : ZMod M) := by
    rw [pow_zero, one_mul, pre_cons_head, pre_zero, add_zero, vget_zero]
  have hterm : ∀ k ∈ Finset.range n,
      (F.q : ZMod M) ^ (k + 1) * ((F.p : ZMod M)⁻¹) ^ pre (fun i => (v i).1) (k + 1 + 1)
        * (F.r (vget (fun i => (v i).2) 0 (k + 1)) : ZMod M)
      = ((F.p : ZMod M)⁻¹) ^ (v 0).1 * ((F.q : ZMod M) * ((F.q : ZMod M) ^ k
          * ((F.p : ZMod M)⁻¹) ^ pre (fun i => (Fin.tail v i).1) (k + 1)
          * (F.r (vget (fun i => (Fin.tail v i).2) 0 k) : ZMod M))) := by
    intro k _
    rw [pre_cons_head (fun i => (v i).1) (k + 1), vget_succ_tail, pow_add, pow_succ,
      show (Fin.tail fun i => (v i).1) = (fun i => (Fin.tail v i).1) from rfl,
      show (Fin.tail fun i => (v i).2) = (fun i => (Fin.tail v i).2) from rfl]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum, hhead]
  ring

/-- The kernel of multiplication by `q` modulo `q^{n+1}` is the kernel of the projection to modulus `q^n`
(tao-collatz's `three_mul_eq_iff`). -/
theorem q_mul_eq_iff (n : ℕ) (A B : ZMod (F.q ^ (n + 1))) :
    (F.q : ZMod (F.q ^ (n + 1))) * A = (F.q : ZMod (F.q ^ (n + 1))) * B ↔
      ZMod.castHom (pow_dvd_pow F.q (Nat.le_succ n)) (ZMod (F.q ^ n)) A
        = ZMod.castHom (pow_dvd_pow F.q (Nat.le_succ n)) (ZMod (F.q ^ n)) B := by
  have := F.neZero_q_pow (n + 1)
  set φ := ZMod.castHom (pow_dvd_pow F.q (Nat.le_succ n)) (ZMod (F.q ^ n)) with hφ
  have key : ∀ C : ZMod (F.q ^ (n + 1)), (F.q : ZMod (F.q ^ (n + 1))) * C = 0 ↔ φ C = 0 := by
    intro C
    have hφC : φ C = ((C.val : ℕ) : ZMod (F.q ^ n)) := by
      rw [hφ, ZMod.castHom_apply, ← ZMod.natCast_val]
    have hqC : (F.q : ZMod (F.q ^ (n + 1))) * C = ((F.q * C.val : ℕ) : ZMod (F.q ^ (n + 1))) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val C]
    rw [hqC, ZMod.natCast_eq_zero_iff, hφC, ZMod.natCast_eq_zero_iff]
    generalize C.val = w
    rw [pow_succ']
    exact Nat.mul_dvd_mul_iff_left F.q_pos
  constructor
  · intro h
    have h0 : (F.q : ZMod (F.q ^ (n + 1))) * (A - B) = 0 := by rw [mul_sub, h, sub_self]
    have h1 := (key (A - B)).mp h0
    rwa [map_sub, sub_eq_zero] at h1
  · intro h
    have h0 : φ (A - B) = 0 := by rw [map_sub, h, sub_self]
    have h1 := (key (A - B)).mpr h0
    rwa [mul_sub, sub_eq_zero] at h1

/-- Pointwise condition: `x = p^{-a₀}(r(d₀) + q Ĝ)` is equivalent, for `m = p^{a₀} x - r(d₀)`, to
`q ∣ m` and `m/q ≡ offset_n(w) (mod q^n)`. -/
theorem fiber_iff (n a0 d0 : ℕ) (x : ZMod (F.q ^ (n + 1))) (w : Fin n → ℕ × ℕ) :
    (x = F.offsetIn (F.q ^ (n + 1)) (Fin.cons (a0, d0) w)) ↔
      ((F.q : ℤ) ∣ (F.p : ℤ) ^ a0 * x.val - F.r d0 ∧
        ((((F.p : ℤ) ^ a0 * x.val - F.r d0) / F.q : ℤ) : ZMod (F.q ^ n))
          = F.offsetIn (F.q ^ n) w) := by
  have := F.neZero_q_pow (n + 1)
  set m : ℤ := (F.p : ℤ) ^ a0 * x.val - F.r d0 with hm
  set Ghat := F.offsetIn (F.q ^ (n + 1)) w with hGhat
  rw [F.offsetIn_peel (F.q ^ (n + 1)) (Fin.cons (a0, d0) w)]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [← hGhat]
  have hpow1 : (F.p : ZMod (F.q ^ (n + 1))) ^ a0 * ((F.p : ZMod (F.q ^ (n + 1)))⁻¹) ^ a0 = 1 := by
    rw [← mul_pow, F.p_mul_inv_zmod, one_pow]
  have hpow2 : ((F.p : ZMod (F.q ^ (n + 1)))⁻¹) ^ a0 * (F.p : ZMod (F.q ^ (n + 1))) ^ a0 = 1 := by
    rw [mul_comm]; exact hpow1
  have hmcast : ((m : ℤ) : ZMod (F.q ^ (n + 1))) = (F.p : ZMod (F.q ^ (n + 1))) ^ a0 * x - (F.r d0 : ZMod (F.q ^ (n + 1))) := by
    rw [hm]; push_cast; rw [ZMod.natCast_zmod_val x]
  -- clear the unit
  have hstep1 : (x = ((F.p : ZMod (F.q ^ (n + 1)))⁻¹) ^ a0 * ((F.r d0 : ZMod (F.q ^ (n + 1))) + (F.q : ZMod (F.q ^ (n + 1))) * Ghat))
      ↔ ((m : ℤ) : ZMod (F.q ^ (n + 1))) = (F.q : ZMod (F.q ^ (n + 1))) * Ghat := by
    rw [hmcast]
    constructor
    · intro h
      rw [h, ← mul_assoc, hpow1, one_mul]; ring
    · intro h
      have h' : (F.p : ZMod (F.q ^ (n + 1))) ^ a0 * x = (F.r d0 : ZMod (F.q ^ (n + 1))) + (F.q : ZMod (F.q ^ (n + 1))) * Ghat := by
        rw [← h]; ring
      rw [← h', ← mul_assoc, hpow2, one_mul]
  rw [hstep1]
  set ψ := ZMod.castHom (pow_dvd_pow F.q (Nat.le_succ n)) (ZMod (F.q ^ n)) with hψ
  have hcastG : ψ Ghat = F.offsetIn (F.q ^ n) w := F.castHom_offsetIn (Nat.le_succ n) w
  constructor
  · intro heq
    have hdvd : (F.q : ℤ) ∣ m := by
      have hχ := congrArg (ZMod.castHom (dvd_pow_self F.q (Nat.succ_ne_zero n)) (ZMod F.q)) heq
      rw [map_intCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul] at hχ
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd m F.q).mp hχ
    refine ⟨hdvd, ?_⟩
    obtain ⟨t, ht⟩ := hdvd
    have hdiv : m / F.q = t := by rw [ht]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast F.q_pos.ne')
    rw [hdiv]
    have heq' : (F.q : ZMod (F.q ^ (n + 1))) * (t : ZMod (F.q ^ (n + 1))) = (F.q : ZMod (F.q ^ (n + 1))) * Ghat := by
      rw [← heq, ht]; push_cast; ring
    have h3 := (F.q_mul_eq_iff n _ _).mp heq'
    rw [map_intCast, hcastG] at h3
    exact h3
  · rintro ⟨hdvd, hval⟩
    obtain ⟨t, ht⟩ := hdvd
    have hdiv : m / F.q = t := by rw [ht]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast F.q_pos.ne')
    rw [hdiv] at hval
    rw [ht]
    push_cast
    apply (F.q_mul_eq_iff n _ _).mpr
    rw [map_intCast, hcastG]
    exact hval

/-- **The fibre lemma** (the core of Lemma 1.12): the remaining mass when the head `(a₀, d₀)` is fixed. -/
theorem syracZ_fiber (n a0 d0 : ℕ) (x : ZMod (F.q ^ (n + 1))) :
    (∑' w : Fin n → ℕ × ℕ, ((stepLaw F.p).iid n) w *
        (if x = F.offsetIn (F.q ^ (n + 1)) (Fin.cons (a0, d0) w) then 1 else 0))
      = if (F.q : ℤ) ∣ (F.p : ℤ) ^ a0 * x.val - F.r d0
        then F.syracZ n ((((F.p : ℤ) ^ a0 * x.val - F.r d0) / F.q : ℤ) : ZMod (F.q ^ n))
        else 0 := by
  classical
  by_cases hg : (F.q : ℤ) ∣ (F.p : ℤ) ^ a0 * x.val - F.r d0
  · rw [if_pos hg, syracZ, PMF.map_apply]
    apply tsum_congr
    intro w
    have hiff := F.fiber_iff n a0 d0 x w
    by_cases hc : ((((F.p : ℤ) ^ a0 * x.val - F.r d0) / F.q : ℤ) : ZMod (F.q ^ n))
        = F.offsetIn (F.q ^ n) w
    · rw [if_pos (hiff.mpr ⟨hg, hc⟩), if_pos hc, mul_one]
    · rw [if_neg (fun h => hc (hiff.mp h).2), if_neg hc, mul_zero]
  · rw [if_neg hg]
    apply ENNReal.tsum_eq_zero.mpr
    intro w
    rw [if_neg (fun h => hg ((F.fiber_iff n a0 d0 x w).mp h).1), mul_zero]

/-- Period: `p^{φ(q^{n+1})} ≡ 1 (mod q^{n+1})` (in ℤ). -/
theorem q_pow_dvd_p_pow_totient_sub_one (n : ℕ) :
    ((F.q : ℤ) ^ (n + 1)) ∣ (F.p : ℤ) ^ (F.q ^ (n + 1)).totient - 1 := by
  have h := Nat.ModEq.pow_totient (Nat.Coprime.pow_right (n + 1) F.coprime)
  have h' := (Nat.modEq_iff_dvd.mp h.symm)
  push_cast at h'
  exact h'

-- RATIFY-DRIFT (the same caveat as in tao-collatz): the "divide by `q`" step of Lemma 1.12 is written not with
-- `q⁻¹` modulo `q^{n+1}` (`q` is a zero divisor) but with the division in ℤ, `(p^a x - r(d))/q` (exact under
-- the condition `q ∣ …`).
/-- **The recursion** (counterpart of tao-collatz's Lemma 1.12): the mass of `𝒮_{n+1}` at `x` is the sum, over
digits `d ∈ {1,…,p-1}` and `1 ≤ a ≤ P = φ(q^{n+1})`, of the `p^{-a}`-weighted masses of `𝒮_n`, normalized by
`(1 - p^{-P})⁻¹`. -/
theorem syracZ_recursion (n : ℕ) (x : ZMod (F.q ^ (n + 1))) :
    F.syracZ (n + 1) x
      = (1 - ((F.p : ℝ≥0∞)⁻¹) ^ (F.q ^ (n + 1)).totient)⁻¹ *
          ∑ d ∈ Finset.Ioo 0 F.p, ∑ a ∈ Finset.Icc 1 (F.q ^ (n + 1)).totient,
            (if (F.q : ℤ) ∣ (F.p : ℤ) ^ a * x.val - F.r d
              then ((F.p : ℝ≥0∞)⁻¹) ^ a
                * F.syracZ n ((((F.p : ℤ) ^ a * x.val - F.r d) / F.q : ℤ) : ZMod (F.q ^ n))
              else 0) := by
  classical
  have hp := F.two_le_p
  set P : ℕ := (F.q ^ (n + 1)).totient with hPdef
  have hPpos : 0 < P := Nat.totient_pos.mpr (pow_pos F.q_pos _)
  set f : ℕ → ℕ → ℝ≥0∞ := fun a d =>
    if (F.q : ℤ) ∣ (F.p : ℤ) ^ a * x.val - F.r d
      then F.syracZ n ((((F.p : ℤ) ^ a * x.val - F.r d) / F.q : ℤ) : ZMod (F.q ^ n)) else 0
    with hf
  -- 1. peel off the head pair
  have hmain : F.syracZ (n + 1) x
      = ∑' a0 : ℕ, ∑' d0 : ℕ, geomP F.p a0 * unifDigit F.p d0 * f a0 d0 := by
    have h1 : F.syracZ (n + 1) x
        = ∑' v : Fin (n + 1) → ℕ × ℕ, ((stepLaw F.p).iid (n + 1)) v *
            (if x = F.offsetIn (F.q ^ (n + 1)) v then 1 else 0) := by
      rw [syracZ, PMF.map_apply]
      apply tsum_congr
      intro v
      by_cases hc : x = F.offsetIn (F.q ^ (n + 1)) v
      · rw [if_pos hc, if_pos hc, mul_one]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [h1, PMF.tsum_iid_succ_mul (stepLaw F.p) n
      (fun v => if x = F.offsetIn (F.q ^ (n + 1)) v then 1 else 0), ENNReal.tsum_prod']
    apply tsum_congr; intro a0
    apply tsum_congr; intro d0
    rw [stepLaw_apply, F.syracZ_fiber n a0 d0 x]
  -- 2. periodicity
  have hper : ∀ d a, f (a + P) d = f a d := by
    intro d a
    simp only [hf]
    have hqM : ((F.q : ℤ) ^ (n + 1)) ∣
        ((F.p : ℤ) ^ (a + P) * x.val - F.r d) - ((F.p : ℤ) ^ a * x.val - F.r d) := by
      have hP := F.q_pow_dvd_p_pow_totient_sub_one n
      rw [← hPdef] at hP
      have : ((F.p : ℤ) ^ (a + P) * x.val - F.r d) - ((F.p : ℤ) ^ a * x.val - F.r d)
          = ((F.p : ℤ) ^ P - 1) * ((F.p : ℤ) ^ a * x.val) := by ring
      rw [this]
      exact Dvd.dvd.mul_right hP _
    have hqdvd : (F.q : ℤ) ∣
        ((F.p : ℤ) ^ (a + P) * x.val - F.r d) - ((F.p : ℤ) ^ a * x.val - F.r d) :=
      dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero n)) hqM
    have hiff : (F.q : ℤ) ∣ (F.p : ℤ) ^ (a + P) * x.val - F.r d ↔
        (F.q : ℤ) ∣ (F.p : ℤ) ^ a * x.val - F.r d := by
      constructor
      · intro h; have := dvd_sub h hqdvd; simpa using this
      · intro h; have := dvd_add h hqdvd; simpa using this
    by_cases hga : (F.q : ℤ) ∣ (F.p : ℤ) ^ a * x.val - F.r d
    · rw [if_pos (hiff.mpr hga), if_pos hga]
      congr 1
      obtain ⟨t, ht⟩ := hga
      obtain ⟨t', ht'⟩ := hiff.mpr ⟨t, ht⟩
      have hq0 : (F.q : ℤ) ≠ 0 := by exact_mod_cast F.q_pos.ne'
      rw [ht, ht', Int.mul_ediv_cancel_left _ hq0, Int.mul_ediv_cancel_left _ hq0]
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      rw [ht, ht'] at hqM
      obtain ⟨s, hs⟩ := hqM
      refine ⟨-s, ?_⟩
      have : (F.q : ℤ) * (t - t') = (F.q : ℤ) * ((F.q : ℤ) ^ n * -s) := by
        linear_combination -hs
      push_cast
      exact mul_left_cancel₀ hq0 this
    · rw [if_neg (fun h => hga (hiff.mp h)), if_neg hga]
  -- 3. sum over digits and folding of valuations
  rw [hmain, ENNReal.tsum_comm]
  rw [tsum_eq_sum (s := Finset.Ioo 0 F.p) (fun d hd => by
    apply ENNReal.tsum_eq_zero.mpr
    intro a0
    rw [unifDigit_apply hp, if_neg (by simpa using hd), mul_zero, zero_mul])]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : 0 < d ∧ d < F.p := by simpa using hd
  have hfold := geom_fold_geomP hp hPpos (fun a => f a d) (fun a => hper d a)
  rw [show (∑' a0 : ℕ, geomP F.p a0 * unifDigit F.p d * f a0 d)
      = unifDigit F.p d * ∑' a0 : ℕ, geomP F.p a0 * f a0 d by
    rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun a0 => by ring,
    hfold, unifDigit_apply hp, if_pos hd']
  have hc : ((F.p - 1 : ℕ) : ℝ≥0∞)⁻¹ * ((F.p - 1 : ℕ) : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel (natCast_sub_one_ne_zero hp) (ENNReal.natCast_ne_top _)
  rw [show ((F.p - 1 : ℕ) : ℝ≥0∞)⁻¹ * ((1 - ((F.p : ℝ≥0∞)⁻¹) ^ P)⁻¹ *
        ∑ a ∈ Finset.Icc 1 P, ((F.p - 1 : ℕ) : ℝ≥0∞) * ((F.p : ℝ≥0∞)⁻¹) ^ a * f a d)
      = (1 - ((F.p : ℝ≥0∞)⁻¹) ^ P)⁻¹ *
        ∑ a ∈ Finset.Icc 1 P, (((F.p - 1 : ℕ) : ℝ≥0∞)⁻¹ * ((F.p - 1 : ℕ) : ℝ≥0∞))
          * (((F.p : ℝ≥0∞)⁻¹) ^ a * f a d) by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring]
  rw [hc]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp only [hf, one_mul]
  rw [mul_ite, mul_zero]

/-! ### Reversal of direction and splitting of the offset -/

/-- Writing `fint` as a sum over ℕ indices (reading via `vget`). -/
theorem fint_eq_sum_range {k n : ℕ} (a : Fin k → ℕ) (R : Fin n → ℤ) :
    F.fint a R = ∑ m ∈ Finset.range n,
      (F.q : ℤ) ^ (n - 1 - m) * (F.p : ℤ) ^ pre a m * vget R 0 m := by
  unfold fint
  rw [← Fin.sum_univ_eq_sum_range
    (fun m => (F.q : ℤ) ^ (n - 1 - m) * (F.p : ℤ) ^ pre a m * vget R 0 m) n]
  apply Finset.sum_congr rfl
  intro m _
  rw [vget_of_lt R 0 m.isLt]

/-- **Reversal of direction** (GGM (4.3), the bridge of tao-collatz's (1.21)): `𝒮_n` can also be written as the
pushforward under `v ↦ fint(a, r ∘ d) · p^{-|a|}` (`v i = (a_i, d_i)`). -/
theorem syracZ_eq_rev_fint (n : ℕ) :
    F.syracZ n = ((stepLaw F.p).iid n).map (fun v =>
      ((F.fint (fun i => (v i).1) (fun i => F.r (v i).2) : ℤ) : ZMod (F.q ^ n))
        * ((F.p : ZMod (F.q ^ n))⁻¹) ^ pre (fun i => (v i).1) n) := by
  have hunit := F.p_mul_inv_zmod n
  have hkey : ∀ b : Fin n → ℕ × ℕ,
      ((F.fint (fun i => (b i).1) (fun i => F.r (b i).2) : ℤ) : ZMod (F.q ^ n))
          * ((F.p : ZMod (F.q ^ n))⁻¹) ^ pre (fun i => (b i).1) n
        = F.offsetIn (F.q ^ n) (b ∘ Fin.rev) := by
    intro b
    set a : Fin n → ℕ := fun i => (b i).1 with ha
    rw [F.fint_eq_sum_range, Int.cast_sum, Finset.sum_mul, ← Finset.sum_range_reflect]
    unfold offsetIn
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hj' : n - 1 - (n - 1 - j) = j := by omega
    rw [hj']
    have hsplit : pre (a ∘ Fin.rev) (j + 1) + pre a (n - 1 - j) = pre a n := by
      have := pre_comp_rev a (m := j + 1) (by omega)
      rwa [show n - (j + 1) = n - 1 - j from by omega] at this
    have hvget : vget (fun i => F.r (b i).2) 0 (n - 1 - j)
        = F.r (vget (fun i => ((b ∘ Fin.rev) i).2) 0 j) := by
      rw [vget_of_lt _ _ (by omega), vget_of_lt _ _ hj]
      simp only [Function.comp_apply]
      congr 3
      apply Fin.ext
      rw [Fin.val_rev]
      simp only
      omega
    rw [hvget]
    have hpre_eq : pre (fun i => ((b ∘ Fin.rev) i).1) (j + 1) = pre (a ∘ Fin.rev) (j + 1) := rfl
    rw [hpre_eq]
    set P := pre a (n - 1 - j)
    set Q := pre (a ∘ Fin.rev) (j + 1)
    push_cast
    rw [← hsplit, pow_add]
    have h2 : (F.p : ZMod (F.q ^ n)) ^ P * ((F.p : ZMod (F.q ^ n))⁻¹) ^ P = 1 := by
      rw [← mul_pow, hunit, one_pow]
    linear_combination ((F.q : ZMod (F.q ^ n)) ^ j * ((F.p : ZMod (F.q ^ n))⁻¹) ^ Q
      * (F.r (vget (fun i => ((b ∘ Fin.rev) i).2) 0 j) : ZMod (F.q ^ n))) * h2
  have hGF : (fun v : Fin n → ℕ × ℕ =>
        ((F.fint (fun i => (v i).1) (fun i => F.r (v i).2) : ℤ) : ZMod (F.q ^ n))
          * ((F.p : ZMod (F.q ^ n))⁻¹) ^ pre (fun i => (v i).1) n)
      = F.offsetIn (F.q ^ n) ∘ (fun v : Fin n → ℕ × ℕ => v ∘ Fin.rev) := funext hkey
  unfold syracZ
  rw [hGF, ← PMF.map_comp, iid_map_rev]

/-- **Splitting of the offset** (the modulo-`q^{j+l}` form of GGM (3.3), tao-collatz's `syracZ_offset_split`):
`fint(a,R) p^{-|a|} = q^l (offset of the first part) p^{-|second part|} + (offset of the second part)`. The offset
of the second part is itself a Syracuse offset of length `l`. -/
theorem syracZ_offset_split {j l : ℕ} (a : Fin (j + l) → ℕ) (R : Fin (j + l) → ℤ) :
    ((F.fint a R : ℤ) : ZMod (F.q ^ (j + l))) * ((F.p : ZMod (F.q ^ (j + l)))⁻¹) ^ pre a (j + l)
      = (F.q : ZMod (F.q ^ (j + l))) ^ l
          * (((F.fint (fun i => a (Fin.castAdd l i)) (fun i => R (Fin.castAdd l i)) : ℤ)
                : ZMod (F.q ^ (j + l))) * ((F.p : ZMod (F.q ^ (j + l)))⁻¹) ^ pre a j)
          * ((F.p : ZMod (F.q ^ (j + l)))⁻¹) ^ pre (fun i => a (Fin.natAdd j i)) l
        + ((F.fint (fun i => a (Fin.natAdd j i)) (fun i => R (Fin.natAdd j i)) : ℤ)
              : ZMod (F.q ^ (j + l)))
          * ((F.p : ZMod (F.q ^ (j + l)))⁻¹) ^ pre (fun i => a (Fin.natAdd j i)) l := by
  have hunit := F.p_mul_inv_zmod (j + l)
  have hpre : pre a (j + l) = pre a j + pre (fun i => a (Fin.natAdd j i)) l :=
    pre_natAdd_split a (le_refl l)
  have hfint : ((F.fint a R : ℤ) : ZMod (F.q ^ (j + l)))
      = (F.q : ZMod (F.q ^ (j + l))) ^ l
          * ((F.fint (fun i => a (Fin.castAdd l i)) (fun i => R (Fin.castAdd l i)) : ℤ)
              : ZMod (F.q ^ (j + l)))
        + (F.p : ZMod (F.q ^ (j + l))) ^ pre a j
          * ((F.fint (fun i => a (Fin.natAdd j i)) (fun i => R (Fin.natAdd j i)) : ℤ)
              : ZMod (F.q ^ (j + l))) := by
    rw [F.fint_split]; push_cast; ring
  have h2 : (F.p : ZMod (F.q ^ (j + l))) ^ pre a j
      * ((F.p : ZMod (F.q ^ (j + l)))⁻¹) ^ pre a j = 1 := by
    rw [← mul_pow, hunit, one_pow]
  rw [hfint, hpre]
  linear_combination
    (((F.fint (fun i => a (Fin.natAdd j i)) (fun i => R (Fin.natAdd j i)) : ℤ)
        : ZMod (F.q ^ (j + l)))
      * ((F.p : ZMod (F.q ^ (j + l)))⁻¹) ^ pre (fun i => a (Fin.natAdd j i)) l) * h2

end Family

end GGMCollatz
