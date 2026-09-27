import GGMCollatz.Tao.Prob.Geometric

/-!
# Gaussian-type weights and i.i.d. sums (counterpart of the foundation of node S3 of tao-collatz)

Derived from `TaoCollatz/Prob/LocalBound.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r): `geomHalf`, `pascal` are replaced by `geomP p`, `pascalP p`.
The rest of the content (`Gweight`, `iidSum` and their algebra) does not depend on `p` and is unchanged
(only the namespace is `GGMCollatz`).

* `Gweight t x = exp(-x²/t) + exp(-|x|)`: the Gaussian-type weight of Tao (2.2) (the same form in GGM §2.1).
* `iidSum μ n`: the law of the i.i.d. sum `v₁ + ⋯ + vₙ` (`M` is an arbitrary additive commutative monoid).
* `pascalP_eq_iidSum`, `iidSum_pascalP_apply`: a sum of copies of `P(μ) = G(μ) + G(μ)` is a sum of `2n` copies
  of `G(μ)`.

The local bound and the tail bound (the `G(μ)` version of Tao's Lemma 2.2) are in `Prob/LocalInstances.lean`.
-/

open scoped ENNReal

namespace GGMCollatz

/-- The Gaussian-type weight `G_t(x) = exp(-x²/t) + exp(-|x|)` (Tao (2.2)). -/
noncomputable def Gweight (t x : ℝ) : ℝ := Real.exp (-(x ^ 2) / t) + Real.exp (-|x|)

theorem Gweight_pos (t x : ℝ) : 0 < Gweight t x :=
  add_pos (Real.exp_pos _) (Real.exp_pos _)

theorem Gweight_nonneg (t x : ℝ) : 0 ≤ Gweight t x := (Gweight_pos t x).le

theorem Gweight_le_two (t x : ℝ) (ht : 0 ≤ t) : Gweight t x ≤ 2 := by
  have h1 : Real.exp (-(x ^ 2) / t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, div_zero]
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) ht |>.trans_eq rfl
  have h2 : Real.exp (-|x|) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))
  calc Gweight t x ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

variable {M : Type*} [AddCommMonoid M]

/-- The law of the i.i.d. sum `v₁ + ⋯ + vₙ` (Tao's `v_{[1,n]}`, (1.6)). -/
noncomputable def iidSum (p : PMF M) (n : ℕ) : PMF M :=
  (p.iid n).map fun v => ∑ i, v i

theorem iidSum_zero (p : PMF M) : iidSum p 0 = PMF.pure 0 := by
  rw [iidSum, show p.iid 0 = PMF.pure (fun i : Fin 0 => i.elim0) from rfl,
    PMF.pure_map]
  simp

/-- Peeling off the first term: in law, `S_{n+1} = a + S_n`. -/
theorem iidSum_succ (p : PMF M) (n : ℕ) :
    iidSum p (n + 1) = p.bind fun a => (iidSum p n).map (a + ·) := by
  rw [iidSum, show p.iid (n + 1) = p.bind fun a => (p.iid n).map (Fin.cons a) from rfl,
    PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [PMF.map_comp, iidSum, PMF.map_comp]
  have hf : ((fun v : Fin (n + 1) → M => ∑ i, v i) ∘ Fin.cons a)
      = ((a + ·) ∘ fun w : Fin n → M => ∑ i, w i) := by
    funext w
    simp only [Function.comp_apply]
    rw [Fin.sum_cons]
  rw [hf]

/-- Renewal additivity: `S_{k+n} = S_k + S'_n` (the two blocks are independent). -/
theorem iidSum_add (p : PMF M) (k n : ℕ) :
    iidSum p (k + n) = (iidSum p k).bind fun s => (iidSum p n).map (s + ·) := by
  induction k with
  | zero =>
    rw [Nat.zero_add, iidSum_zero, PMF.pure_bind]
    have h : (fun x : M => (0 : M) + x) = id := funext fun x => zero_add x
    rw [h, PMF.map_id]
  | succ k IH =>
    rw [show k + 1 + n = (k + n) + 1 from by omega, iidSum_succ, iidSum_succ,
      PMF.bind_bind]
    refine congrArg _ (funext fun a => ?_)
    rw [IH, PMF.map_bind, PMF.bind_map]
    refine congrArg _ (funext fun s => ?_)
    simp only [Function.comp_apply]
    rw [PMF.map_comp]
    have hf : ((a + ·) ∘ (s + ·)) = ((a + s) + ·) := by
      funext x
      simp only [Function.comp_apply]
      rw [add_assoc]
    rw [hf]

/-- Sum of sums: the sum of `n` independent copies of `S_k` is `S_{nk}`. -/
theorem iidSum_iidSum (p : PMF M) (k n : ℕ) :
    iidSum (iidSum p k) n = iidSum p (n * k) := by
  induction n with
  | zero => rw [Nat.zero_mul, iidSum_zero, iidSum_zero]
  | succ n IH =>
    rw [iidSum_succ, show (n + 1) * k = k + n * k from by ring, iidSum_add]
    refine congrArg _ (funext fun s => ?_)
    rw [IH]

/-- Additive pushforward commutes with i.i.d. sums (the entry point of the circle method: take `φ` to be reduction mod `N`). -/
theorem iidSum_map (p : PMF M) {M' : Type*} [AddCommMonoid M'] (φ : M → M')
    (hφ0 : φ 0 = 0) (hφ : ∀ a b, φ (a + b) = φ a + φ b) (n : ℕ) :
    (iidSum p n).map φ = iidSum (p.map φ) n := by
  induction n with
  | zero => rw [iidSum_zero, iidSum_zero, PMF.pure_map, hφ0]
  | succ n IH =>
    rw [iidSum_succ, iidSum_succ, PMF.map_bind, PMF.bind_map]
    refine congrArg _ (funext fun a => ?_)
    simp only [Function.comp_apply]
    rw [PMF.map_comp, ← IH, PMF.map_comp]
    have hf : (φ ∘ (a + ·)) = ((φ a + ·) ∘ φ) := by
      funext x
      simp only [Function.comp_apply]
      rw [hφ]
    rw [hf]

/-- `pascalP p` is the sum of 2 copies of `geomP p` (tao-collatz's `pascal_eq_iidSum`). -/
theorem pascalP_eq_iidSum (p : ℕ) : pascalP p = iidSum (geomP p) 2 := by
  rw [pascal_eq_map_iid, iidSum]
  have hf : (fun v : Fin 2 → ℕ => v 0 + v 1) = fun v : Fin 2 → ℕ => ∑ i, v i := by
    funext v
    rw [Fin.sum_univ_two]
  rw [hf]

/-- The pointwise mass of the sum of `n` copies of `pascalP p`: the law of `|G(μ)^{(2n)}|`
(`C(L-1, 2n-1)(p-1)^{2n} p^{-L}`, `negBinomial_apply`). -/
theorem iidSum_pascalP_apply {p : ℕ} (hp : 2 ≤ p) (n L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (iidSum (pascalP p) n) L
      = (L - 1).choose (2 * n - 1) * ((p - 1 : ℕ) : ℝ≥0∞) ^ (2 * n) * ((p : ℝ≥0∞)⁻¹) ^ L := by
  rw [pascalP_eq_iidSum, iidSum_iidSum, show n * 2 = 2 * n from by ring]
  exact negBinomial_apply hp (2 * n) L (by omega) hL

/-- The pointwise mass of the sum of `n` copies of `geomP p` (the `iidSum` form of `negBinomial_apply`). -/
theorem iidSum_geomP_apply {p : ℕ} (hp : 2 ≤ p) (n L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (iidSum (geomP p) n) L
      = (L - 1).choose (n - 1) * ((p - 1 : ℕ) : ℝ≥0∞) ^ n * ((p : ℝ≥0∞)⁻¹) ^ L :=
  negBinomial_apply hp n L hn hL

end GGMCollatz
