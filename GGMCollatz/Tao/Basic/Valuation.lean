import GGMCollatz.Tao.Basic.Collatz

/-!
# Valuation sequences, residue sequences and the iteration formula (counterpart of node C2 of tao-collatz)

Derived from `TaoCollatz/Basic/Valuation.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r). GGM (arXiv:2111.06170) §3, formulas (3.1)–(3.3), Lemmas 3.2 and 3.3.

* `pre a m`: the forward partial sum `a_{[1,m]}` (as in tao-collatz; indices beyond the length of `a` contribute 0).
* `valVec N n`: the valuation sequence `a_i(N) = ν_p(q S^{i-1}(N) + R_i(N))` (0-indexed).
* `digVec N n`: the digit sequence `S^{i-1}(N) mod p ∈ {1, …, p-1}`. `resVec N n = r ∘ digVec N n` is the residue sequence `R_i(N)`.
* `fint a R`: the integer-valued correction term `Σ_{m<n} q^{n-1-m} p^{a_{[1,m]}} R_m ∈ ℤ` (generalization of tao-collatz's `fnat`;
  it takes values in ℤ since `R` can be negative). The lengths of `a` and `R` may differ (the length `n` of `R` is the length of the sum).
* `syr_iterate_key`: **GGM (3.2) × p^{|a|}**: `p^{|a|} S^n(N) = q^n N + fint a R` (`p ∤ N`).
* `valDig_eq_iff_dvd`, `valDig_eq_iff_residue`: **GGM Lemma 3.3** (`k` valuations and `k+1` digits determine
  a single residue class modulo `p^{|a|+1}`). `valDig_stable_below`: **GGM Lemma 3.2**.
* `valVec_unique`: counterpart of tao-collatz's Lemma 2.1 (the observation in GGM §4 Step 2).
* `fint_split`, `fint_cons`: GGM (3.3) (tao-collatz's (1.26), (1.5)). `fint_inj_fixed_val`: GGM §6 Step 2
  (tao-collatz's Lemma 6.2).
-/

namespace GGMCollatz

open Finset

/-! ### The forward partial sum `pre` (independent of `p`, `q`, `r`) -/

/-- The forward partial sum `a_{[1,m]} = a₁ + ⋯ + a_m` (0-indexed; the part of `m` beyond the length contributes 0). -/
def pre {n : ℕ} (a : Fin n → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, if h : i < n then a ⟨i, h⟩ else 0

@[simp] theorem pre_zero {n : ℕ} (a : Fin n → ℕ) : pre a 0 = 0 := by simp [pre]

theorem pre_succ {n : ℕ} (a : Fin n → ℕ) (m : ℕ) :
    pre a (m + 1) = pre a m + (if h : m < n then a ⟨m, h⟩ else 0) := by
  unfold pre; rw [Finset.sum_range_succ]

/-- `pre` is monotone. -/
theorem pre_mono {n : ℕ} (a : Fin n → ℕ) {m m' : ℕ} (h : m ≤ m') : pre a m ≤ pre a m' := by
  unfold pre
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => Nat.zero_le _)

/-- If every entry is at least 1 then `m ≤ pre a m` (`m ≤ n`). -/
theorem le_pre_of_pos {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) {m : ℕ} (hm : m ≤ n) :
    m ≤ pre a m := by
  unfold pre
  calc m = ∑ _i ∈ Finset.range m, 1 := by simp
    _ ≤ ∑ i ∈ Finset.range m, if h : i < n then a ⟨i, h⟩ else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      rw [dif_pos (lt_of_lt_of_le hi hm)]
      exact ha _

/-- `pre a n` is the sum of all entries. -/
theorem pre_eq_fin_sum {n : ℕ} (a : Fin n → ℕ) : pre a n = ∑ i, a i := by
  unfold pre
  rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < n then a ⟨i, h⟩ else 0) n]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt]

/-- Peeling off the head: `a_{[1,m+1]} = a₀ + (tail a)_{[1,m]}` (for all `m`). -/
theorem pre_cons_head {n : ℕ} (a : Fin (n + 1) → ℕ) (m : ℕ) :
    pre a (m + 1) = a 0 + pre (Fin.tail a) m := by
  unfold pre
  rw [Finset.sum_range_succ']
  have hf0 : (if h : (0:ℕ) < n + 1 then a ⟨0, h⟩ else 0) = a 0 := by
    rw [dif_pos (Nat.succ_pos n)]; rfl
  rw [hf0, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hin : i < n
  · rw [dif_pos (by omega : i + 1 < n + 1), dif_pos hin]; rfl
  · rw [dif_neg (by omega : ¬ i + 1 < n + 1), dif_neg hin]

/-- The partial sum of the first `j` entries agrees with the partial sum of the whole sequence (`m ≤ j`). -/
theorem pre_castAdd {j l : ℕ} (a : Fin (j + l) → ℕ) {m : ℕ} (hm : m ≤ j) :
    pre (fun i => a (Fin.castAdd l i)) m = pre a m := by
  unfold pre
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hij : i < j := lt_of_lt_of_le hi hm
  rw [dif_pos hij, dif_pos (lt_of_lt_of_le hij (Nat.le_add_right j l))]
  rfl

/-- The partial sum up to `j + m` splits into the partial sum of the first `j` entries and a partial sum of the second part (`m ≤ l`). -/
theorem pre_natAdd_split {j l : ℕ} (a : Fin (j + l) → ℕ) {m : ℕ} (hm : m ≤ l) :
    pre a (j + m) = pre a j + pre (fun i => a (Fin.natAdd j i)) m := by
  unfold pre
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos (lt_of_lt_of_le hi hm), dif_pos (by omega : j + i < j + l)]
  rfl

/-- The partial sum of the sequence with its last entry dropped (`Fin.init`) agrees with that of the original sequence for `m ≤ n`. -/
theorem pre_init {n : ℕ} (a : Fin (n + 1) → ℕ) {m : ℕ} (hm : m ≤ n) :
    pre (Fin.init a) m = pre a m := by
  unfold pre
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos (by omega : i < n), dif_pos (by omega : i < n + 1)]
  rfl

/-- Full partial sum = partial sum with the last entry dropped + the last entry. -/
theorem pre_succ_init {n : ℕ} (a : Fin (n + 1) → ℕ) :
    pre a (n + 1) = pre (Fin.init a) n + a (Fin.last n) := by
  rw [pre_succ, pre_init a (le_refl n), dif_pos (Nat.lt_succ_self n)]
  rfl

/-- The first `m` entries of the reversed sequence and the first `n - m` entries of the original sequence cover the whole. -/
theorem pre_comp_rev {n : ℕ} (a : Fin n → ℕ) {m : ℕ} (hm : m ≤ n) :
    pre (a ∘ Fin.rev) m + pre a (n - m) = pre a n := by
  set g : ℕ → ℕ := fun i => if h : i < n then a ⟨i, h⟩ else 0 with hg
  have hpre : ∀ (m' : ℕ), pre a m' = ∑ i ∈ Finset.range m', g i := fun _ => rfl
  have hrev : pre (a ∘ Fin.rev) m = ∑ i ∈ Finset.range m, g (n - 1 - i) := by
    unfold pre
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hin : i < n := lt_of_lt_of_le hi hm
    have hni : n - 1 - i < n := by omega
    simp only [hg]
    rw [dif_pos hin, dif_pos hni]
    show a (Fin.rev ⟨i, hin⟩) = a ⟨n - 1 - i, hni⟩
    congr 1
    apply Fin.ext
    rw [Fin.val_rev]
    show n - (i + 1) = n - 1 - i
    omega
  rw [hrev, hpre, hpre]
  have hreflect : (∑ i ∈ Finset.range m, g (n - 1 - i))
      = ∑ i ∈ Finset.range m, g (n - m + i) := by
    rw [← Finset.sum_range_reflect (fun i => g (n - m + i)) m]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    congr 1
    omega
  rw [hreflect]
  have hIco : (∑ i ∈ Finset.range m, g (n - m + i)) = ∑ i ∈ Finset.Ico (n - m) n, g i := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.sub_sub_self hm]
  rw [hIco, add_comm, Finset.range_eq_Ico,
    Finset.sum_Ico_consecutive _ (Nat.zero_le _) (Nat.sub_le n m), Finset.range_eq_Ico]

/-- Bound for the geometric sum: `∑_{j<n} q^j ≤ q^n` (`q ≥ 2`, in ℤ). -/
theorem geom_sum_le_pow {q : ℤ} (hq : 2 ≤ q) (n : ℕ) : (∑ j ∈ Finset.range n, q ^ j) ≤ q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hpos : 0 ≤ q ^ n := pow_nonneg (by omega) n
    nlinarith

/-- Reflected geometric sum: `∑_{m<n} q^{n-1-m} ≤ q^n`. -/
theorem sum_pow_reflect_le {q : ℤ} (hq : 2 ≤ q) (n : ℕ) :
    (∑ m ∈ Finset.range n, q ^ (n - 1 - m)) ≤ q ^ n := by
  rw [Finset.sum_range_reflect (fun j => q ^ j) n]
  exact geom_sum_le_pow hq n

/-- If `p^s u = p^t v`, `p ∤ u` and `p ∤ v`, then `s = t` and `u = v` (in ℤ; tao-collatz's `two_pow_odd_eq`). -/
theorem pow_mul_eq_pow_mul {p : ℤ} (hp : p ≠ 0) {s t : ℕ} {u v : ℤ} (hu : ¬ p ∣ u) (hv : ¬ p ∣ v)
    (h : p ^ s * u = p ^ t * v) : s = t ∧ u = v := by
  wlog hst : s ≤ t generalizing s t u v
  · obtain ⟨h1, h2⟩ := this hv hu h.symm (not_le.mp hst).le
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [pow_add, mul_assoc] at h
  have hcancel : u = p ^ d * v := mul_left_cancel₀ (pow_ne_zero s hp) h
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp at hcancel; exact ⟨rfl, hcancel⟩
  · exact absurd (by rw [hcancel]; exact Dvd.dvd.mul_right (dvd_pow_self p hd.ne') v) hu

namespace Family

variable (F : Family)

/-! ### Valuation sequences, digit sequences, residue sequences -/

/-- The valuation sequence `a⁽ⁿ⁾(N)`: `a_i = ν_p(q·S^i(N) + r(S^i(N) mod p))` (0-indexed). -/
def valVec (N n : ℕ) : Fin n → ℕ := fun i => padicValNat F.p (F.lift (F.S^[(i : ℕ)] N))

/-- The digit sequence: `S^i(N) mod p` (lies in `{1, …, p-1}` if `p ∤ N`). -/
def digVec (N n : ℕ) : Fin n → ℕ := fun i => F.S^[(i : ℕ)] N % F.p

/-- The residue sequence `R⁽ⁿ⁾(N)`: `R_i = r(S^i(N) mod p)` (`r ∘ digVec`). -/
def resVec (N n : ℕ) : Fin n → ℤ := fun i => F.r (F.digVec N n i)

/-- Partial sums of the valuations (ℕ-indexed form; used in the induction for the iteration formula). -/
def valSum (N n : ℕ) : ℕ := ∑ i ∈ Finset.range n, padicValNat F.p (F.lift (F.S^[i] N))

/-- The residue sequence (ℕ-indexed form). -/
def resSeq (N i : ℕ) : ℤ := F.r (F.S^[i] N % F.p)

/-- The integer-valued correction term `Σ_{m<n} q^{n-1-m} p^{a_{[1,m]}} R_m` (generalization of tao-collatz's `fnat`;
GGM (3.2)'s `F_n(a, R)` multiplied by `p^{|a|}`). The length `k` of `a` and the length `n` of `R` may differ. -/
def fint {k n : ℕ} (a : Fin k → ℕ) (R : Fin n → ℤ) : ℤ :=
  ∑ m : Fin n, (F.q : ℤ) ^ (n - 1 - (m : ℕ)) * (F.p : ℤ) ^ pre a m * R m

@[simp] theorem valSum_zero (N : ℕ) : F.valSum N 0 = 0 := by simp [valSum]

theorem valSum_succ (N n : ℕ) :
    F.valSum N (n + 1) = F.valSum N n + padicValNat F.p (F.lift (F.S^[n] N)) := by
  unfold valSum; rw [Finset.sum_range_succ]

theorem valSum_mono (N : ℕ) {m n : ℕ} (h : m ≤ n) : F.valSum N m ≤ F.valSum N n := by
  unfold valSum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => Nat.zero_le _)

/-- `pre (valVec N n) m = valSum N m` (`m ≤ n`). -/
theorem pre_valVec {N n m : ℕ} (hmn : m ≤ n) : pre (F.valVec N n) m = F.valSum N m := by
  unfold pre valSum valVec
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [dif_pos (lt_of_lt_of_le hi hmn)]

/-- The valuations are at least 1 (`p ∤ N`). -/
theorem valVec_pos {N : ℕ} (hN : N % F.p ≠ 0) (n : ℕ) (i : Fin n) : 1 ≤ F.valVec N n i :=
  F.one_le_val_lift (F.syr_iterate_mod_ne_zero hN i)

/-- The digits lie in `{1, …, p-1}` (`p ∤ N`). -/
theorem digVec_pos_lt {N : ℕ} (hN : N % F.p ≠ 0) (n : ℕ) (i : Fin n) :
    0 < F.digVec N n i ∧ F.digVec N n i < F.p :=
  F.mod_pos_lt (F.syr_iterate_mod_ne_zero hN i)

/-- Peeling off the head of the valuation sequence: `a⁽ⁿ⁺¹⁾(N) = (ν(N), a⁽ⁿ⁾(S N))`. -/
theorem valVec_succ (N n : ℕ) :
    F.valVec N (n + 1) = Fin.cons (padicValNat F.p (F.lift N)) (F.valVec (F.S N) n) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · simp only [valVec, Fin.cons_succ, Fin.val_succ, Function.iterate_succ_apply]

/-- Peeling off the head of the digit sequence. -/
theorem digVec_succ (N n : ℕ) :
    F.digVec N (n + 1) = Fin.cons (N % F.p) (F.digVec (F.S N) n) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · simp only [digVec, Fin.cons_succ, Fin.val_succ, Function.iterate_succ_apply]

/-- The last entry of the valuation sequence: `a⁽ⁿ⁺¹⁾(N) = (a⁽ⁿ⁾(N), ν(S^n N))`. -/
theorem valVec_snoc (N n : ℕ) :
    F.valVec N (n + 1) = Fin.snoc (F.valVec N n) (padicValNat F.p (F.lift (F.S^[n] N))) := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [valVec]
  · simp [valVec]

/-- Restriction of the digit sequence to an initial segment. -/
theorem digVec_init (N n : ℕ) : Fin.init (F.digVec N (n + 1)) = F.digVec N n := by
  funext i; rfl

/-- Restriction of the valuation sequence to an initial segment. -/
theorem valVec_init (N n : ℕ) : Fin.init (F.valVec N (n + 1)) = F.valVec N n := by
  funext i; rfl

/-! ### Properties of `r` -/

/-- If `0 < j < p` then `p ∤ r(j)` (from conditions (a), (c): `r(j) ≡ -qj (mod p)`). -/
theorem r_not_dvd {j : ℕ} (h0 : 0 < j) (hj : j < F.p) : ¬ (F.p : ℤ) ∣ F.r j := by
  intro hr
  have hc := F.divisible j h0 hj
  have hqj : (F.p : ℤ) ∣ (F.q : ℤ) * j := by
    have := dvd_sub hc hr
    simpa using this
  have hcop : IsCoprime (F.p : ℤ) (F.q : ℤ) := Nat.isCoprime_iff_coprime.mpr F.coprime
  have hpj : (F.p : ℤ) ∣ (j : ℤ) := hcop.dvd_of_dvd_mul_left hqj
  have hpj' : F.p ∣ j := Int.natCast_dvd_natCast.mp hpj
  exact absurd (Nat.le_of_dvd h0 hpj') (by omega)

/-- `r` is injective on `{1, …, p-1}` (since `r(j) ≡ -qj (mod p)`). Hence the residue sequence `R⁽ⁿ⁾(N)` and
the digit sequence `digVec N n` determine each other, and the condition `R ∈ {r(1),…,r(p-1)}^{k+1}` of GGM Lemma 3.3 may be stated with digit sequences. -/
theorem r_inj {j j' : ℕ} (h0 : 0 < j) (hj : j < F.p) (h0' : 0 < j') (hj' : j' < F.p)
    (h : F.r j = F.r j') : j = j' := by
  have hc := F.divisible j h0 hj
  have hc' := F.divisible j' h0' hj'
  have h1 : (F.p : ℤ) ∣ (F.q : ℤ) * ((j' : ℤ) - j) := by
    have := dvd_sub hc' hc
    have heq : (F.q : ℤ) * j' + F.r j' - ((F.q : ℤ) * j + F.r j) = (F.q : ℤ) * ((j' : ℤ) - j) := by
      rw [h]; ring
    rwa [heq] at this
  have hcop : IsCoprime (F.p : ℤ) (F.q : ℤ) := Nat.isCoprime_iff_coprime.mpr F.coprime
  have h2 : j ≡ j' [MOD F.p] := Nat.modEq_iff_dvd.mpr (hcop.dvd_of_dvd_mul_left h1)
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h2

/-- Equality of residue sequences is equivalent to equality of digit sequences (`p ∤ N`, `p ∤ M`). -/
theorem resVec_eq_iff_digVec_eq {N M : ℕ} (hN : N % F.p ≠ 0) (hM : M % F.p ≠ 0) (n : ℕ) :
    F.resVec N n = F.resVec M n ↔ F.digVec N n = F.digVec M n := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    exact F.r_inj (F.digVec_pos_lt hN n i).1 (F.digVec_pos_lt hN n i).2
      (F.digVec_pos_lt hM n i).1 (F.digVec_pos_lt hM n i).2 hi
  · intro h
    funext i
    simp only [resVec, h]

/-- Cancellation: `p^s ∣ q^e · X` implies `p^s ∣ X` (`p` and `q` are coprime). -/
theorem dvd_of_dvd_q_pow_mul {s e : ℕ} {X : ℤ} (h : (F.p : ℤ) ^ s ∣ (F.q : ℤ) ^ e * X) :
    (F.p : ℤ) ^ s ∣ X := by
  have hcop : IsCoprime ((F.p : ℤ) ^ s) ((F.q : ℤ) ^ e) :=
    (Nat.isCoprime_iff_coprime.mpr F.coprime).pow
  exact hcop.dvd_of_dvd_mul_left h

/-- If `p ∣ q^e (qN + r(j))` and `0 < j < p`, then `N mod p = j`. -/
theorem mod_eq_of_dvd {N j e : ℕ} (h0 : 0 < j) (hj : j < F.p)
    (h : (F.p : ℤ) ∣ (F.q : ℤ) ^ e * ((F.q : ℤ) * N + F.r j)) : N % F.p = j := by
  have h1 : (F.p : ℤ) ∣ (F.q : ℤ) * N + F.r j := by
    simpa using F.dvd_of_dvd_q_pow_mul (s := 1) (by simpa using h)
  have hc := F.divisible j h0 hj
  have h2 : (F.p : ℤ) ∣ (F.q : ℤ) * ((N : ℤ) - j) := by
    have := dvd_sub h1 hc
    have heq : (F.q : ℤ) * N + F.r j - ((F.q : ℤ) * j + F.r j) = (F.q : ℤ) * ((N : ℤ) - j) := by
      ring
    rwa [heq] at this
  have hcop : IsCoprime (F.p : ℤ) (F.q : ℤ) := Nat.isCoprime_iff_coprime.mpr F.coprime
  have h3 : (F.p : ℤ) ∣ (N : ℤ) - j := hcop.dvd_of_dvd_mul_left h2
  have h4 : j ≡ N [MOD F.p] := Nat.modEq_iff_dvd.mpr h3
  rw [← h4, Nat.mod_eq_of_lt hj]

/-! ### Algebra of the correction term `fint` -/

/-- `fint` depends only on `pre a m` (`m < n`). -/
theorem fint_congr_pre {k k' n : ℕ} {a : Fin k → ℕ} {a' : Fin k' → ℕ} (R : Fin n → ℤ)
    (h : ∀ m, m < n → pre a m = pre a' m) : F.fint a R = F.fint a' R := by
  unfold fint
  exact Finset.sum_congr rfl fun m _ => by rw [h m m.isLt]

/-- **Peeling off the head** (GGM (3.3) with `i = 1`; tao-collatz's `fnat_cons`):
`fint a R = q^n R₀ + p^{a₀} fint (tail a) (tail R)`. -/
theorem fint_cons {k n : ℕ} (a : Fin (k + 1) → ℕ) (R : Fin (n + 1) → ℤ) :
    F.fint a R = (F.q : ℤ) ^ n * R 0 + (F.p : ℤ) ^ (a 0) * F.fint (Fin.tail a) (Fin.tail R) := by
  unfold fint
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro m _
    rw [Fin.val_succ, pre_cons_head, pow_add,
      show n + 1 - 1 - ((m : ℕ) + 1) = n - 1 - (m : ℕ) by omega]
    simp only [Fin.tail]
    ring

/-- **Splitting formula** (GGM (3.3); tao-collatz's `fnat_split`): cutting at index `j`,
`fint a R = q^l · fint(first part) + p^{a_{[1,j]}} · fint(second part)`. -/
theorem fint_split {j l : ℕ} (a : Fin (j + l) → ℕ) (R : Fin (j + l) → ℤ) :
    F.fint a R
      = (F.q : ℤ) ^ l * F.fint (fun i => a (Fin.castAdd l i)) (fun i => R (Fin.castAdd l i))
        + (F.p : ℤ) ^ pre a j * F.fint (fun i => a (Fin.natAdd j i)) (fun i => R (Fin.natAdd j i)) := by
  unfold fint
  rw [Fin.sum_univ_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro m _
    rw [Fin.val_castAdd, pre_castAdd a (le_of_lt m.isLt),
      show j + l - 1 - (m : ℕ) = l + (j - 1 - (m : ℕ)) by omega, pow_add]
    ring
  · apply Finset.sum_congr rfl
    intro m _
    rw [Fin.val_natAdd, pre_natAdd_split a (le_of_lt m.isLt), pow_add,
      show j + l - 1 - (j + (m : ℕ)) = l - 1 - (m : ℕ) by omega]
    ring

/-- `fint a R ≡ q^n R₀ (mod p)` (the entries of `a` are at least 1, and the length of `R` is `n + 1 ≤ k + 1`).
Generalization of tao-collatz's `fnat_mod_two_of_pos`. -/
theorem fint_modp {k n : ℕ} (a : Fin k → ℕ) (ha : ∀ i, 1 ≤ a i) (R : Fin (n + 1) → ℤ)
    (hn : n ≤ k) : (F.p : ℤ) ∣ F.fint a R - (F.q : ℤ) ^ n * R 0 := by
  unfold fint
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pre_zero, pow_zero, mul_one, Nat.sub_zero, Nat.add_sub_cancel]
  rw [add_sub_cancel_left]
  apply Finset.dvd_sum
  intro m _
  have hm : (m : ℕ) + 1 ≤ k := by have := m.isLt; omega
  have h1 : 1 ≤ pre a ((m : ℕ) + 1) := le_trans (by omega) (le_pre_of_pos a ha hm)
  rw [Fin.val_succ]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
  rw [hd, pow_add, pow_one]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_refl _) _) _) _

/-- If `R 0` is not divisible by `p` and the entries of `a` are at least 1, then `p ∤ fint a R` (length
`n + 1 ≤ k + 1`). -/
theorem fint_not_dvd {k n : ℕ} (a : Fin k → ℕ) (ha : ∀ i, 1 ≤ a i) (R : Fin (n + 1) → ℤ)
    (hn : n ≤ k) (hR : ¬ (F.p : ℤ) ∣ R 0) : ¬ (F.p : ℤ) ∣ F.fint a R := by
  intro h
  have h1 := dvd_sub h (F.fint_modp a ha R hn)
  rw [sub_sub_cancel] at h1
  have hcop : IsCoprime (F.p : ℤ) ((F.q : ℤ) ^ n) :=
    (Nat.isCoprime_iff_coprime.mpr F.coprime).pow_right
  exact hR (hcop.dvd_of_dvd_mul_left h1)

/-- **GGM §6 Step 2 (tao-collatz's Lemma 6.2)**: for fixed `R` whose entries are not divisible by `p`,
`fint (·) R` is injective on sequences with positive entries and equal total valuation `a_{[1,n]}`. -/
theorem fint_inj_fixed_val : ∀ (n : ℕ) (a a' : Fin n → ℕ) (R : Fin n → ℤ),
    (∀ i, 1 ≤ a i) → (∀ i, 1 ≤ a' i) → (∀ i, ¬ (F.p : ℤ) ∣ R i) →
    pre a n = pre a' n → F.fint a R = F.fint a' R → a = a' := by
  intro n
  induction n with
  | zero => intro a a' _ _ _ _ _ _; exact funext (fun i => i.elim0)
  | succ n ih =>
    intro a a' R ha ha' hR hpre hf
    rw [F.fint_cons, F.fint_cons] at hf
    have hFF : (F.p : ℤ) ^ (a 0) * F.fint (Fin.tail a) (Fin.tail R)
        = (F.p : ℤ) ^ (a' 0) * F.fint (Fin.tail a') (Fin.tail R) := by linarith
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h00 : a 0 = a' 0 := by
        have e1 : pre a 1 = a 0 := by simp [pre]
        have e2 : pre a' 1 = a' 0 := by simp [pre]
        rw [e1, e2] at hpre; exact hpre
      exact funext (fun i => by rw [Fin.fin_one_eq_zero i]; exact h00)
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hnd : ∀ (b : Fin (n' + 1 + 1) → ℕ), (∀ i, 1 ≤ b i) →
          ¬ (F.p : ℤ) ∣ F.fint (Fin.tail b) (Fin.tail R) := by
        intro b hb
        exact F.fint_not_dvd (Fin.tail b) (fun i => hb i.succ) (Fin.tail R) (by omega)
          (hR _)
      have hp0 : (F.p : ℤ) ≠ 0 := by exact_mod_cast F.p_ne_zero
      obtain ⟨h0eq, hFeq⟩ := pow_mul_eq_pow_mul hp0 (hnd a ha) (hnd a' ha') hFF
      have hpretail : pre (Fin.tail a) (n' + 1) = pre (Fin.tail a') (n' + 1) := by
        have ea := pre_cons_head a (n' + 1)
        have ea' := pre_cons_head a' (n' + 1)
        rw [ea, ea', h0eq] at hpre; omega
      have htail := ih (Fin.tail a) (Fin.tail a') (Fin.tail R) (fun i => ha i.succ)
        (fun i => ha' i.succ) (fun i => hR i.succ) hpretail hFeq
      exact funext (fun i => Fin.cases h0eq (fun j => congrFun htail j) i)

/-! ### The iteration formula (GGM (3.2) × `p^{|a|}`) -/

/-- Recursion for the sum: `Σ_{m<n+1} q^{n-m} f(m) = q Σ_{m<n} q^{n-1-m} f(m) + f(n)`. -/
theorem sum_q_pow_succ (f : ℕ → ℤ) (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), (F.q : ℤ) ^ (n + 1 - 1 - m) * f m)
      = (F.q : ℤ) * (∑ m ∈ Finset.range n, (F.q : ℤ) ^ (n - 1 - m) * f m) + f n := by
  rw [Finset.sum_range_succ, show n + 1 - 1 - n = 0 by omega, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_range] at hm
  rw [show n + 1 - 1 - m = (n - 1 - m) + 1 by omega, pow_succ]
  ring

/-- Core of the induction for the iteration formula (ℕ-indexed form). -/
theorem key_aux {N : ℕ} (hN : N % F.p ≠ 0) (n : ℕ) :
    (F.p : ℤ) ^ F.valSum N n * (F.S^[n] N : ℤ)
      = (F.q : ℤ) ^ n * N
        + ∑ m ∈ Finset.range n, (F.q : ℤ) ^ (n - 1 - m) * ((F.p : ℤ) ^ F.valSum N m * F.resSeq N m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := F.pow_val_mul_syr_int (F.syr_iterate_mod_ne_zero hN n)
    rw [show F.r (F.S^[n] N % F.p) = F.resSeq N n from rfl] at hstep
    rw [F.sum_q_pow_succ (fun m => (F.p : ℤ) ^ F.valSum N m * F.resSeq N m) n,
      F.valSum_succ, pow_add, Function.iterate_succ_apply', mul_assoc, hstep, pow_succ]
    linear_combination (F.q : ℤ) * ih

/-- Writing `fint (valVec N n) (resVec N n)` as an ℕ-indexed sum. -/
theorem fint_valVec (N n : ℕ) :
    F.fint (F.valVec N n) (F.resVec N n)
      = ∑ m ∈ Finset.range n, (F.q : ℤ) ^ (n - 1 - m) * ((F.p : ℤ) ^ F.valSum N m * F.resSeq N m) := by
  unfold fint
  rw [← Fin.sum_univ_eq_sum_range
    (fun m => (F.q : ℤ) ^ (n - 1 - m) * ((F.p : ℤ) ^ F.valSum N m * F.resSeq N m)) n]
  apply Finset.sum_congr rfl
  intro m _
  rw [F.pre_valVec (le_of_lt m.isLt)]
  simp only [resVec, digVec, resSeq]
  ring

/-- **GGM (3.2) × `p^{|a|}`** (tao-collatz's `syr_iterate_key`): if `p ∤ N` then
`p^{|a⁽ⁿ⁾(N)|} S^n(N) = q^n N + fint a⁽ⁿ⁾(N) R⁽ⁿ⁾(N)`. -/
theorem syr_iterate_key {N : ℕ} (hN : N % F.p ≠ 0) (n : ℕ) :
    (F.p : ℤ) ^ pre (F.valVec N n) n * (F.S^[n] N : ℤ)
      = (F.q : ℤ) ^ n * N + F.fint (F.valVec N n) (F.resVec N n) := by
  rw [F.pre_valVec (le_refl n), F.fint_valVec]
  exact F.key_aux hN n

/-- The affine map `Aff_{a,R}(N) = (q^n N + fint a R) / p^{|a|}` (division in ℤ; tao-collatz's `Aff`). -/
def Aff {n : ℕ} (N : ℕ) (a : Fin n → ℕ) (R : Fin n → ℤ) : ℤ :=
  ((F.q : ℤ) ^ n * N + F.fint a R) / (F.p : ℤ) ^ pre a n

/-- On its own valuation and residue sequences, `Aff` agrees with the iterate of `S`. -/
theorem aff_valVec_eq_syr {N : ℕ} (hN : N % F.p ≠ 0) (n : ℕ) :
    F.Aff N (F.valVec N n) (F.resVec N n) = F.S^[n] N := by
  unfold Aff
  rw [← F.syr_iterate_key hN n]
  exact Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by exact_mod_cast F.p_ne_zero))

/-! ### Size bounds (tao-collatz's `fnat_valVec_le`, `syr_descent_bound`) -/

/-- A uniform upper bound for `|r(j)|` (`j < p`). -/
def rBound : ℤ := ∑ j ∈ Finset.range F.p, |F.r j|

theorem rBound_nonneg : 0 ≤ F.rBound :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_r_le_rBound {j : ℕ} (hj : j < F.p) : |F.r j| ≤ F.rBound := by
  unfold rBound
  exact Finset.single_le_sum (f := fun j => |F.r j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr hj)

/-- `|fint a R| ≤ p^{|a|} q^n B` (`|R_m| ≤ B`). -/
theorem abs_fint_le {k n : ℕ} (a : Fin k → ℕ) (R : Fin n → ℤ) {B : ℤ} (hB0 : 0 ≤ B)
    (hB : ∀ m, |R m| ≤ B) : |F.fint a R| ≤ (F.p : ℤ) ^ pre a n * (F.q : ℤ) ^ n * B := by
  unfold fint
  have hp : (1 : ℤ) ≤ F.p := by exact_mod_cast F.p_pos
  have hq2 : (2 : ℤ) ≤ F.q := by exact_mod_cast F.two_le_q
  calc |∑ m : Fin n, (F.q : ℤ) ^ (n - 1 - (m : ℕ)) * (F.p : ℤ) ^ pre a m * R m|
      ≤ ∑ m : Fin n, |(F.q : ℤ) ^ (n - 1 - (m : ℕ)) * (F.p : ℤ) ^ pre a m * R m| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m : Fin n, (F.q : ℤ) ^ (n - 1 - (m : ℕ)) * ((F.p : ℤ) ^ pre a n * B) := by
        apply Finset.sum_le_sum
        intro m _
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
          mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul (pow_le_pow_right₀ hp (pre_mono a (le_of_lt m.isLt))) (hB m)
          (abs_nonneg _) (by positivity)
    _ = (F.p : ℤ) ^ pre a n * B * ∑ m ∈ Finset.range n, (F.q : ℤ) ^ (n - 1 - m) := by
        rw [← Fin.sum_univ_eq_sum_range (fun m => (F.q : ℤ) ^ (n - 1 - m)) n, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ (F.p : ℤ) ^ pre a n * B * (F.q : ℤ) ^ n :=
        mul_le_mul_of_nonneg_left (sum_pow_reflect_le hq2 n) (by positivity)
    _ = (F.p : ℤ) ^ pre a n * (F.q : ℤ) ^ n * B := by ring

/-- **Descent bound** (tao-collatz's `syr_descent_bound`):
`p^{valSum} S^n(N) ≤ q^n N + p^{valSum} q^n · rBound`. -/
theorem syr_descent_bound {N : ℕ} (hN : N % F.p ≠ 0) (n : ℕ) :
    (F.p : ℤ) ^ F.valSum N n * (F.S^[n] N : ℤ)
      ≤ (F.q : ℤ) ^ n * N + (F.p : ℤ) ^ F.valSum N n * (F.q : ℤ) ^ n * F.rBound := by
  have hkey := F.syr_iterate_key hN n
  rw [F.pre_valVec (le_refl n)] at hkey
  rw [hkey]
  have hb := F.abs_fint_le (F.valVec N n) (F.resVec N n) F.rBound_nonneg
    (fun m => F.abs_r_le_rBound (F.digVec_pos_lt hN n m).2)
  rw [F.pre_valVec (le_refl n)] at hb
  have := le_abs_self (F.fint (F.valVec N n) (F.resVec N n))
  linarith

/-! ### GGM Lemmas 3.3 and 3.2 (the valuation and digit sequences determine a single residue class modulo `p^{|a|+1}`) -/

/-- Forward direction of Lemma 3.3: if `p ∤ N`, then for its own `k` valuations and `k+1` digits,
`p^{|a|+1} ∣ q^{k+1} N + fint a (r ∘ j)`. -/
theorem dvd_of_valDig {N : ℕ} (hN : N % F.p ≠ 0) (k : ℕ) :
    (F.p : ℤ) ^ (pre (F.valVec N k) k + 1)
      ∣ (F.q : ℤ) ^ (k + 1) * N + F.fint (F.valVec N k) (fun i => F.r (F.digVec N (k + 1) i)) := by
  have hkey := F.syr_iterate_key hN (k + 1)
  have hf : F.fint (F.valVec N (k + 1)) (F.resVec N (k + 1))
      = F.fint (F.valVec N k) (fun i => F.r (F.digVec N (k + 1) i)) := by
    apply F.fint_congr_pre
    intro m hm
    rw [F.pre_valVec (by omega), F.pre_valVec (by omega)]
  rw [hf] at hkey
  rw [← hkey, F.pre_valVec (N := N) (n := k + 1) (m := k + 1) (le_refl _), F.valSum_succ,
    ← F.pre_valVec (N := N) (n := k) (le_refl k)]
  have h1 := F.one_le_val_lift (F.syr_iterate_mod_ne_zero hN k)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
  rw [hd]
  exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _

/-- Converse direction of Lemma 3.3 (core of the induction): if `p^{|a|+1} ∣ q^{k+1} N + fint a (r ∘ j)`, then
`p ∤ N`, the valuation sequence of `N` is `a`, and its digit sequence is `j`. -/
theorem valDig_of_dvd : ∀ (k N : ℕ) (a : Fin k → ℕ) (j : Fin (k + 1) → ℕ),
    (∀ i, 1 ≤ a i) → (∀ i, 0 < j i ∧ j i < F.p) →
    (F.p : ℤ) ^ (pre a k + 1) ∣ (F.q : ℤ) ^ (k + 1) * N + F.fint a (fun i => F.r (j i)) →
    N % F.p ≠ 0 ∧ F.valVec N k = a ∧ F.digVec N (k + 1) = j := by
  intro k
  induction k with
  | zero =>
    intro N a j _ hj h
    have hf : F.fint a (fun i => F.r (j i)) = F.r (j 0) := by
      simp [fint]
    rw [hf] at h
    simp only [pre_zero, zero_add, pow_one] at h
    have hmod : N % F.p = j 0 :=
      F.mod_eq_of_dvd (hj 0).1 (hj 0).2 (e := 0) (by simpa using h)
    refine ⟨by rw [hmod]; exact (Nat.pos_iff_ne_zero.mp (hj 0).1), funext (fun i => i.elim0), ?_⟩
    funext i
    rw [Fin.fin_one_eq_zero i]
    simpa [digVec] using hmod
  | succ k ih =>
    intro N a j ha hj h
    set G' := F.fint (Fin.tail a) (fun i => F.r (Fin.tail j i)) with hG'
    have hcons : F.fint a (fun i => F.r (j i))
        = (F.q : ℤ) ^ (k + 1) * F.r (j 0) + (F.p : ℤ) ^ (a 0) * G' := by
      rw [F.fint_cons]; rfl
    have hpre : pre a (k + 1) = a 0 + pre (Fin.tail a) k := pre_cons_head a k
    have hX : (F.q : ℤ) ^ (k + 1 + 1) * N + F.fint a (fun i => F.r (j i))
        = (F.q : ℤ) ^ (k + 1) * ((F.q : ℤ) * N + F.r (j 0)) + (F.p : ℤ) ^ (a 0) * G' := by
      rw [hcons]; ring
    rw [hX, hpre] at h
    have ha0 : 1 ≤ a 0 := ha 0
    -- (i) The leading digit
    have hdvd_a0 : (F.p : ℤ) ^ (a 0) ∣ (F.q : ℤ) ^ (k + 1) * ((F.q : ℤ) * N + F.r (j 0)) := by
      have h1 : (F.p : ℤ) ^ (a 0) ∣ (F.p : ℤ) ^ (a 0 + pre (Fin.tail a) k + 1) :=
        pow_dvd_pow _ (by omega)
      have h2 := dvd_trans h1 h
      have h3 : (F.p : ℤ) ^ (a 0) ∣ (F.p : ℤ) ^ (a 0) * G' := dvd_mul_right _ _
      simpa using dvd_sub h2 h3
    have hmod : N % F.p = j 0 := by
      apply F.mod_eq_of_dvd (hj 0).1 (hj 0).2 (e := k + 1)
      exact dvd_trans (dvd_pow_self _ (by omega)) hdvd_a0
    have hN : N % F.p ≠ 0 := by rw [hmod]; exact Nat.pos_iff_ne_zero.mp (hj 0).1
    -- (ii) `lift N = p^{a₀} W`
    have hlift : ((F.lift N : ℕ) : ℤ) = (F.q : ℤ) * N + F.r (j 0) := by
      rw [F.lift_intCast hN, hmod]
    have hdl : (F.p : ℤ) ^ (a 0) ∣ ((F.lift N : ℕ) : ℤ) := by
      rw [hlift]; exact F.dvd_of_dvd_q_pow_mul hdvd_a0
    have hdl' : F.p ^ (a 0) ∣ F.lift N := by exact_mod_cast hdl
    obtain ⟨W, hW⟩ := hdl'
    -- (iii) The remaining division
    have hX2 : (F.q : ℤ) ^ (k + 1) * ((F.q : ℤ) * N + F.r (j 0)) + (F.p : ℤ) ^ (a 0) * G'
        = (F.p : ℤ) ^ (a 0) * ((F.q : ℤ) ^ (k + 1) * W + G') := by
      rw [← hlift, hW]; push_cast; ring
    rw [hX2, show a 0 + pre (Fin.tail a) k + 1 = a 0 + (pre (Fin.tail a) k + 1) by omega,
      pow_add] at h
    have hp0 : (F.p : ℤ) ^ (a 0) ≠ 0 := pow_ne_zero _ (by exact_mod_cast F.p_ne_zero)
    have hrest : (F.p : ℤ) ^ (pre (Fin.tail a) k + 1) ∣ (F.q : ℤ) ^ (k + 1) * W + G' :=
      (mul_dvd_mul_iff_left hp0).mp h
    -- (iv) `p ∤ W`
    have hW0 : W % F.p ≠ 0 := by
      intro hWp
      have hpW : (F.p : ℤ) ∣ (W : ℤ) := by
        exact_mod_cast Nat.dvd_of_mod_eq_zero hWp
      have hpX : (F.p : ℤ) ∣ (F.q : ℤ) ^ (k + 1) * W + G' :=
        dvd_trans (dvd_pow_self _ (by omega)) hrest
      have hpG : (F.p : ℤ) ∣ G' := by
        have := dvd_sub hpX (Dvd.dvd.mul_left hpW ((F.q : ℤ) ^ (k + 1)))
        simpa using this
      apply F.fint_not_dvd (Fin.tail a) (fun i => ha i.succ) (fun i => F.r (Fin.tail j i))
        (le_refl k) (F.r_not_dvd (hj 1).1 (hj 1).2) hpG
    -- (v) The induction hypothesis
    obtain ⟨_, hva, hdj⟩ := ih W (Fin.tail a) (Fin.tail j) (fun i => ha i.succ)
      (fun i => hj i.succ) hrest
    -- (vi) `ν(lift N) = a₀`, `S N = W`
    have hval : padicValNat F.p (F.lift N) = a 0 := F.padicValNat_eq_of_mul hW.symm hW0
    have hSN : F.S N = W := F.oddPart_eq_of_mul hW.symm hW0
    refine ⟨hN, ?_, ?_⟩
    · rw [F.valVec_succ, hval, hSN, hva]; exact Fin.cons_self_tail a
    · rw [F.digVec_succ, hmod, hSN, hdj]; exact Fin.cons_self_tail j

/-- **GGM Lemma 3.3** (divisibility form): for `k` valuations `a` (entries ≥ 1) and `k+1` digits `j` (`0 < j_i < p`),
`N` is not divisible by `p` and has valuation sequence `a` and digit sequence `j` if and only if `p^{|a|+1} ∣ q^{k+1} N + fint a (r ∘ j)`. -/
theorem valDig_eq_iff_dvd (N k : ℕ) (a : Fin k → ℕ) (ha : ∀ i, 1 ≤ a i)
    (j : Fin (k + 1) → ℕ) (hj : ∀ i, 0 < j i ∧ j i < F.p) :
    (N % F.p ≠ 0 ∧ F.valVec N k = a ∧ F.digVec N (k + 1) = j) ↔
      (F.p : ℤ) ^ (pre a k + 1) ∣ (F.q : ℤ) ^ (k + 1) * N + F.fint a (fun i => F.r (j i)) := by
  constructor
  · rintro ⟨hN, rfl, rfl⟩
    exact F.dvd_of_valDig hN k
  · exact F.valDig_of_dvd k N a j ha hj

/-- The residue class of Lemma 3.3: `-(q^{k+1})⁻¹ · fint a (r ∘ j) mod p^{|a|+1}`. -/
noncomputable def valuationResidue (k : ℕ) (a : Fin k → ℕ) (j : Fin (k + 1) → ℕ) :
    ZMod (F.p ^ (pre a k + 1)) :=
  -((F.q : ZMod (F.p ^ (pre a k + 1))) ^ (k + 1))⁻¹
    * ((F.fint a (fun i => F.r (j i)) : ℤ) : ZMod (F.p ^ (pre a k + 1)))

/-- `q` is invertible modulo `p^e`. -/
theorem isUnit_q_zmod (e : ℕ) : IsUnit (F.q : ZMod (F.p ^ e)) :=
  (ZMod.isUnit_iff_coprime F.q (F.p ^ e)).mpr (Nat.Coprime.pow_right e F.coprime.symm)

/-- **GGM Lemma 3.3** (residue-class form): `E_k(a, R)` is exactly one residue class modulo `p^{|a|+1}`,
namely `valuationResidue k a j` (no number in that class is divisible by `p`). -/
theorem valDig_eq_iff_residue (N k : ℕ) (a : Fin k → ℕ) (ha : ∀ i, 1 ≤ a i)
    (j : Fin (k + 1) → ℕ) (hj : ∀ i, 0 < j i ∧ j i < F.p) :
    (N % F.p ≠ 0 ∧ F.valVec N k = a ∧ F.digVec N (k + 1) = j) ↔
      (N : ZMod (F.p ^ (pre a k + 1))) = F.valuationResidue k a j := by
  rw [F.valDig_eq_iff_dvd N k a ha j hj]
  set m := F.p ^ (pre a k + 1)
  have hu : IsUnit ((F.q : ZMod m) ^ (k + 1)) := (F.isUnit_q_zmod _).pow _
  rw [show (F.p : ℤ) ^ (pre a k + 1) = ((F.p ^ (pre a k + 1) : ℕ) : ℤ) by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  unfold valuationResidue
  constructor
  · intro h
    have h' : ((F.q : ZMod m) ^ (k + 1)) * (N : ZMod m)
        = -((F.fint a (fun i => F.r (j i)) : ℤ) : ZMod m) := eq_neg_of_add_eq_zero_left h
    calc (N : ZMod m)
        = ((F.q : ZMod m) ^ (k + 1))⁻¹ * (((F.q : ZMod m) ^ (k + 1)) * (N : ZMod m)) := by
          rw [← mul_assoc, ZMod.inv_mul_of_unit _ hu, one_mul]
      _ = _ := by rw [h']; ring
  · intro h
    rw [h, ← mul_assoc, mul_neg, ZMod.mul_inv_of_unit _ hu]
    ring

/-- **GGM Lemma 3.2**: if `p ∤ N` and `M ≡ N (mod p^{|a⁽ᵏ⁾(N)|+1})`, then `p ∤ M`,
`a⁽ᵏ⁾(M) = a⁽ᵏ⁾(N)` and `R⁽ᵏ⁺¹⁾(M) = R⁽ᵏ⁺¹⁾(N)` (stated with digit sequences). -/
theorem valDig_stable_below {N M k : ℕ} (hN : N % F.p ≠ 0)
    (hmod : M ≡ N [MOD F.p ^ (F.valSum N k + 1)]) :
    M % F.p ≠ 0 ∧ F.valVec M k = F.valVec N k ∧ F.digVec M (k + 1) = F.digVec N (k + 1) := by
  have ha := F.valVec_pos hN k
  have hj := F.digVec_pos_lt hN (k + 1)
  rw [F.valDig_eq_iff_residue M k _ ha _ hj]
  have hNres := (F.valDig_eq_iff_residue N k _ ha _ hj).mp ⟨hN, rfl, rfl⟩
  rw [← hNres]
  rw [F.pre_valVec (le_refl k)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

/-- Lemma 3.2 with a larger modulus (the form of tao-collatz's `valVec_stable_below`). -/
theorem valDig_stable_below' {N M k e : ℕ} (hN : N % F.p ≠ 0)
    (hmod : N % F.p ^ e = M % F.p ^ e) (hL : F.valSum N k < e) :
    M % F.p ≠ 0 ∧ F.valVec M k = F.valVec N k ∧ F.digVec M (k + 1) = F.digVec N (k + 1) := by
  apply F.valDig_stable_below hN
  have hdvd : F.p ^ (F.valSum N k + 1) ∣ F.p ^ e := pow_dvd_pow _ (by omega)
  exact (Nat.ModEq.of_dvd hdvd hmod.symm)

/-! ### Counterpart of tao-collatz's Lemma 2.1 (the observation in GGM §4 Step 2) -/

/-- If `p^{|a|} M = q^n N + fint a (r ∘ j)` holds with its own sequences, then `M = S^n(N)`. -/
theorem eq_syr_iterate_of {N : ℕ} (hN : N % F.p ≠ 0) (n M : ℕ)
    (hM : (F.p : ℤ) ^ pre (F.valVec N n) n * M
      = (F.q : ℤ) ^ n * N + F.fint (F.valVec N n) (F.resVec N n)) :
    M = F.S^[n] N := by
  have hkey := F.syr_iterate_key hN n
  have h : ((M : ℕ) : ℤ) = (F.S^[n] N : ℤ) :=
    mul_left_cancel₀ (pow_ne_zero _ (by exact_mod_cast F.p_ne_zero)) (hM.trans hkey.symm)
  exact_mod_cast h

/-- **Counterpart of tao-collatz's Lemma 2.1**: for `p ∤ N`, `a` with entries ≥ 1 and digits `j` (length `n`),
`(q^n N + fint a (r ∘ j)) / p^{|a|}` is a natural number not divisible by `p` if and only if `a = a⁽ⁿ⁾(N)` and
`j` is the digit sequence of `N` (in that case the value is `S^n(N)`, by `eq_syr_iterate_of`). -/
theorem valVec_unique {N : ℕ} (hN : N % F.p ≠ 0) (n : ℕ) (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i)
    (j : Fin n → ℕ) (hj : ∀ i, 0 < j i ∧ j i < F.p) :
    (∃ M : ℕ, M % F.p ≠ 0 ∧
        (F.p : ℤ) ^ pre a n * M = (F.q : ℤ) ^ n * N + F.fint a (fun i => F.r (j i)))
      ↔ (a = F.valVec N n ∧ j = F.digVec N n) := by
  constructor
  · rintro ⟨M, hM, hEq⟩
    cases n with
    | zero => exact ⟨funext (fun i => i.elim0), funext (fun i => i.elim0)⟩
    | succ k =>
      have hinit : ∀ i, 1 ≤ Fin.init a i := fun i => ha _
      have hf : F.fint a (fun i => F.r (j i)) = F.fint (Fin.init a) (fun i => F.r (j i)) := by
        apply F.fint_congr_pre
        intro m hm
        rw [pre_init a (by omega)]
      have hsplit : pre a (k + 1) = pre (Fin.init a) k + a (Fin.last k) := pre_succ_init a
      have hlast : 1 ≤ a (Fin.last k) := ha _
      have hdvd : (F.p : ℤ) ^ (pre (Fin.init a) k + 1)
          ∣ (F.q : ℤ) ^ (k + 1) * N + F.fint (Fin.init a) (fun i => F.r (j i)) := by
        rw [← hf, ← hEq, hsplit]
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlast
        rw [hd]
        exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
      obtain ⟨_, hva, hdj⟩ := F.valDig_of_dvd k N (Fin.init a) j hinit hj hdvd
      -- The last valuation
      have hkey := F.syr_iterate_key hN (k + 1)
      have hf2 : F.fint (F.valVec N (k + 1)) (F.resVec N (k + 1))
          = F.fint a (fun i => F.r (j i)) := by
        rw [hf]
        have hres : F.resVec N (k + 1) = fun i => F.r (j i) := by
          funext i; simp only [resVec, hdj]
        rw [hres]
        apply F.fint_congr_pre
        intro m hm
        rw [F.pre_valVec (by omega), ← F.pre_valVec (n := k) (by omega), hva]
      rw [hf2, ← hEq, F.valVec_snoc, pre_succ_init, Fin.init_snoc, Fin.snoc_last, hva,
        hsplit, pow_add, pow_add, mul_assoc, mul_assoc] at hkey
      have hp0 : (F.p : ℤ) ^ pre (Fin.init a) k ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast F.p_ne_zero)
      have hk2 := mul_left_cancel₀ hp0 hkey
      have hS : ¬ (F.p : ℤ) ∣ (F.S^[k + 1] N : ℤ) := by
        intro hd
        exact F.syr_iterate_mod_ne_zero hN (k + 1)
          (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp hd))
      have hMd : ¬ (F.p : ℤ) ∣ (M : ℤ) := by
        intro hd
        exact hM (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp hd))
      obtain ⟨hνa, _⟩ := pow_mul_eq_pow_mul (by exact_mod_cast F.p_ne_zero) hS hMd hk2
      refine ⟨?_, hdj.symm⟩
      rw [F.valVec_snoc, hva, hνa, Fin.snoc_init_self]
  · rintro ⟨rfl, rfl⟩
    refine ⟨F.S^[n] N, F.syr_iterate_mod_ne_zero hN n, ?_⟩
    exact F.syr_iterate_key hN n

/-- **The observation in GGM §4 Step 2 (constructive direction)**: for `a` with entries ≥ 1, digits `j` (length `k`) and `p ∤ M`,
if `q^k N = p^{|a|} M - fint a (r ∘ j)`, then `p ∤ N`, `a⁽ᵏ⁾(N) = a`, the digit sequence is `j`, and `S^k(N) = M`. -/
theorem valVec_of_eq (k : ℕ) (a : Fin k → ℕ) (ha : ∀ i, 1 ≤ a i)
    (j : Fin k → ℕ) (hj : ∀ i, 0 < j i ∧ j i < F.p) {M N : ℕ} (hM : M % F.p ≠ 0)
    (hN : (F.q : ℤ) ^ k * N = (F.p : ℤ) ^ pre a k * M - F.fint a (fun i => F.r (j i))) :
    N % F.p ≠ 0 ∧ F.valVec N k = a ∧ F.digVec N k = j ∧ F.S^[k] N = M := by
  have hNp : N % F.p ≠ 0 := by
    cases k with
    | zero =>
      have hf : F.fint a (fun i => F.r (j i)) = 0 := by simp [fint]
      rw [hf] at hN
      simp only [pow_zero, pre_zero, one_mul, sub_zero] at hN
      have : N = M := by exact_mod_cast hN
      rw [this]; exact hM
    | succ k' =>
      intro hN0
      have hpN : (F.p : ℤ) ∣ (F.q : ℤ) ^ (k' + 1) * N :=
        Dvd.dvd.mul_left (by exact_mod_cast Nat.dvd_of_mod_eq_zero hN0) _
      have hpre : 1 ≤ pre a (k' + 1) := le_trans (by omega) (le_pre_of_pos a ha (le_refl _))
      have hpM : (F.p : ℤ) ∣ (F.p : ℤ) ^ pre a (k' + 1) * M :=
        Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
      have hpf : (F.p : ℤ) ∣ F.fint a (fun i => F.r (j i)) := by
        have := dvd_sub hpM hpN
        rw [hN] at this
        simpa using this
      exact F.fint_not_dvd a ha (fun i => F.r (j i)) (by omega)
        (F.r_not_dvd (hj 0).1 (hj 0).2) hpf
  have hEq : (F.p : ℤ) ^ pre a k * M = (F.q : ℤ) ^ k * N + F.fint a (fun i => F.r (j i)) := by
    rw [hN]; ring
  obtain ⟨hav, hjv⟩ := (F.valVec_unique hNp k a ha j hj).mp ⟨M, hM, hEq⟩
  refine ⟨hNp, hav.symm, hjv.symm, ?_⟩
  symm
  apply F.eq_syr_iterate_of hNp k M
  have hres : F.resVec N k = fun i => F.r (j i) := by
    funext i; simp only [resVec, hjv]
  rw [hres, ← hav]
  exact hEq

end Family

end GGMCollatz
