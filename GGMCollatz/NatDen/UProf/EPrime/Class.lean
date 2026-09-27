import GGMCollatz.NatDen.UProf.Statements

/-!
# Prefix classes of `E'` (Lemma 7.13 (i) of the paper)

Let `m = m₀ = F.mZero α x` and `E' = F.Eprime α x Set.univ`. The **key** of `M ∈ ℕ_p` is
`key m M = (a^{(m)}(M), dig^{(m+1)}(M))` (the valuation vector and the digit vector).

* `modEq_of_key_eq`, `key_eq_of_modEq`: equality of keys is the same as congruence mod `p^{|a|+1}`
  (GGM Lemmas 3.3, 3.2; `valDig_eq_iff_residue`, `valDig_stable_below`).
* `iterate_le_of_key_eq`: between two numbers with equal keys, `S^i` (`i ≤ m`) is monotone (by the iteration formula `syr_iterate_key`,
  `p^{|a|} S^i(M) = q^i M + (a correction determined by the key alone)`).
* `convex`: a class of `E'` with a given key is "convex" within its residue class (the numbers of the same class between two elements
  also lie in `E'` and have the same key). This is the Lean form of "the intersection of a class with an interval".
* Size bounds (under `Good`): `x p^{a_{[1,m-1]}} ≤ 2 q^{m-1} M` (from `S^{m-1}(M) > x`),
  `q^{m-1} M ≤ 2x p^{|a|}` (from `S^m(M) ≤ x`), `p^{a_{[1,m-1]}} ≤ W`, and each valuation is `≤ Bmax`.
-/

namespace GGMCollatz

namespace ND

namespace EPrimeAux

open Family

variable (F : Family)

/-- The prefix key `(a^{(m)}(M), dig^{(m+1)}(M))`. -/
def key (m M : ℕ) : (Fin m → ℕ) × (Fin (m + 1) → ℕ) := (F.valVec M m, F.digVec M (m + 1))

/-- `R = Σ_{j<p} |r(j)|` (a real number; `|r(j)| ≤ R`). -/
noncomputable def Rb : ℝ := (F.rBound : ℝ)

/-- The upper bound `W = 2 q^{m-1} Mhi / x` for the valuation sum of length `m-1` (`p^{a_{[1,m-1]}} ≤ W`). -/
noncomputable def Wb (α x : ℝ) : ℝ := 2 * (F.q : ℝ) ^ (F.mZero α x - 1) * F.Mhi α x / x

/-- The upper bound for each valuation, `Bmax = ⌊log(q^m (Mhi + 2R)) / log p⌋`. -/
noncomputable def Bmax (α x : ℝ) : ℕ :=
  ⌊Real.log ((F.q : ℝ) ^ F.mZero α x * (F.Mhi α x + 2 * Rb F)) / Real.log F.p⌋₊

/-- The bundle of conditions that hold when `x` is large enough (shown in `eventually_good`). -/
structure Good (α x : ℝ) : Prop where
  one_le_x : 1 ≤ x
  one_le_m : 1 ≤ F.mZero α x
  qR : (F.q : ℝ) ^ F.mZero α x * Rb F ≤ x / 2
  count : Wb F α x * ((F.p : ℝ) - 1) ^ 2 * (Bmax F α x : ℝ) ≤ x ^ (1 / 2 : ℝ)
  small : x ^ (1 / 2 : ℝ) * x ^ (1 / 5 : ℝ) ≤ F.Mlo α x

theorem Rb_nonneg : 0 ≤ Rb F := by
  unfold Rb; exact_mod_cast F.rBound_nonneg

/-! ### The membership condition of `E'` -/

/-- The membership condition of `E'(ℕ)`, unfolded. -/
theorem mem_Eprime_univ {α x : ℝ} {M : ℕ} :
    M ∈ F.Eprime α x Set.univ ↔ M % F.p ≠ 0 ∧ F.Mlo α x ≤ M ∧ M ≤ ⌊F.Mhi α x⌋₊ ∧
      F.S^[F.mZero α x] M ≤ ⌊x⌋₊ ∧ ∀ j < F.mZero α x, ⌊x⌋₊ < F.S^[j] M := by
  unfold Family.Eprime
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_univ, and_true]
  constructor
  · rintro ⟨hlt, hp, hlo, hpass, htime⟩
    refine ⟨hp, hlo, by omega, ?_, ?_⟩
    · rw [← htime]; exact F.passTime_spec hpass
    · intro j hj; rw [← htime] at hj; exact F.lt_of_lt_passTime hj
  · rintro ⟨hp, hlo, hle, hS, hlt⟩
    exact ⟨by omega, hp, hlo, F.passes_of_le hS, F.passTime_eq_of hS hlt⟩

/-! ### Keys and residue classes -/

/-- Two numbers with equal keys are congruent mod `p^{|a|+1}` (GGM Lemma 3.3). -/
theorem modEq_of_key_eq {m M M' : ℕ} (hM : M % F.p ≠ 0) (hM' : M' % F.p ≠ 0)
    (h : key F m M = key F m M') : M ≡ M' [MOD F.p ^ (pre (key F m M).1 m + 1)] := by
  have hv : F.valVec M m = F.valVec M' m := congrArg Prod.fst h
  have hd : F.digVec M (m + 1) = F.digVec M' (m + 1) := congrArg Prod.snd h
  have ha := F.valVec_pos hM m
  have hj := F.digVec_pos_lt hM (m + 1)
  have e1 := (F.valDig_eq_iff_residue M m _ ha _ hj).mp ⟨hM, rfl, rfl⟩
  have e2 := (F.valDig_eq_iff_residue M' m _ ha _ hj).mp ⟨hM', hv.symm, hd.symm⟩
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (e1.trans e2.symm)

/-- Congruence mod `p^{|a|+1}` implies equal keys (GGM Lemma 3.2). -/
theorem key_eq_of_modEq {m M M' : ℕ} (hM : M % F.p ≠ 0)
    (h : M' ≡ M [MOD F.p ^ (pre (key F m M).1 m + 1)]) :
    M' % F.p ≠ 0 ∧ key F m M' = key F m M := by
  have h' : M' ≡ M [MOD F.p ^ (F.valSum M m + 1)] := by
    have e : pre (key F m M).1 m = F.valSum M m := F.pre_valVec le_rfl
    rw [e] at h; exact h
  obtain ⟨h1, h2, h3⟩ := F.valDig_stable_below hM h'
  refine ⟨h1, ?_⟩
  simp only [key, h2, h3]

/-- Between two numbers with equal keys, `S^i` (`i ≤ m`) is monotone. -/
theorem iterate_le_of_key_eq {m M M' : ℕ} (hM : M % F.p ≠ 0) (hM' : M' % F.p ≠ 0)
    (h : key F m M = key F m M') (hle : M ≤ M') {i : ℕ} (hi : i ≤ m) :
    F.S^[i] M ≤ F.S^[i] M' := by
  have hv : F.valVec M m = F.valVec M' m := congrArg Prod.fst h
  have hd : F.digVec M (m + 1) = F.digVec M' (m + 1) := congrArg Prod.snd h
  have hvi : F.valVec M i = F.valVec M' i := by
    funext j
    exact congrFun hv ⟨j, lt_of_lt_of_le j.isLt hi⟩
  have hri : F.resVec M i = F.resVec M' i := by
    funext j
    have := congrFun hd ⟨j, by omega⟩
    simp only [Family.resVec]
    exact congrArg F.r this
  have k1 := F.syr_iterate_key hM i
  have k2 := F.syr_iterate_key hM' i
  rw [hvi, hri] at k1
  have hA : (0 : ℤ) < (F.p : ℤ) ^ pre (F.valVec M' i) i := by
    have : (0 : ℤ) < F.p := by exact_mod_cast F.p_pos
    positivity
  have heq : (F.p : ℤ) ^ pre (F.valVec M' i) i * ((F.S^[i] M' : ℤ) - (F.S^[i] M : ℤ))
      = (F.q : ℤ) ^ i * ((M' : ℤ) - M) := by
    rw [mul_sub, k1, k2]; ring
  have hMM : (0 : ℤ) ≤ (M' : ℤ) - M := by
    have : (M : ℤ) ≤ M' := by exact_mod_cast hle
    linarith
  have hprod : 0 ≤ (F.p : ℤ) ^ pre (F.valVec M' i) i * ((F.S^[i] M' : ℤ) - (F.S^[i] M : ℤ)) := by
    rw [heq]; positivity
  have hdiff : (0 : ℤ) ≤ (F.S^[i] M' : ℤ) - (F.S^[i] M : ℤ) :=
    (mul_nonneg_iff_of_pos_left hA).mp hprod
  have : (F.S^[i] M : ℤ) ≤ F.S^[i] M' := by linarith
  exact_mod_cast this

/-- **Convexity**: the numbers of the same residue class between two elements with the same key lie in `E'` and have the same key. -/
theorem convex {α x : ℝ} {M₁ M₂ M : ℕ} (h₁ : M₁ ∈ F.Eprime α x Set.univ)
    (h₂ : M₂ ∈ F.Eprime α x Set.univ)
    (hk : key F (F.mZero α x) M₁ = key F (F.mZero α x) M₂) (hle₁ : M₁ ≤ M) (hle₂ : M ≤ M₂)
    (hmod : M ≡ M₁ [MOD F.p ^ (pre (key F (F.mZero α x) M₁).1 (F.mZero α x) + 1)]) :
    M ∈ F.Eprime α x Set.univ ∧ key F (F.mZero α x) M = key F (F.mZero α x) M₁ := by
  rw [mem_Eprime_univ] at h₁ h₂
  obtain ⟨hp₁, hlo₁, -, -, hlt₁⟩ := h₁
  obtain ⟨hp₂, -, hhi₂, hS₂, -⟩ := h₂
  obtain ⟨hp, hkey⟩ := key_eq_of_modEq F hp₁ hmod
  refine ⟨?_, hkey⟩
  rw [mem_Eprime_univ]
  refine ⟨hp, le_trans hlo₁ (by exact_mod_cast hle₁), le_trans hle₂ hhi₂, ?_, ?_⟩
  · exact le_trans (iterate_le_of_key_eq F hp hp₂ (hkey.trans hk) hle₂ le_rfl) hS₂
  · intro j hj
    exact lt_of_lt_of_le (hlt₁ j hj) (iterate_le_of_key_eq F hp₁ hp hkey.symm hle₁ hj.le)

/-! ### Size bounds -/

/-- Split the partial sum at the last valuation: `|a| = a_{[1,m-1]} + a_m`. -/
theorem pre_last {m : ℕ} (hm : 1 ≤ m) (a : Fin m → ℕ) :
    pre a m = pre a (m - 1) + a ⟨m - 1, by omega⟩ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [pre_succ, dif_pos (by omega : m' < m' + 1)]
  rfl

/-- Two-sided bound: `|p^{a_{[1,n]}} S^n(N) - q^n N| ≤ p^{a_{[1,n]}} q^n R` (the iteration formula and `|fint| ≤ p^{|a|} q^n R`). -/
theorem abs_pow_val_mul_sub_le {N : ℕ} (hN : N % F.p ≠ 0) (n : ℕ) :
    |(F.p : ℝ) ^ F.valSum N n * (F.S^[n] N : ℝ) - (F.q : ℝ) ^ n * N|
      ≤ (F.p : ℝ) ^ F.valSum N n * (F.q : ℝ) ^ n * Rb F := by
  have hkey := F.syr_iterate_key hN n
  rw [F.pre_valVec le_rfl] at hkey
  have hb := F.abs_fint_le (F.valVec N n) (F.resVec N n) F.rBound_nonneg
    (fun m => F.abs_r_le_rBound (F.digVec_pos_lt hN n m).2)
  rw [F.pre_valVec le_rfl] at hb
  have hd : (F.p : ℤ) ^ F.valSum N n * (F.S^[n] N : ℤ) - (F.q : ℤ) ^ n * N
      = F.fint (F.valVec N n) (F.resVec N n) := by rw [hkey]; ring
  have hZ : |(F.p : ℤ) ^ F.valSum N n * (F.S^[n] N : ℤ) - (F.q : ℤ) ^ n * N|
      ≤ (F.p : ℤ) ^ F.valSum N n * (F.q : ℤ) ^ n * F.rBound := by rw [hd]; exact hb
  have hR := (Int.cast_le (R := ℝ)).mpr hZ
  push_cast at hR
  unfold Rb
  exact hR

/-- The basic bounds for elements of `E'` under `Good`: `x < S^{m-1}(M)`, `S^m(M) ≤ x`, `Mlo ≤ M ≤ Mhi`. -/
theorem basic_of_mem {α x : ℝ} (hG : Good F α x) {M : ℕ} (hM : M ∈ F.Eprime α x Set.univ) :
    M % F.p ≠ 0 ∧ x < (F.S^[F.mZero α x - 1] M : ℝ) ∧ (F.S^[F.mZero α x] M : ℝ) ≤ x ∧
      (M : ℝ) ≤ F.Mhi α x ∧ F.Mlo α x ≤ M := by
  rw [mem_Eprime_univ] at hM
  obtain ⟨hp, hlo, hhi, hS, hlt⟩ := hM
  have hx0 : 0 ≤ x := by linarith [hG.one_le_x]
  have hm := hG.one_le_m
  refine ⟨hp, ?_, ?_, ?_, hlo⟩
  · have h1 := hlt (F.mZero α x - 1) (by omega)
    have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (F.S^[F.mZero α x - 1] M : ℝ) := by exact_mod_cast h1
    have h3 := Nat.lt_floor_add_one x
    push_cast at h2
    linarith
  · have h1 : (F.S^[F.mZero α x] M : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hS
    exact le_trans h1 (Nat.floor_le hx0)
  · have h1 : (M : ℝ) ≤ (⌊F.Mhi α x⌋₊ : ℝ) := by exact_mod_cast hhi
    exact le_trans h1 (Nat.floor_le (Real.exp_pos _).le)

/-- Under `Good`, `q^{m-1} R ≤ x/2`. -/
theorem qR_pred {α x : ℝ} (hG : Good F α x) : (F.q : ℝ) ^ (F.mZero α x - 1) * Rb F ≤ x / 2 := by
  have hq1 : (1 : ℝ) ≤ F.q := by exact_mod_cast F.q_pos
  have h1 : (F.q : ℝ) ^ (F.mZero α x - 1) ≤ (F.q : ℝ) ^ F.mZero α x :=
    pow_le_pow_right₀ hq1 (Nat.sub_le _ _)
  exact le_trans (mul_le_mul_of_nonneg_right h1 (Rb_nonneg F)) hG.qR

/-- **Lower end**: `x p^{a_{[1,m-1]}} ≤ 2 q^{m-1} M` (from `S^{m-1}(M) > x`). -/
theorem lower_bound {α x : ℝ} (hG : Good F α x) {M : ℕ} (hM : M ∈ F.Eprime α x Set.univ) :
    x * (F.p : ℝ) ^ pre (key F (F.mZero α x) M).1 (F.mZero α x - 1)
      ≤ 2 * (F.q : ℝ) ^ (F.mZero α x - 1) * M := by
  obtain ⟨hp, hS1, -, -, -⟩ := basic_of_mem F hG hM
  have e : pre (key F (F.mZero α x) M).1 (F.mZero α x - 1) = F.valSum M (F.mZero α x - 1) :=
    F.pre_valVec (Nat.sub_le _ _)
  rw [e]
  set n := F.mZero α x - 1
  have hab := abs_pow_val_mul_sub_le F hp n
  have hup := (abs_le.mp hab).2
  have hP : (0 : ℝ) ≤ (F.p : ℝ) ^ F.valSum M n := by positivity
  have hqR := qR_pred F hG
  have h1 : x * (F.p : ℝ) ^ F.valSum M n ≤ (F.p : ℝ) ^ F.valSum M n * (F.S^[n] M : ℝ) := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hS1.le hP
  have h2 : (F.p : ℝ) ^ F.valSum M n * ((F.q : ℝ) ^ n * Rb F)
      ≤ (F.p : ℝ) ^ F.valSum M n * (x / 2) :=
    mul_le_mul_of_nonneg_left hqR hP
  nlinarith

/-- **Upper end**: `q^{m-1} M ≤ 2x p^{|a|}` (from `S^m(M) ≤ x`). -/
theorem upper_bound {α x : ℝ} (hG : Good F α x) {M : ℕ} (hM : M ∈ F.Eprime α x Set.univ) :
    (F.q : ℝ) ^ (F.mZero α x - 1) * M
      ≤ 2 * x * (F.p : ℝ) ^ pre (key F (F.mZero α x) M).1 (F.mZero α x) := by
  obtain ⟨hp, -, hSm, -, -⟩ := basic_of_mem F hG hM
  have e : pre (key F (F.mZero α x) M).1 (F.mZero α x) = F.valSum M (F.mZero α x) :=
    F.pre_valVec le_rfl
  rw [e]
  have hqR := hG.qR
  set m := F.mZero α x
  have hab := abs_pow_val_mul_sub_le F hp m
  have hlow := (abs_le.mp hab).1
  have hP : (0 : ℝ) ≤ (F.p : ℝ) ^ F.valSum M m := by positivity
  have hq1 : (1 : ℝ) ≤ F.q := by exact_mod_cast F.q_pos
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h1 : (F.q : ℝ) ^ (m - 1) * M ≤ (F.q : ℝ) ^ m * M :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq1 (Nat.sub_le _ _)) hM0
  have h2 : (F.p : ℝ) ^ F.valSum M m * (F.S^[m] M : ℝ) ≤ (F.p : ℝ) ^ F.valSum M m * x :=
    mul_le_mul_of_nonneg_left hSm hP
  have h3 : (F.p : ℝ) ^ F.valSum M m * ((F.q : ℝ) ^ m * Rb F)
      ≤ (F.p : ℝ) ^ F.valSum M m * (x / 2) :=
    mul_le_mul_of_nonneg_left hqR hP
  nlinarith

/-- `p^{a_{[1,m-1]}} ≤ W`. -/
theorem pow_pre_le_W {α x : ℝ} (hG : Good F α x) {M : ℕ} (hM : M ∈ F.Eprime α x Set.univ) :
    (F.p : ℝ) ^ pre (key F (F.mZero α x) M).1 (F.mZero α x - 1) ≤ Wb F α x := by
  obtain ⟨-, -, -, hMhi, -⟩ := basic_of_mem F hG hM
  have hlow := lower_bound F hG hM
  have hx0 : 0 < x := by linarith [hG.one_le_x]
  unfold Wb
  rw [le_div_iff₀ hx0]
  have hq0 : (0 : ℝ) ≤ 2 * (F.q : ℝ) ^ (F.mZero α x - 1) := by positivity
  have := mul_le_mul_of_nonneg_left hMhi hq0
  nlinarith

/-- The ranges of the key's components: valuations in `[1, Bmax]`, digits in `(0, p)`. -/
theorem key_bounds {α x : ℝ} (hG : Good F α x) {M : ℕ} (hM : M ∈ F.Eprime α x Set.univ) :
    (∀ i, 1 ≤ (key F (F.mZero α x) M).1 i ∧ (key F (F.mZero α x) M).1 i ≤ Bmax F α x) ∧
      (∀ i, 0 < (key F (F.mZero α x) M).2 i ∧ (key F (F.mZero α x) M).2 i < F.p) := by
  obtain ⟨hp, -, -, hMhi, -⟩ := basic_of_mem F hG hM
  refine ⟨?_, fun i => F.digVec_pos_lt hp _ i⟩
  intro i
  refine ⟨F.valVec_pos hp _ i, ?_⟩
  set N := F.S^[(i : ℕ)] M with hNdef
  have hN : N % F.p ≠ 0 := F.syr_iterate_mod_ne_zero hp i
  show padicValNat F.p (F.lift N) ≤ Bmax F α x
  set ν := padicValNat F.p (F.lift N)
  have hR0 := Rb_nonneg F
  have hq1 : (1 : ℝ) ≤ F.q := by exact_mod_cast F.q_pos
  have hp1 : (1 : ℝ) ≤ F.p := by exact_mod_cast F.p_pos
  -- `p^ν ≤ qN + R`
  have hstep := F.pow_val_mul_syr_int hN
  have hSN : (1 : ℤ) ≤ (F.S N : ℤ) := by exact_mod_cast F.syr_pos hN
  have hrle : F.r (N % F.p) ≤ F.rBound :=
    le_trans (le_abs_self _) (F.abs_r_le_rBound (Nat.mod_lt _ F.p_pos))
  have hpνZ : (F.p : ℤ) ^ ν ≤ (F.q : ℤ) * N + F.rBound := by
    have hP : (0 : ℤ) ≤ (F.p : ℤ) ^ ν := by positivity
    nlinarith
  have hpν : (F.p : ℝ) ^ ν ≤ (F.q : ℝ) * N + Rb F := by
    have := (Int.cast_le (R := ℝ)).mpr hpνZ
    push_cast at this
    unfold Rb; exact this
  -- `N ≤ q^i (M + R)`
  have hNle : (N : ℝ) ≤ (F.q : ℝ) ^ (i : ℕ) * (M + Rb F) := by
    have hab := abs_pow_val_mul_sub_le F hp i
    have hup := (abs_le.mp hab).2
    have hP1 : (1 : ℝ) ≤ (F.p : ℝ) ^ F.valSum M i := one_le_pow₀ hp1
    have hqi : (0 : ℝ) ≤ (F.q : ℝ) ^ (i : ℕ) := by positivity
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have h1 : (F.p : ℝ) ^ F.valSum M i * (N : ℝ)
        ≤ (F.p : ℝ) ^ F.valSum M i * ((F.q : ℝ) ^ (i : ℕ) * (M + Rb F)) := by
      have : (F.q : ℝ) ^ (i : ℕ) * M ≤ (F.p : ℝ) ^ F.valSum M i * ((F.q : ℝ) ^ (i : ℕ) * M) := by
        nlinarith [mul_nonneg hqi hM0]
      nlinarith
    exact le_of_mul_le_mul_left h1 (by linarith)
  -- `p^ν ≤ V = q^m (Mhi + 2R)`
  have hi : (i : ℕ) + 1 ≤ F.mZero α x := i.isLt
  have hV : (F.p : ℝ) ^ ν ≤ (F.q : ℝ) ^ F.mZero α x * (F.Mhi α x + 2 * Rb F) := by
    have hqm : (F.q : ℝ) ^ ((i : ℕ) + 1) ≤ (F.q : ℝ) ^ F.mZero α x := pow_le_pow_right₀ hq1 hi
    have hqm1 : (1 : ℝ) ≤ (F.q : ℝ) ^ F.mZero α x := one_le_pow₀ hq1
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have e1 : (F.q : ℝ) * N ≤ (F.q : ℝ) ^ ((i : ℕ) + 1) * (M + Rb F) := by
      rw [pow_succ]
      have := mul_le_mul_of_nonneg_left hNle (by linarith : (0 : ℝ) ≤ F.q)
      nlinarith
    have e2 : (F.q : ℝ) ^ ((i : ℕ) + 1) * (M + Rb F) ≤ (F.q : ℝ) ^ F.mZero α x * (M + Rb F) :=
      mul_le_mul_of_nonneg_right hqm (by linarith)
    have e3 : (F.q : ℝ) ^ F.mZero α x * (M + Rb F) + Rb F ≤ (F.q : ℝ) ^ F.mZero α x * (F.Mhi α x + 2 * Rb F) := by
      nlinarith
    linarith
  -- take logarithms
  have hpos : (0 : ℝ) < (F.p : ℝ) ^ ν := by positivity
  have hlog : (ν : ℝ) * Real.log F.p ≤ Real.log ((F.q : ℝ) ^ F.mZero α x * (F.Mhi α x + 2 * Rb F)) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hpos hV
  have hν : (ν : ℝ) ≤ Real.log ((F.q : ℝ) ^ F.mZero α x * (F.Mhi α x + 2 * Rb F)) / Real.log F.p := by
    rw [le_div_iff₀ F.log_p_pos]; exact hlog
  exact Nat.le_floor hν

end EPrimeAux

end ND

end GGMCollatz
