import GGMCollatz.Tao.Sec5.Drift

/-!
# Parts for recounting via preimages (Lemma 7.9 of the paper, Tao's Lemma 2.1, tao-collatz's `approxMainTerm_eq_steppedMid`)

Derived from `TaoCollatz/Sec5/ApproxFormula.lean` (`approxMainTerm_eq_steppedMid`, `aff_valVec_eq_syr`)
and `TaoCollatz/Sec5/Stabilization.lean` (`perNTerm_pointmass`, `solvable_iff_fmapZ`) of
gotrevor/tao-collatz (Apache-2.0), commit 15efca2; generalized to the GGM family (p, q, r).

* `vecOf N k`: the sequence of (valuation, digit) pairs `v_i = (a_i(N), S^i(N) mod p)`.
* `stepLaw_iid_toReal_of_valid`: the model probability of a valid tuple is `p^{-|a|}` (the `(p-1)^n` of
  `G(μ)` and the `(p-1)^{-n}` of the uniform distribution of the digits cancel; see the accompanying
  paper).
* `offsetFwd_vecOf`: `F_k(a(N), R(N)) ≡ S^k(N) (mod q^k)`.
* `exists_preimage`: if `M ≡ F_k(a, R) (mod q^k)` then `N = p^{|a|}(M - F_k)/q^k` is a preimage
  (Lemma 7.9 of the paper).
* `vecOf_injective`: `N` is determined by the tuple and `S^k(N)`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- The sequence of (valuation, digit) pairs. -/
def vecOf (N k : ℕ) : Fin k → ℕ × ℕ := fun i => (F.valVec N k i, F.digVec N k i)

/-- Valid tuples: valuations ≥ 1, digits ∈ `(0, p)`. -/
def validVec {k : ℕ} (v : Fin k → ℕ × ℕ) : Prop :=
  ∀ i, 1 ≤ (v i).1 ∧ 0 < (v i).2 ∧ (v i).2 < F.p

theorem vecOf_valid {N : ℕ} (hN : N % F.p ≠ 0) (k : ℕ) : F.validVec (F.vecOf N k) := fun i =>
  ⟨F.valVec_pos hN k i, (F.digVec_pos_lt hN k i).1, (F.digVec_pos_lt hN k i).2⟩

/-- The model probability (as a real) of a valid tuple is `p^{-|a|}`. -/
theorem stepLaw_iid_toReal_of_valid {k : ℕ} {v : Fin k → ℕ × ℕ} (hv : F.validVec v) :
    ((PMF.iid (stepLaw F.p) k) v).toReal = ((F.p : ℝ) ^ pre (fun i => (v i).1) k)⁻¹ := by
  rw [iid_stepLaw_apply, ENNReal.toReal_prod]
  have hp2 := F.two_le_p
  have hp1 : (F.p : ℝ) - 1 ≠ 0 := by have := F.one_lt_p_real; linarith
  have hfac : ∀ i, (geomP F.p (v i).1 * unifDigit F.p (v i).2).toReal
      = ((F.p : ℝ) ^ (v i).1)⁻¹ := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hv i
    rw [ENNReal.toReal_mul, geomP_toReal hp2, if_neg (by omega), unifDigit_apply hp2,
      if_pos ⟨h2, h3⟩, ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_sub (by omega)]
    push_cast
    rw [inv_pow]
    field_simp
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_inv_distrib,
    Finset.prod_pow_eq_pow_sum, pre_eq_fin_sum]

/-- A tuple with nonzero model probability is valid. -/
theorem validVec_of_ne_zero {k : ℕ} {v : Fin k → ℕ × ℕ} (hv : (PMF.iid (stepLaw F.p) k) v ≠ 0) :
    F.validVec v := by
  rw [iid_stepLaw_apply, Finset.prod_ne_zero_iff] at hv
  intro i
  have h := hv i (Finset.mem_univ i)
  rw [mul_ne_zero_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [geomP_apply F.two_le_p] at h1
  rw [unifDigit_apply F.two_le_p] at h2
  refine ⟨?_, ?_⟩
  · by_contra h0
    exact h1 (if_pos (by omega))
  · by_contra h0
    exact h2 (if_neg h0)

/-- The forward offset is `S^k(N) mod q^k` (reading the iteration formula modulo `q^k`). -/
theorem offsetFwd_vecOf {N : ℕ} (hN : N % F.p ≠ 0) (k : ℕ) :
    F.offsetFwd (F.vecOf N k) = ((F.S^[k] N : ℕ) : ZMod (F.q ^ k)) := by
  have hkey := F.syr_iterate_key hN k
  have hZ := congrArg (Int.cast : ℤ → ZMod (F.q ^ k)) hkey
  push_cast at hZ
  rw [show ((F.q : ZMod (F.q ^ k))) ^ k = ((F.q ^ k : ℕ) : ZMod (F.q ^ k)) by push_cast; rfl,
    ZMod.natCast_self, zero_mul, zero_add] at hZ
  unfold offsetFwd vecOf
  simp only
  have hres : (fun i => F.r (F.digVec N k i)) = F.resVec N k := rfl
  have hval : (fun i : Fin k => F.valVec N k i) = F.valVec N k := rfl
  rw [hres, hval, ← hZ, mul_comm, ← mul_assoc, ← mul_pow, F.inv_mul_p_zmod, one_pow, one_mul]

/-- **Lemma 7.9 of the paper**: for a valid tuple `v` and `M ≡ F_k(v) (mod q^k)` (`p ∤ M`, `F_k < p^{|a|} M`),
`N = (p^{|a|} M - fint)/q^k` satisfies `p ∤ N`, `vecOf N k = v`, `S^k(N) = M`. -/
theorem exists_preimage {k : ℕ} {v : Fin k → ℕ × ℕ} (hv : F.validVec v) {M : ℕ}
    (hM : M % F.p ≠ 0) (hMc : ((M : ℕ) : ZMod (F.q ^ k)) = F.offsetFwd v)
    (hpos : F.fint (fun i => (v i).1) (fun i => F.r (v i).2)
      < (F.p : ℤ) ^ pre (fun i => (v i).1) k * M) :
    ∃ N : ℕ, N % F.p ≠ 0 ∧ F.vecOf N k = v ∧ F.S^[k] N = M ∧
      (F.q : ℤ) ^ k * N = (F.p : ℤ) ^ pre (fun i => (v i).1) k * M
        - F.fint (fun i => (v i).1) (fun i => F.r (v i).2) := by
  set a : Fin k → ℕ := fun i => (v i).1 with ha
  set j : Fin k → ℕ := fun i => (v i).2 with hj
  set f := F.fint a (fun i => F.r (j i)) with hf
  set A := pre a k with hA
  set Zi : ℤ := (F.p : ℤ) ^ A * M - f with hZi
  have hZpos : 0 < Zi := by rw [hZi]; linarith
  -- `q^k ∣ Z`
  have hZmod : ((Zi : ℤ) : ZMod (F.q ^ k)) = 0 := by
    rw [hZi]; push_cast
    rw [hMc]; unfold offsetFwd
    rw [← hf, ← hA]
    rw [show (F.p : ZMod (F.q ^ k)) ^ A * ((f : ZMod (F.q ^ k)) * ((F.p : ZMod (F.q ^ k))⁻¹) ^ A)
        = ((F.p : ZMod (F.q ^ k)) * (F.p : ZMod (F.q ^ k))⁻¹) ^ A * (f : ZMod (F.q ^ k)) by ring,
      F.p_mul_inv_zmod, one_pow, one_mul, sub_self]
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd Zi (F.q ^ k)).mp hZmod
  obtain ⟨w, hw⟩ := hdvd
  have hqk : (0 : ℤ) < ((F.q ^ k : ℕ) : ℤ) := by exact_mod_cast pow_pos F.q_pos k
  have hw0 : 0 < w := by
    by_contra h0
    push_neg at h0
    have : Zi ≤ 0 := by rw [hw]; exact mul_nonpos_of_nonneg_of_nonpos hqk.le h0
    linarith
  refine ?_
  set N := w.toNat with hN
  have hNw : (N : ℤ) = w := Int.toNat_of_nonneg hw0.le
  have hqN : (F.q : ℤ) ^ k * N = (F.p : ℤ) ^ A * M - f := by
    rw [hNw, ← hZi, hw]; push_cast; ring
  have hj' : ∀ i, 0 < j i ∧ j i < F.p := fun i => ⟨(hv i).2.1, (hv i).2.2⟩
  obtain ⟨hNp, hval, hdig, hS⟩ := F.valVec_of_eq k a (fun i => (hv i).1) j hj' hM hqN
  refine ⟨N, hNp, ?_, hS, hqN⟩
  funext i
  unfold vecOf
  rw [hval, hdig]

/-- `N` is determined by the tuple and `S^k(N)`. -/
theorem vecOf_injective {N N' k : ℕ} (hN : N % F.p ≠ 0) (hN' : N' % F.p ≠ 0)
    (hv : F.vecOf N k = F.vecOf N' k) (hS : F.S^[k] N = F.S^[k] N') : N = N' := by
  have hval : F.valVec N k = F.valVec N' k := by
    funext i
    have := congrFun hv i
    simp only [vecOf, Prod.mk.injEq] at this
    exact this.1
  have hdig : F.digVec N k = F.digVec N' k := by
    funext i
    have := congrFun hv i
    simp only [vecOf, Prod.mk.injEq] at this
    exact this.2
  have hres : F.resVec N k = F.resVec N' k := by
    funext i; simp only [resVec, hdig]
  have h1 := F.syr_iterate_key hN k
  have h2 := F.syr_iterate_key hN' k
  rw [hval, hres, hS] at h1
  have : (F.q : ℤ) ^ k * N = (F.q : ℤ) ^ k * N' := by linarith
  have hq0 : (F.q : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast F.q_pos.ne')
  exact_mod_cast mul_left_cancel₀ hq0 this

/-! ### Real-number auxiliaries -/

/-- If `|u| ≤ 1/2` then `|log(1 - u)| ≤ 1`. -/
theorem abs_log_one_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) : |Real.log (1 - u)| ≤ 1 := by
  have hu1 : 0 < 1 - u := by linarith [(abs_le.mp hu).2]
  rw [abs_le]
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hu1
    have h7 : (1 - u)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hu1 (by norm_num)]; linarith [(abs_le.mp hu).2]
    linarith
  · have := Real.log_le_sub_one_of_pos hu1
    linarith [(abs_le.mp hu).1]

/-- If `|u| ≤ 1/2` and `B > 0` then `|1/(B(1-u)) - 1/B| ≤ 2|u|/B`. -/
theorem abs_inv_mul_one_sub_sub_le {B u : ℝ} (hB : 0 < B) (hu : |u| ≤ 1 / 2) :
    |(B * (1 - u))⁻¹ - B⁻¹| ≤ 2 * |u| * B⁻¹ := by
  have hu1 : 0 < 1 - u := by linarith [(abs_le.mp hu).2]
  have h : (B * (1 - u))⁻¹ - B⁻¹ = B⁻¹ * (u / (1 - u)) := by
    field_simp; ring
  rw [h, abs_mul, abs_of_pos (inv_pos.mpr hB), abs_div, abs_of_pos hu1]
  rw [mul_comm (2 * |u|)]
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hB).le
  rw [div_le_iff₀ hu1]
  have : 1 / 2 ≤ 1 - u := by linarith [(abs_le.mp hu).2]
  nlinarith [abs_nonneg u]

end Family

end GGMCollatz
