import GGMCollatz.NatDen.SumMixB.Bound
import GGMCollatz.NatDen.Statements

/-!
# Assembly of the bound for the reduced quantity of (SUMMIX b)

* `typical_point`: for typical `σ` (`|σ - μm| < √m log n`), check `σ ≤ s` and the range of the local limit theorem, and apply `point_core`.
* `reduced_bound_large`: the bound for large `n` (`log n ≥ L₀`, `log⁶ n ≤ δ n^{1/10}`).
* `reduced_bound`: all `n ≥ 2` (small `n` by the trivial upper bound `reduced_le_two`).
-/

open scoped ENNReal
open Filter

namespace GGMCollatz

namespace ND

namespace SumMixBAux

/-- The local limit theorem with its constant (the content of `lclt_statement`). -/
def LCLTWith (p : ℕ) (CL : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ s : ℕ, |(s : ℝ) - muP p * n| ≤ (n : ℝ) ^ (3 / 5 : ℝ) →
    |nb p n s - gauss p n s| ≤
      CL * gauss p n s * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + |(s : ℝ) - muP p * n| ^ 3 / (n : ℝ) ^ 2)

theorem sig2_pos {p : ℕ} (hp : 2 ≤ p) : 0 < sig2 p := by
  unfold sig2
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < p - 1 := by linarith
  apply div_pos (by linarith)
  positivity

theorem abs_fcut_sub_le_one (p k s σ n : ℕ) : |fcut p k s σ - nb p n s| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [fcut_nonneg p k s σ, fcut_le_one p k s σ, nb_nonneg p n s,
    nb_le_one p n s]

/-- **The pointwise bound for typical `σ`**. -/
theorem typical_point {p : ℕ} (hp : 2 ≤ p) {CL : ℝ} (hCL : 0 < CL) (hLC : LCLTWith p CL)
    {C : ℝ} (hC : 0 < C) {n m s σ : ℕ} (hmn : m ≤ n) {L a sm : ℝ} (hn : (0 : ℝ) < n)
    (hn1 : (1 : ℝ) ≤ n) (hL1 : 1 ≤ L) (ha : 0 ≤ a) (hna : (n : ℝ) * a ^ 2 = L) (hsm : 0 < sm)
    (hsm2 : sm ^ 2 = m) (hmL : (m : ℝ) * L ≤ n) (hLm : L ^ 2 ≤ m) (h2m : 2 * (m : ℝ) ≤ n)
    (hx : |(s : ℝ) - muP p * n| ≤ C * n * a)
    (hX1 : 3 * (sm * a) * (C + 1) ^ 2 * L ^ 2 ≤ sig2 p)
    (hε : CL * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + |(s : ℝ) - muP p * n| ^ 3 / (n : ℝ) ^ 2) ≤ 1 / 2)
    (h5 : 4 * (C + 1) ^ 2 * L ≤ (n : ℝ) ^ (1 / 5 : ℝ))
    (hσ : |(σ : ℝ) - muP p * m| < sm * L) :
    nb p m σ * |fcut p (n - m) s σ - nb p n s|
      ≤ 4 * Acoef (sig2 p) CL C * nb p n s * (sm * a) *
        (nb p m σ * (Real.exp (((σ : ℝ) - muP p * m) / sm)
          + Real.exp (-(((σ : ℝ) - muP p * m) / sm)))) := by
  have hkR : ((n - m : ℕ) : ℝ) = n - m := Nat.cast_sub hmn
  have hk2 : (n : ℝ) ≤ 2 * ((n - m : ℕ) : ℝ) := by rw [hkR]; linarith
  have hkpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by linarith
  have hk1 : 1 ≤ n - m := by
    have : 0 < n - m := by exact_mod_cast hkpos
    omega
  have hn1' : 1 ≤ n := by exact_mod_cast hn1
  -- `σ ≤ s`
  have hsL := smL_le_na hn hL1 ha hna hsm.le hsm2 hmL
  have hna_half : (C + 1) * n * a ≤ n / 2 := by
    have hfive : 4 * (C + 1) ^ 2 * L ≤ n := h5.trans (rpow_fifth_le hn1)
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    rw [show ((C + 1) * n * a) ^ 2 = (C + 1) ^ 2 * n * (n * a ^ 2) by ring, hna]
    have : (C + 1) ^ 2 * L ≤ n / 4 := by linarith
    calc (C + 1) ^ 2 * (n : ℝ) * L = (n : ℝ) * ((C + 1) ^ 2 * L) := by ring
      _ ≤ (n : ℝ) * ((n : ℝ) / 4) := mul_le_mul_of_nonneg_left this hn.le
      _ = ((n : ℝ) / 2) ^ 2 := by ring
  have hμ1 : 1 < muP p := one_lt_muP hp
  have hσs : σ ≤ s := by
    have h1 : (σ : ℝ) ≤ muP p * m + sm * L := by linarith [(abs_lt.mp hσ).2]
    have h2 : muP p * n - C * n * a ≤ s := by linarith [(abs_le.mp hx).1]
    have hnm : (0 : ℝ) ≤ n - m := by linarith
    have h3 : (n : ℝ) - m ≤ muP p * n - muP p * m := by
      have := le_mul_of_one_le_left hnm hμ1.le
      linarith [show muP p * ((n : ℝ) - m) = muP p * n - muP p * m by ring]
    have h4 : sm * L + C * n * a ≤ (n : ℝ) - m := by
      have : (C + 1) * n * a = C * n * a + n * a := by ring
      linarith
    have : (σ : ℝ) ≤ s := by linarith
    exact_mod_cast this
  have hfcut : fcut p (n - m) s σ = nb p (n - m) (s - σ) := by
    unfold fcut; rw [if_pos hσs]
  -- local limit for the numerator
  have hsσ : ((s - σ : ℕ) : ℝ) = s - σ := Nat.cast_sub hσs
  have hval : ((s - σ : ℕ) : ℝ) - muP p * ((n - m : ℕ) : ℝ)
      = ((s : ℝ) - muP p * n) - ((σ : ℝ) - muP p * m) := by
    rw [hsσ, hkR]; ring
  have hy : |(σ : ℝ) - muP p * m| ≤ sm * L := hσ.le
  have hxy := abs_sub_le_na hn hL1 ha hna hsm.le hsm2 hmL hx hy
  have hrk := range_k hn hk2 ha hna hC.le hxy h5
  have hLCk := hLC (n - m) hk1 (s - σ) (by rw [hval]; exact hrk)
  rw [gauss_eq_gaussR, hval] at hLCk
  -- local limit for the denominator
  have hrn := range_n hn ha hna hC.le hx h5
  have hLCn := hLC n hn1' s hrn
  rw [gauss_eq_gaussR] at hLCn
  -- the core estimate
  set y := (σ : ℝ) - muP p * m with hydef
  set z := |y| / sm with hzdef
  have hz : 0 ≤ z := div_nonneg (abs_nonneg _) hsm.le
  have hyz : |y| = sm * z := by rw [hzdef]; field_simp
  have hzL : z ≤ L := by rw [hzdef, div_le_iff₀ hsm]; linarith
  have hcore := point_core (sig2_pos hp) hCL.le hC.le hn hkpos (by rw [hkR]; ring) hk2 hL1 ha hna
    hsm hsm2 hmL hLm hx hz hyz hzL hX1 hLCn hLCk hε
  have hW : 1 + z + z ^ 2 ≤ 2 * (Real.exp (y / sm) + Real.exp (-(y / sm))) := by
    have := one_add_abs_add_sq_le (y / sm)
    have e : (y / sm) ^ 2 = z ^ 2 := by rw [hzdef, div_pow, div_pow, sq_abs]
    rwa [abs_div, abs_of_pos hsm, e] at this
  have hA0 : 0 ≤ Acoef (sig2 p) CL C := (Acoef_pos (sig2_pos hp) hCL.le hC.le).le
  have hb0 : 0 ≤ nb p n s := nb_nonneg _ _ _
  rw [hfcut]
  calc nb p m σ * |nb p (n - m) (s - σ) - nb p n s|
      ≤ nb p m σ * (2 * Acoef (sig2 p) CL C * nb p n s * (sm * a) * (1 + z + z ^ 2)) :=
        mul_le_mul_of_nonneg_left hcore (nb_nonneg _ _ _)
    _ ≤ nb p m σ * (2 * Acoef (sig2 p) CL C * nb p n s * (sm * a) *
          (2 * (Real.exp (y / sm) + Real.exp (-(y / sm))))) := by
        have := nb_nonneg p m σ
        gcongr
    _ = 4 * Acoef (sig2 p) CL C * nb p n s * (sm * a) *
          (nb p m σ * (Real.exp (y / sm) + Real.exp (-(y / sm)))) := by ring

/-- **The bound for large `n`**. -/
theorem reduced_bound_large {p : ℕ} (hp : 2 ≤ p) {CL : ℝ} (hCL : 0 < CL) (hLC : LCLTWith p CL)
    {C : ℝ} (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → m ≤ n → 2 ≤ n → Real.log n ^ 4 ≤ m →
      (m : ℝ) ≤ (n : ℝ) ^ (9 / 10 : ℝ) → ∀ s : ℕ,
        |(s : ℝ) - muP p * n| ≤ C * Real.sqrt (n * Real.log n) →
        ∑' σ, nb p m σ * |fcut p (n - m) s σ - nb p n s|
          ≤ K * Real.sqrt (m * Real.log n / n) * nb p n s := by
  have hv := sig2_pos hp
  set v := sig2 p with hvdef
  set A := Acoef v CL C with hA
  have hA0 : 0 < A := Acoef_pos hv hCL.le hC.le
  set P := (2 * Real.pi * v) ^ (-(1 / 2 : ℝ)) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos (by positivity) _
  set B := 1 + C ^ 2 / (2 * v) with hB
  set D := 8 / P with hD
  have hD0 : 0 < D := by positivity
  set δ := min (min 1 (v ^ 2 / (9 * (C + 1) ^ 4)))
    (min (1 / (4 * CL ^ 2 * (1 + C ^ 3) ^ 2)) (1 / (4 * (C + 1) ^ 2))) with hδ
  have hδ0 : 0 < δ := by
    simp only [hδ, lt_min_iff]
    exact ⟨⟨by norm_num, by positivity⟩, by positivity, by positivity⟩
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδv : δ ≤ v ^ 2 / (9 * (C + 1) ^ 4) := (min_le_left _ _).trans (min_le_right _ _)
  have hδCL : δ ≤ 1 / (4 * CL ^ 2 * (1 + C ^ 3) ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hδC : δ ≤ 1 / (4 * (C + 1) ^ 2) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((eventually_log_ge (max 15 (320000 * (B + D)))).and (eventually_log_six_le hδ0))
  refine ⟨1 + 8 * Real.exp 8 * A, by positivity, N, ?_⟩
  intro n m hNn hmn hn2 hm4 hm9 s hs
  obtain ⟨hLge, hL6⟩ := hN n hNn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  set L := Real.log n with hLdef
  have hL15 : 15 ≤ L := (le_max_left _ _).trans hLge
  have hLB : 320000 * (B + D) ≤ L := (le_max_right _ _).trans hLge
  have hL1 : 1 ≤ L := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hm1 : (1 : ℝ) ≤ m := hL4.trans hm4
  have hLm : L ^ 2 ≤ m := (pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 4)).trans hm4
  have hL6ge : L ≤ L ^ 6 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL6two : 2 ≤ L ^ 6 := by linarith
  have hδn : δ * n ≤ n := mul_le_of_le_one_left hnR.le hδ1
  have hkey : (m : ℝ) * L ^ 6 ≤ δ * n := by
    calc (m : ℝ) * L ^ 6 ≤ (m : ℝ) * (δ * (n : ℝ) ^ (1 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_left hL6 hm0
      _ = δ * ((m : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)) := by ring
      _ ≤ δ * ((n : ℝ) ^ (9 / 10 : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hδ0.le
          exact mul_le_mul_of_nonneg_right hm9 (Real.rpow_nonneg hnR.le _)
      _ = δ * n := by rw [rpow_nine_tenths_mul hnR]
  have hmL : (m : ℝ) * L ≤ n := by
    have : (m : ℝ) * L ≤ (m : ℝ) * L ^ 6 := mul_le_mul_of_nonneg_left hL6ge hm0
    linarith
  have h2m : 2 * (m : ℝ) ≤ n := by
    have : 2 * (m : ℝ) ≤ (m : ℝ) * L ^ 6 := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hL6two hm0
    linarith
  -- `a = √(L/n)`, `sm = √m`
  set a := Real.sqrt (L / n) with hadef
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := by linarith
  have hna : (n : ℝ) * a ^ 2 = L := by
    rw [hadef, Real.sq_sqrt (div_nonneg hL0 hnR.le), mul_div_cancel₀ _ hnR.ne']
  set sm := Real.sqrt m with hsmdef
  have hsm : 0 < sm := Real.sqrt_pos.mpr (by linarith)
  have hsm2 : sm ^ 2 = m := Real.sq_sqrt hm0
  have ht_eq : Real.sqrt (m * L / n) = sm * a := sqrt_t_eq hm0
  have hx : |(s : ℝ) - muP p * n| ≤ C * n * a := by
    have h := hs
    rw [sqrt_mul_log_eq hnR] at h
    linarith [show C * ((n : ℝ) * a) = C * n * a by ring]
  set t := sm * a with htdef
  have ht0 : 0 ≤ t := by positivity
  have ht2 : (n : ℝ) * t ^ 2 = m * L := by
    rw [htdef, mul_pow, hsm2, show (n : ℝ) * ((m : ℝ) * a ^ 2) = m * (n * a ^ 2) by ring, hna]
  have htL4 : t ^ 2 * L ^ 4 ≤ δ := by
    have h1 : (n : ℝ) * (t ^ 2 * L ^ 4) = m * L ^ 5 := by
      rw [← mul_assoc, ht2]; ring
    have h2 : (m : ℝ) * L ^ 5 ≤ m * L ^ 6 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by norm_num)) hm0
    have h3 : (n : ℝ) * (t ^ 2 * L ^ 4) ≤ n * δ := by
      rw [h1]; linarith [mul_comm δ (n : ℝ)]
    exact le_of_mul_le_mul_left h3 hnR
  have ht2δ : t ^ 2 ≤ δ := le_trans (le_mul_of_one_le_right (sq_nonneg t) hL4) htL4
  -- the conditions `hX1`, `hε`, `h5`
  have hX1 : 3 * t * (C + 1) ^ 2 * L ^ 2 ≤ v := by
    refine (sq_le_sq₀ (by positivity) hv.le).mp ?_
    have hC4 : 0 < 9 * (C + 1) ^ 4 := by positivity
    calc (3 * t * (C + 1) ^ 2 * L ^ 2) ^ 2 = 9 * (C + 1) ^ 4 * (t ^ 2 * L ^ 4) := by ring
      _ ≤ 9 * (C + 1) ^ 4 * δ := mul_le_mul_of_nonneg_left htL4 hC4.le
      _ ≤ 9 * (C + 1) ^ 4 * (v ^ 2 / (9 * (C + 1) ^ 4)) := mul_le_mul_of_nonneg_left hδv hC4.le
      _ = v ^ 2 := by field_simp
  have hεn := eps_n_le hnR hL1 ha hna hsm.le hsm2 hLm hC.le hx
  have hε : CL * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + |(s : ℝ) - muP p * n| ^ 3 / (n : ℝ) ^ 2) ≤ 1 / 2 := by
    have h1 : CL * (1 + C ^ 3) * t ≤ 1 / 2 := by
      refine (sq_le_sq₀ (by positivity) (by norm_num)).mp ?_
      have hc' : 0 ≤ CL ^ 2 * (1 + C ^ 3) ^ 2 := by positivity
      have hc'' : CL ^ 2 * (1 + C ^ 3) ^ 2 ≠ 0 := by positivity
      calc (CL * (1 + C ^ 3) * t) ^ 2 = CL ^ 2 * (1 + C ^ 3) ^ 2 * t ^ 2 := by ring
        _ ≤ CL ^ 2 * (1 + C ^ 3) ^ 2 * δ := mul_le_mul_of_nonneg_left ht2δ hc'
        _ ≤ CL ^ 2 * (1 + C ^ 3) ^ 2 * (1 / (4 * CL ^ 2 * (1 + C ^ 3) ^ 2)) :=
            mul_le_mul_of_nonneg_left hδCL hc'
        _ = (1 / 2) ^ 2 := by field_simp; ring
    calc CL * ((n : ℝ) ^ (-(1 / 2 : ℝ)) + |(s : ℝ) - muP p * n| ^ 3 / (n : ℝ) ^ 2)
        ≤ CL * ((1 + C ^ 3) * t) := mul_le_mul_of_nonneg_left hεn hCL.le
      _ = CL * (1 + C ^ 3) * t := by ring
      _ ≤ 1 / 2 := h1
  have h5 : 4 * (C + 1) ^ 2 * L ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hc : 0 < 4 * (C + 1) ^ 2 := by positivity
    calc 4 * (C + 1) ^ 2 * L ≤ 4 * (C + 1) ^ 2 * (δ * (n : ℝ) ^ (1 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hL6ge.trans hL6) hc.le
      _ ≤ 4 * (C + 1) ^ 2 * (1 / (4 * (C + 1) ^ 2) * (n : ℝ) ^ (1 / 5 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hc.le
          exact mul_le_mul hδC (rpow_tenth_le_fifth hn1) (Real.rpow_nonneg hnR.le _)
            (by positivity)
      _ = (n : ℝ) ^ (1 / 5 : ℝ) := by field_simp
  -- local limit for the denominator and the lower bound for `t · P(s_n = s)`
  have hrn := range_n hnR ha hna hC.le hx h5
  have hLCn := hLC n (by omega) s hrn
  rw [gauss_eq_gaussR] at hLCn
  have hgn := gn_le_two_nb (gaussR_nonneg v n _ hv.le hnR.le) hLCn hε
  set b := nb p n s with hbdef
  have hb0 : 0 ≤ b := nb_nonneg _ _ _
  have hLs := L_le_sm hL1 hsm.le hsm2 hLm
  have htn := rpow_neg_half_le_t hnR hL1 ha hna hsm.le hsm2 hLm
  have htb := tb_lower hv hnR hLdef.symm hna hx htn hgn
  have hgw := gweight_tail_le hm1 hsm.le hsm2 hL1 hLs
  have hexp := exp_quad_ge hD0 hL1 hLB
  have htail : 2 * Gweight (1 + (m : ℝ)) (1 / 400 * (sm * L)) ≤ t * b := by
    refine hgw.trans (le_trans ?_ htb)
    have e : P / 2 * Real.exp (-B * L)
        = P / 2 * Real.exp (L ^ 2 / 320000 - B * L) * Real.exp (-(L ^ 2 / 320000)) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [e]
    have hE0 : 0 ≤ Real.exp (-(L ^ 2 / 320000)) := (Real.exp_pos _).le
    calc 4 * Real.exp (-(L ^ 2 / 320000)) = P / 2 * D * Real.exp (-(L ^ 2 / 320000)) := by
          rw [hD]; field_simp; ring
      _ ≤ P / 2 * Real.exp (L ^ 2 / 320000 - B * L) * Real.exp (-(L ^ 2 / 320000)) := by
          apply mul_le_mul_of_nonneg_right _ hE0
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
  -- splitting into typical and atypical
  have hsm200 : 200 ≤ sm := by
    rw [hsmdef]
    refine (Real.le_sqrt (by norm_num) hm0).mpr ?_
    have : (15 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL15 4
    have h' : (200 : ℝ) ^ 2 ≤ 15 ^ 4 := by norm_num
    linarith
  obtain ⟨hMs, hM⟩ := coshMoment hp m hsm200
  have hsplit := tsum_le_of_split
    (f := fun σ => nb p m σ * |fcut p (n - m) s σ - b|)
    (g := fun σ => if sm * L ≤ |(σ : ℝ) - muP p * m| then nb p m σ else 0)
    (h := fun σ => 4 * A * b * t * (nb p m σ * (Real.exp (((σ : ℝ) - muP p * m) / sm)
      + Real.exp (-(((σ : ℝ) - muP p * m) / sm)))))
    (fun σ => sm * L ≤ |(σ : ℝ) - muP p * m|)
    (fun σ => mul_nonneg (nb_nonneg _ _ _) (abs_nonneg _))
    (fun σ => by
      show 0 ≤ (if sm * L ≤ |(σ : ℝ) - muP p * m| then nb p m σ else 0)
      split_ifs
      · exact nb_nonneg _ _ _
      · exact le_refl 0)
    (fun σ => by
      have := nb_nonneg p m σ
      have := Real.exp_pos (((σ : ℝ) - muP p * m) / sm)
      have := Real.exp_pos (-(((σ : ℝ) - muP p * m) / sm))
      positivity)
    (summable_tail p m (sm * L)) (hMs.mul_left _)
    (fun σ hσ => by
      show nb p m σ * |fcut p (n - m) s σ - b|
        ≤ (if sm * L ≤ |(σ : ℝ) - muP p * m| then nb p m σ else 0)
      rw [if_pos hσ]
      exact mul_le_of_le_one_right (nb_nonneg _ _ _) (abs_fcut_sub_le_one _ _ _ _ _))
    (fun σ hσ => typical_point hp hCL hLC hC hmn hnR hn1 hL1 ha hna hsm hsm2 hmL hLm h2m hx hX1
      hε h5 (not_le.mp hσ))
  have hgt : ∑' σ : ℕ, (if sm * L ≤ |(σ : ℝ) - muP p * m| then nb p m σ else 0) ≤ t * b :=
    (tail_le hp m (by positivity)).trans htail
  have hht : ∑' σ : ℕ, 4 * A * b * t * (nb p m σ * (Real.exp (((σ : ℝ) - muP p * m) / sm)
      + Real.exp (-(((σ : ℝ) - muP p * m) / sm)))) ≤ 8 * Real.exp 8 * A * t * b := by
    rw [tsum_mul_left]
    calc 4 * A * b * t * ∑' σ : ℕ, nb p m σ * (Real.exp (((σ : ℝ) - muP p * m) / sm)
          + Real.exp (-(((σ : ℝ) - muP p * m) / sm)))
        ≤ 4 * A * b * t * (2 * Real.exp 8) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 8 * Real.exp 8 * A * t * b := by ring
  rw [ht_eq]
  calc ∑' σ, nb p m σ * |fcut p (n - m) s σ - b| ≤ t * b + 8 * Real.exp 8 * A * t * b := by
        linarith
    _ = (1 + 8 * Real.exp 8 * A) * t * b := by ring

/-- **Bound for the reduced quantity** (all `n ≥ 2`): `Σ_σ P(s_m = σ) |P(s_{n-m} = s - σ) - P(s_n = s)|
≤ K √(m log n / n) P(s_n = s)`. Small `n` by the trivial upper bound `reduced_le_two` and `t ≥ √(log 2 / N)`. -/
theorem reduced_bound {p : ℕ} (hp : 2 ≤ p) (hL : lclt_statement p) :
    ∀ C : ℝ, 0 < C → ∃ K : ℝ, 0 < K ∧ ∀ n m : ℕ, m ≤ n → 2 ≤ n → Real.log n ^ 4 ≤ m →
      (m : ℝ) ≤ (n : ℝ) ^ (9 / 10 : ℝ) → ∀ s : ℕ,
        |(s : ℝ) - muP p * n| ≤ C * Real.sqrt (n * Real.log n) →
        ∑' σ, nb p m σ * |fcut p (n - m) s σ - nb p n s|
          ≤ K * Real.sqrt (m * Real.log n / n) * nb p n s := by
  intro C hC
  obtain ⟨CL, hCL, hLC⟩ := hL
  obtain ⟨K₁, hK₁, N, hN⟩ := reduced_bound_large hp hCL hLC hC
  have hN'2 : 2 ≤ max N 2 := le_max_right _ _
  have hN'pos : (0 : ℝ) < (max N 2 : ℕ) := by exact_mod_cast (by omega : 0 < max N 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs2 : 0 < Real.sqrt (Real.log 2 / (max N 2 : ℕ)) :=
    Real.sqrt_pos.mpr (div_pos hlog2 hN'pos)
  set K₂ := 2 / Real.sqrt (Real.log 2 / (max N 2 : ℕ)) with hK₂def
  have hK₂ : 0 < K₂ := div_pos two_pos hs2
  refine ⟨max K₁ K₂, lt_max_of_lt_left hK₁, ?_⟩
  intro n m hmn hn2 hm4 hm9 s hs
  have hb0 : 0 ≤ nb p n s := nb_nonneg _ _ _
  by_cases hNn : N ≤ n
  · calc _ ≤ K₁ * Real.sqrt (m * Real.log n / n) * nb p n s := hN n m hNn hmn hn2 hm4 hm9 s hs
      _ ≤ max K₁ K₂ * Real.sqrt (m * Real.log n / n) * nb p n s := by
          gcongr
          exact le_max_left _ _
  · have hnN : (n : ℝ) ≤ (max N 2 : ℕ) := by
      exact_mod_cast (le_of_lt (lt_of_lt_of_le (not_le.mp hNn) (le_max_left _ _)))
    have htriv := reduced_le_two p m (n - m) s
    rw [Nat.add_sub_cancel' hmn] at htriv
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlogn : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hlogn0 : 0 < Real.log n := lt_of_lt_of_le hlog2 hlogn
    have hm1 : (1 : ℝ) ≤ m := by
      have h1 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm4
      have h2 : 0 < m := by exact_mod_cast h1
      exact_mod_cast h2
    have ht : Real.sqrt (Real.log 2 / (max N 2 : ℕ)) ≤ Real.sqrt (m * Real.log n / n) := by
      apply Real.sqrt_le_sqrt
      calc Real.log 2 / ((max N 2 : ℕ) : ℝ) ≤ Real.log n / n :=
            div_le_div₀ hlogn0.le hlogn hnR hnN
        _ ≤ m * Real.log n / n := by
            apply div_le_div_of_nonneg_right _ hnR.le
            exact le_mul_of_one_le_left hlogn0.le hm1
    calc ∑' σ, nb p m σ * |fcut p (n - m) s σ - nb p n s| ≤ 2 * nb p n s := htriv
      _ = K₂ * Real.sqrt (Real.log 2 / (max N 2 : ℕ)) * nb p n s := by
          rw [hK₂def, div_mul_cancel₀ _ hs2.ne']
      _ ≤ max K₁ K₂ * Real.sqrt (m * Real.log n / n) * nb p n s := by
          gcongr
          exact le_max_right _ _

end SumMixBAux

end ND

end GGMCollatz
