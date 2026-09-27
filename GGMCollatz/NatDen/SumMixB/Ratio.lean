import GGMCollatz.NatDen.SumMixB.Moment

/-!
# The pointwise bound for (SUMMIX b): bounding the Radon–Nikodym derivative by the local limit theorem

The core estimate, written in real variables (`point_core`). `n = m + k`, `L = log n`, `a = √(L/n)`, `sm = √m`, `t = sm·a = √(mL/n)`,
`x = s - μn`, `y = σ - μm`, `|y| = sm·z`. Applying the local limit theorem to the numerator and the denominator,

`|P(s_k = s - σ) - P(s_n = s)| ≤ 2A · P(s_n = s) · t · (1 + z + z²)`

(`A` depends only on `v = σ_G²`, the local limit constant `CL`, and `C`). Instead of the expansion of `log w` in the
accompanying paper, we bound directly the ratio of the Gaussian main terms `g_k/g_n = ρ e^X` (`ρ² = n/k`, `X = x²/(2vn) - (x-y)²/(2vk)`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

namespace SumMixBAux

/-- The Gaussian main term in real variables (`gauss p n s = gaussR (sig2 p) n (s - μn)`). -/
noncomputable def gaussR (v n x : ℝ) : ℝ :=
  (2 * Real.pi * v * n) ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / (2 * v * n))

theorem gauss_eq_gaussR (p n : ℕ) (s : ℝ) :
    gauss p n s = gaussR (sig2 p) n (s - muP p * n) := rfl

theorem gaussR_nonneg (v n x : ℝ) (hv : 0 ≤ v) (hn : 0 ≤ n) : 0 ≤ gaussR v n x := by
  unfold gaussR
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

/-- The constant `A` of the pointwise bound. -/
noncomputable def Acoef (v CL C : ℝ) : ℝ :=
  4 * CL * (2 + 4 * (C + 1) ^ 3) + 3 * (C + 1) ^ 2 / v + 2 + CL * (1 + C ^ 3)

theorem Acoef_pos {v CL C : ℝ} (hv : 0 < v) (hCL : 0 ≤ CL) (hC : 0 ≤ C) : 0 < Acoef v CL C := by
  unfold Acoef
  positivity

/-- For `x > 0`, `(x^{-1/2})² = x⁻¹`. -/
theorem rpow_neg_half_sq {x : ℝ} (hx : 0 < x) : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num [Real.rpow_neg_one]

/-- `L ≤ sm` (`L² ≤ m = sm²`). -/
theorem L_le_sm {L m sm : ℝ} (hL1 : 1 ≤ L) (hsm : 0 ≤ sm) (hsm2 : sm ^ 2 = m) (hLm : L ^ 2 ≤ m) :
    L ≤ sm :=
  (sq_le_sq₀ (by linarith) hsm).mp (by rw [hsm2]; exact hLm)

/-- `n^{-1/2} ≤ t`. -/
theorem rpow_neg_half_le_t {n m L a sm : ℝ} (hn : 0 < n) (hL1 : 1 ≤ L) (ha : 0 ≤ a)
    (hna : n * a ^ 2 = L) (hsm : 0 ≤ sm) (hsm2 : sm ^ 2 = m) (hLm : L ^ 2 ≤ m) :
    n ^ (-(1 / 2 : ℝ)) ≤ sm * a := by
  refine (sq_le_sq₀ (Real.rpow_nonneg hn.le _) (mul_nonneg hsm ha)).mp ?_
  rw [rpow_neg_half_sq hn, mul_pow, hsm2, ← one_div, div_le_iff₀ hn]
  have hm1 : 1 ≤ m := by nlinarith
  nlinarith

/-- **(R4)** Error of the denominator: `n^{-1/2} + |x|³/n² ≤ (1 + C³) t`. -/
theorem eps_n_le {n m L a sm C x : ℝ} (hn : 0 < n) (hL1 : 1 ≤ L) (ha : 0 ≤ a)
    (hna : n * a ^ 2 = L) (hsm : 0 ≤ sm) (hsm2 : sm ^ 2 = m) (hLm : L ^ 2 ≤ m) (hC : 0 ≤ C)
    (hx : |x| ≤ C * n * a) :
    n ^ (-(1 / 2 : ℝ)) + |x| ^ 3 / n ^ 2 ≤ (1 + C ^ 3) * (sm * a) := by
  have h1 := rpow_neg_half_le_t hn hL1 ha hna hsm hsm2 hLm
  have hLs := L_le_sm hL1 hsm hsm2 hLm
  have h3 : |x| ^ 3 ≤ (C * n * a) ^ 3 := pow_le_pow_left₀ (abs_nonneg x) hx 3
  have h4 : |x| ^ 3 / n ^ 2 ≤ C ^ 3 * (sm * a) := by
    rw [div_le_iff₀ (by positivity)]
    calc |x| ^ 3 ≤ (C * n * a) ^ 3 := h3
      _ = C ^ 3 * n ^ 2 * a * (n * a ^ 2) := by ring
      _ = C ^ 3 * n ^ 2 * a * L := by rw [hna]
      _ ≤ C ^ 3 * n ^ 2 * a * sm := by
          apply mul_le_mul_of_nonneg_left hLs; positivity
      _ = C ^ 3 * (sm * a) * n ^ 2 := by ring
  linarith

/-- `|x - y| ≤ (C+1) n a` (`|y| ≤ sm L ≤ n a`). -/
theorem abs_sub_le_na {n m L a sm C x y : ℝ} (hn : 0 < n) (hL1 : 1 ≤ L) (ha : 0 ≤ a)
    (hna : n * a ^ 2 = L) (hsm : 0 ≤ sm) (hsm2 : sm ^ 2 = m) (hmL : m * L ≤ n)
    (hx : |x| ≤ C * n * a) (hy : |y| ≤ sm * L) :
    |x - y| ≤ (C + 1) * n * a := by
  have hsL : sm * L ≤ n * a := by
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    rw [mul_pow, mul_pow, hsm2, show n ^ 2 * a ^ 2 = n * (n * a ^ 2) by ring, hna]
    nlinarith
  calc |x - y| ≤ |x| + |y| := abs_sub _ _
    _ ≤ C * n * a + n * a := by linarith
    _ = (C + 1) * n * a := by ring

/-- **(R5)** Error of the numerator: `k^{-1/2} + |x-y|³/k² ≤ (2 + 4(C+1)³) t` (`n ≤ 2k`). -/
theorem eps_k_le {n m k L a sm C x y : ℝ} (hn : 0 < n) (hk : 0 < k) (hk2 : n ≤ 2 * k)
    (hL1 : 1 ≤ L) (ha : 0 ≤ a) (hna : n * a ^ 2 = L) (hsm : 0 ≤ sm) (hsm2 : sm ^ 2 = m)
    (hmL : m * L ≤ n) (hLm : L ^ 2 ≤ m) (hC : 0 ≤ C)
    (hx : |x| ≤ C * n * a) (hy : |y| ≤ sm * L) :
    k ^ (-(1 / 2 : ℝ)) + |x - y| ^ 3 / k ^ 2 ≤ (2 + 4 * (C + 1) ^ 3) * (sm * a) := by
  have hLs := L_le_sm hL1 hsm hsm2 hLm
  have hm1 : 1 ≤ m := by nlinarith
  have h1 : k ^ (-(1 / 2 : ℝ)) ≤ 2 * (sm * a) := by
    refine (sq_le_sq₀ (Real.rpow_nonneg hk.le _) (by positivity)).mp ?_
    rw [rpow_neg_half_sq hk, mul_pow, mul_pow, hsm2, ← one_div, div_le_iff₀ hk]
    have h1 : 1 ≤ m * L := by nlinarith
    have hma : 0 ≤ m * a ^ 2 := by positivity
    calc (1 : ℝ) ≤ 2 * (m * L) := by linarith
      _ = 2 * (m * a ^ 2) * n := by rw [← hna]; ring
      _ ≤ 2 * (m * a ^ 2) * (2 * k) := mul_le_mul_of_nonneg_left hk2 (by positivity)
      _ = 2 ^ 2 * (m * a ^ 2) * k := by ring
  have hxy := abs_sub_le_na hn hL1 ha hna hsm hsm2 hmL hx hy
  have h3 : |x - y| ^ 3 ≤ ((C + 1) * n * a) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hxy 3
  have h4 : |x - y| ^ 3 / k ^ 2 ≤ 4 * (C + 1) ^ 3 * (sm * a) := by
    rw [div_le_iff₀ (by positivity)]
    have hk2' : n ^ 2 ≤ 4 * k ^ 2 := by nlinarith
    calc |x - y| ^ 3 ≤ ((C + 1) * n * a) ^ 3 := h3
      _ = (C + 1) ^ 3 * a * n ^ 2 * (n * a ^ 2) := by ring
      _ = (C + 1) ^ 3 * a * n ^ 2 * L := by rw [hna]
      _ ≤ (C + 1) ^ 3 * a * (4 * k ^ 2) * sm := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hk2' (by positivity)) hLs
            (by linarith) (by positivity)
      _ = 4 * (C + 1) ^ 3 * (sm * a) * k ^ 2 := by ring
  linarith

/-- **(R2)** Difference of exponents: for `X = x²/(2vn) - (x-y)²/(2vk)`, `|X| ≤ (t/v)(C+1)²(1 + z + z²)`. -/
theorem X_le {v n m k a sm L C x y z : ℝ} (hv : 0 < v) (hn : 0 < n) (hk : 0 < k)
    (hnmk : n = m + k) (hk2 : n ≤ 2 * k) (hL1 : 1 ≤ L) (ha : 0 ≤ a) (hna : n * a ^ 2 = L)
    (hsm : 0 ≤ sm) (hsm2 : sm ^ 2 = m) (hmL : m * L ≤ n) (hC : 0 ≤ C)
    (hx : |x| ≤ C * n * a) (hz : 0 ≤ z) (hyz : |y| = sm * z) :
    |x ^ 2 / (2 * v * n) - (x - y) ^ 2 / (2 * v * k)|
      ≤ sm * a / v * (C + 1) ^ 2 * (1 + z + z ^ 2) := by
  set t := sm * a with ht
  have ht0 : 0 ≤ t := by positivity
  have ht2 : n * t ^ 2 = m * L := by
    rw [ht, mul_pow, hsm2, show n * (m * a ^ 2) = m * (n * a ^ 2) by ring, hna]
  have ht1 : t ≤ 1 := by
    refine (sq_le_sq₀ ht0 zero_le_one).mp ?_
    rw [one_pow]
    have h' : n * t ^ 2 ≤ n * 1 := by rw [ht2]; linarith
    exact le_of_mul_le_mul_left h' hn
  have hm0 : 0 ≤ m := by rw [← hsm2]; positivity
  have hmt : m ≤ n * t ^ 2 := by
    rw [ht2]; exact le_mul_of_one_le_right hm0 hL1
  -- identity for the numerator
  have hid : x ^ 2 / (2 * v * n) - (x - y) ^ 2 / (2 * v * k)
      = (-(x ^ 2 * m) + 2 * x * y * n - y ^ 2 * n) / (2 * v * n * k) := by
    rw [div_sub_div _ _ (by positivity) (by positivity), div_eq_div_iff (by positivity)
      (by positivity), hnmk]
    ring
  rw [hid, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * v * n * k)]
  have hnum : |(-(x ^ 2 * m) + 2 * x * y * n - y ^ 2 * n)|
      ≤ x ^ 2 * m + 2 * |x| * |y| * n + y ^ 2 * n := by
    have e1 : |-(x ^ 2 * m)| = x ^ 2 * m := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
    have e2 : |2 * x * y * n| = 2 * |x| * |y| * n := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hn]
    have e3 : |y ^ 2 * n| = y ^ 2 * n := abs_of_nonneg (by positivity)
    calc _ ≤ |-(x ^ 2 * m) + 2 * x * y * n| + |y ^ 2 * n| := abs_sub _ _
      _ ≤ |-(x ^ 2 * m)| + |2 * x * y * n| + |y ^ 2 * n| := by
          gcongr; exact abs_add_le _ _
      _ = _ := by rw [e1, e2, e3]
  have hx2 : x ^ 2 ≤ C ^ 2 * n ^ 2 * a ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rw [sq_abs] at this
    nlinarith
  have hy2 : y ^ 2 = m * z ^ 2 := by
    rw [← sq_abs, hyz, mul_pow, hsm2]
  -- each term
  have htt : t ^ 2 ≤ t := by
    rw [sq]; exact mul_le_of_le_one_left ht0 ht1
  have T1 : x ^ 2 * m ≤ n ^ 2 * t * C ^ 2 := by
    calc x ^ 2 * m ≤ C ^ 2 * n ^ 2 * a ^ 2 * m := mul_le_mul_of_nonneg_right hx2 hm0
      _ = (n ^ 2 * C ^ 2) * t ^ 2 := by rw [ht, mul_pow, hsm2]; ring
      _ ≤ (n ^ 2 * C ^ 2) * t := mul_le_mul_of_nonneg_left htt (by positivity)
      _ = n ^ 2 * t * C ^ 2 := by ring
  have T2 : 2 * |x| * |y| * n ≤ n ^ 2 * t * (2 * C * z) := by
    rw [hyz]
    calc 2 * |x| * (sm * z) * n = |x| * (2 * sm * z * n) := by ring
      _ ≤ (C * n * a) * (2 * sm * z * n) := mul_le_mul_of_nonneg_right hx (by positivity)
      _ = n ^ 2 * t * (2 * C * z) := by rw [ht]; ring
  have T3 : y ^ 2 * n ≤ n ^ 2 * t * z ^ 2 := by
    rw [hy2]
    have h1 : m * n ≤ n ^ 2 * t := by
      calc m * n ≤ (n * t ^ 2) * n := mul_le_mul_of_nonneg_right hmt hn.le
        _ = n ^ 2 * t ^ 2 := by ring
        _ ≤ n ^ 2 * t := mul_le_mul_of_nonneg_left htt (by positivity)
    calc m * z ^ 2 * n = (m * n) * z ^ 2 := by ring
      _ ≤ (n ^ 2 * t) * z ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg z)
      _ = n ^ 2 * t * z ^ 2 := by ring
  have hW : C ^ 2 + 2 * C * z + z ^ 2 ≤ (C + 1) ^ 2 * (1 + z + z ^ 2) := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  have hsum : |(-(x ^ 2 * m) + 2 * x * y * n - y ^ 2 * n)|
      ≤ n ^ 2 * t * (C ^ 2 + 2 * C * z + z ^ 2) := by
    have := add_le_add (add_le_add T1 T2) T3
    calc _ ≤ x ^ 2 * m + 2 * |x| * |y| * n + y ^ 2 * n := hnum
      _ ≤ n ^ 2 * t * C ^ 2 + n ^ 2 * t * (2 * C * z) + n ^ 2 * t * z ^ 2 := this
      _ = n ^ 2 * t * (C ^ 2 + 2 * C * z + z ^ 2) := by ring
  have hnk : n ^ 2 ≤ 2 * n * k := by
    calc n ^ 2 = n * n := sq n
      _ ≤ n * (2 * k) := mul_le_mul_of_nonneg_left hk2 hn.le
      _ = 2 * n * k := by ring
  have hW0 : 0 ≤ t * ((C + 1) ^ 2 * (1 + z + z ^ 2)) := by positivity
  calc |(-(x ^ 2 * m) + 2 * x * y * n - y ^ 2 * n)|
      ≤ n ^ 2 * t * (C ^ 2 + 2 * C * z + z ^ 2) := hsum
    _ ≤ n ^ 2 * t * ((C + 1) ^ 2 * (1 + z + z ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hW; positivity
    _ = n ^ 2 * (t * ((C + 1) ^ 2 * (1 + z + z ^ 2))) := by ring
    _ ≤ (2 * n * k) * (t * ((C + 1) ^ 2 * (1 + z + z ^ 2))) :=
        mul_le_mul_of_nonneg_right hnk hW0
    _ = t / v * (C + 1) ^ 2 * (1 + z + z ^ 2) * (2 * v * n * k) := by
        field_simp

/-- **(R1)** Ratio of the Gaussian main terms: `g_k(x - y) = g_n(x) · ρ · e^X`, `ρ = (2πvk)^{-1/2}/(2πvn)^{-1/2}`,
`X = x²/(2vn) - (x-y)²/(2vk)`. -/
theorem gaussR_split (v n k x y : ℝ) (hv : 0 < v) (hn : 0 < n) (hk : 0 < k) :
    gaussR v k (x - y) = gaussR v n x *
      ((2 * Real.pi * v * k) ^ (-(1 / 2 : ℝ)) / (2 * Real.pi * v * n) ^ (-(1 / 2 : ℝ))) *
        Real.exp (x ^ 2 / (2 * v * n) - (x - y) ^ 2 / (2 * v * k)) := by
  unfold gaussR
  have hA : 0 < (2 * Real.pi * v * n) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have hsplit : -(x - y) ^ 2 / (2 * v * k)
      = -x ^ 2 / (2 * v * n) + (x ^ 2 / (2 * v * n) - (x - y) ^ 2 / (2 * v * k)) := by ring
  rw [hsplit, Real.exp_add]
  field_simp

/-- `ρ² = n/k`. -/
theorem rho_sq (v n k : ℝ) (hv : 0 < v) (hn : 0 < n) (hk : 0 < k) :
    ((2 * Real.pi * v * k) ^ (-(1 / 2 : ℝ)) / (2 * Real.pi * v * n) ^ (-(1 / 2 : ℝ))) ^ 2
      = n / k := by
  rw [div_pow, rpow_neg_half_sq (by positivity), rpow_neg_half_sq (by positivity)]
  field_simp

/-- Bound for `ρ`: if `ρ² = n/k`, `n = m + k ≤ 2k`, `m ≤ n t²`, `t² ≤ t`, then `1 ≤ ρ ≤ 1.415` and `ρ - 1 ≤ 2t`. -/
theorem rho_facts {ρ n m k t : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ^ 2 = n / k) (hk : 0 < k)
    (hnmk : n = m + k) (hk2 : n ≤ 2 * k) (hm0 : 0 ≤ m) (hmt : m ≤ n * t ^ 2) (htt : t ^ 2 ≤ t) :
    1 ≤ ρ ∧ ρ ≤ 1.415 ∧ ρ - 1 ≤ 2 * t := by
  have hρ1 : 1 ≤ ρ ^ 2 := by rw [hρ2, le_div_iff₀ hk]; linarith
  have hρ22 : ρ ^ 2 ≤ 2 := by rw [hρ2, div_le_iff₀ hk]; linarith
  have hρge1 : 1 ≤ ρ := by nlinarith
  refine ⟨hρge1, by nlinarith, ?_⟩
  have h1 : ρ - 1 ≤ ρ ^ 2 - 1 := by nlinarith
  have h2 : ρ ^ 2 - 1 = m / k := by
    rw [hρ2, hnmk]; field_simp; ring
  have h3 : m / k ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ hk]
    calc m ≤ n * t ^ 2 := hmt
      _ ≤ (2 * k) * t ^ 2 := mul_le_mul_of_nonneg_right hk2 (sq_nonneg t)
      _ = 2 * t ^ 2 * k := by ring
  linarith

/-- Bound for the ratio `R = ρ e^X`. -/
theorem R_facts {ρ X t B : ℝ} (hρ : 1 ≤ ρ ∧ ρ ≤ 1.415 ∧ ρ - 1 ≤ 2 * t) (hXB : |X| ≤ B)
    (hX1 : |X| ≤ 1) :
    0 ≤ ρ * Real.exp X ∧ ρ * Real.exp X ≤ 4 ∧ |ρ * Real.exp X - 1| ≤ 3 * B + 2 * t := by
  obtain ⟨hρ1, hρle, hρm1⟩ := hρ
  have hexpX : |Real.exp X - 1| ≤ 2 * |X| := Real.abs_exp_sub_one_le hX1
  have hexpXle : Real.exp X ≤ Real.exp 1 := Real.exp_le_exp.mpr (le_of_abs_le hX1)
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hρ0 : 0 < ρ := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · calc ρ * Real.exp X ≤ 1.415 * 2.7182818286 :=
          mul_le_mul hρle (hexpXle.trans he1.le) (Real.exp_pos _).le (by norm_num)
      _ ≤ 4 := by norm_num
  · have e : ρ * Real.exp X - 1 = ρ * (Real.exp X - 1) + (ρ - 1) := by ring
    rw [e]
    calc |ρ * (Real.exp X - 1) + (ρ - 1)| ≤ |ρ * (Real.exp X - 1)| + |ρ - 1| := abs_add_le _ _
      _ = ρ * |Real.exp X - 1| + (ρ - 1) := by
          rw [abs_mul, abs_of_pos hρ0, abs_of_nonneg (show (0 : ℝ) ≤ ρ - 1 by linarith)]
      _ ≤ 1.415 * (2 * |X|) + 2 * t := by gcongr
      _ ≤ 3 * B + 2 * t := by nlinarith [abs_nonneg X]

/-- Combining the triangle inequality with `g_n ≤ 2 NBn`. -/
theorem combine_lclt {CL gn NBn NBk R εn εk : ℝ} (hCL : 0 ≤ CL) (hgn0 : 0 ≤ gn) (hR0 : 0 ≤ R)
    (hεn0 : 0 ≤ εn) (hεk0 : 0 ≤ εk)
    (hNBn : |NBn - gn| ≤ CL * gn * εn) (hNBk : |NBk - gn * R| ≤ CL * (gn * R) * εk)
    (hε : CL * εn ≤ 1 / 2) :
    |NBk - NBn| ≤ 2 * NBn * (CL * R * εk + |R - 1| + CL * εn) := by
  have hgnNB : gn ≤ 2 * NBn := by
    have h1 := (abs_le.mp hNBn).1
    have h2 : CL * gn * εn ≤ gn / 2 := by
      calc CL * gn * εn = gn * (CL * εn) := by ring
        _ ≤ gn * (1 / 2) := mul_le_mul_of_nonneg_left hε hgn0
        _ = gn / 2 := by ring
    linarith
  have e2 : |gn * R - gn| = gn * |R - 1| := by
    rw [show gn * R - gn = gn * (R - 1) by ring, abs_mul, abs_of_nonneg hgn0]
  have e3 : |gn - NBn| ≤ CL * gn * εn := by rw [abs_sub_comm]; exact hNBn
  have hB0 : 0 ≤ CL * R * εk + |R - 1| + CL * εn := by positivity
  calc |NBk - NBn| = |(NBk - gn * R) + (gn * R - gn) + (gn - NBn)| := by ring_nf
    _ ≤ |NBk - gn * R| + |gn * R - gn| + |gn - NBn| := abs_add_three _ _ _
    _ ≤ CL * (gn * R) * εk + gn * |R - 1| + CL * gn * εn := by rw [e2]; linarith
    _ = gn * (CL * R * εk + |R - 1| + CL * εn) := by ring
    _ ≤ (2 * NBn) * (CL * R * εk + |R - 1| + CL * εn) := mul_le_mul_of_nonneg_right hgnNB hB0

/-- Bound for the bracket. -/
theorem bracket_le {v CL C R εn εk t W : ℝ} (hCL : 0 ≤ CL) (hC : 0 ≤ C)
    (ht0 : 0 ≤ t) (hW1 : 1 ≤ W) (hR4 : R ≤ 4)
    (hR1 : |R - 1| ≤ 3 * (t / v * (C + 1) ^ 2 * W) + 2 * t)
    (hεn : εn ≤ (1 + C ^ 3) * t) (hεk : εk ≤ (2 + 4 * (C + 1) ^ 3) * t) (hεk0 : 0 ≤ εk) :
    CL * R * εk + |R - 1| + CL * εn ≤ Acoef v CL C * t * W := by
  have b1 : CL * R * εk ≤ 4 * CL * (2 + 4 * (C + 1) ^ 3) * t * W := by
    calc CL * R * εk ≤ CL * 4 * ((2 + 4 * (C + 1) ^ 3) * t) := by gcongr
      _ = 4 * CL * (2 + 4 * (C + 1) ^ 3) * t * 1 := by ring
      _ ≤ 4 * CL * (2 + 4 * (C + 1) ^ 3) * t * W := by gcongr
  have b2 : |R - 1| ≤ 3 * (C + 1) ^ 2 / v * t * W + 2 * t * W := by
    have : 2 * t ≤ 2 * t * W := le_mul_of_one_le_right (by positivity) hW1
    calc |R - 1| ≤ 3 * (t / v * (C + 1) ^ 2 * W) + 2 * t := hR1
      _ = 3 * (C + 1) ^ 2 / v * t * W + 2 * t := by ring
      _ ≤ 3 * (C + 1) ^ 2 / v * t * W + 2 * t * W := by linarith
  have b3 : CL * εn ≤ CL * (1 + C ^ 3) * t * W := by
    calc CL * εn ≤ CL * ((1 + C ^ 3) * t) := by gcongr
      _ = CL * (1 + C ^ 3) * t * 1 := by ring
      _ ≤ CL * (1 + C ^ 3) * t * W := by gcongr
  have : Acoef v CL C * t * W = 4 * CL * (2 + 4 * (C + 1) ^ 3) * t * W
      + (3 * (C + 1) ^ 2 / v * t * W + 2 * t * W) + CL * (1 + C ^ 3) * t * W := by
    unfold Acoef; ring
  rw [this]
  linarith

/-- **The core of the pointwise bound**: from the local limit theorem (numerator `NBk`, denominator `NBn`),
`|NBk - NBn| ≤ 2A · NBn · t · (1 + z + z²)`. -/
theorem point_core {v CL C n m k x y a sm L z NBn NBk : ℝ}
    (hv : 0 < v) (hCL : 0 ≤ CL) (hC : 0 ≤ C) (hn : 0 < n) (hk : 0 < k) (hnmk : n = m + k)
    (hk2 : n ≤ 2 * k) (hL1 : 1 ≤ L) (ha : 0 ≤ a) (hna : n * a ^ 2 = L) (hsm : 0 < sm)
    (hsm2 : sm ^ 2 = m) (hmL : m * L ≤ n) (hLm : L ^ 2 ≤ m) (hx : |x| ≤ C * n * a)
    (hz : 0 ≤ z) (hyz : |y| = sm * z) (hzL : z ≤ L)
    (hX1 : 3 * (sm * a) * (C + 1) ^ 2 * L ^ 2 ≤ v)
    (hNBn : |NBn - gaussR v n x| ≤ CL * gaussR v n x * (n ^ (-(1 / 2 : ℝ)) + |x| ^ 3 / n ^ 2))
    (hNBk : |NBk - gaussR v k (x - y)|
      ≤ CL * gaussR v k (x - y) * (k ^ (-(1 / 2 : ℝ)) + |x - y| ^ 3 / k ^ 2))
    (hε : CL * (n ^ (-(1 / 2 : ℝ)) + |x| ^ 3 / n ^ 2) ≤ 1 / 2) :
    |NBk - NBn| ≤ 2 * Acoef v CL C * NBn * (sm * a) * (1 + z + z ^ 2) := by
  have hy : |y| ≤ sm * L := by rw [hyz]; exact mul_le_mul_of_nonneg_left hzL hsm.le
  have hεn := eps_n_le hn hL1 ha hna hsm.le hsm2 hLm hC hx
  have hεk := eps_k_le hn hk hk2 hL1 ha hna hsm.le hsm2 hmL hLm hC hx hy
  have hXle := X_le hv hn hk hnmk hk2 hL1 ha hna hsm.le hsm2 hmL hC hx hz hyz
  have hgk := gaussR_split v n k x y hv hn hk
  have hρ2 := rho_sq v n k hv hn hk
  have hρ0 : 0 < (2 * Real.pi * v * k) ^ (-(1 / 2 : ℝ)) / (2 * Real.pi * v * n) ^ (-(1 / 2 : ℝ)) :=
    div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)
  have hgn0 : 0 ≤ gaussR v n x := gaussR_nonneg v n x hv.le hn.le
  generalize (2 * Real.pi * v * k) ^ (-(1 / 2 : ℝ)) / (2 * Real.pi * v * n) ^ (-(1 / 2 : ℝ)) = ρ
    at hgk hρ2 hρ0
  generalize x ^ 2 / (2 * v * n) - (x - y) ^ 2 / (2 * v * k) = X at hgk hXle
  generalize gaussR v n x = gn at hgk hNBn hgn0 hε
  rw [hgk, mul_assoc gn ρ] at hNBk
  have hεn0 : 0 ≤ n ^ (-(1 / 2 : ℝ)) + |x| ^ 3 / n ^ 2 := by positivity
  have hεk0 : 0 ≤ k ^ (-(1 / 2 : ℝ)) + |x - y| ^ 3 / k ^ 2 := by positivity
  generalize n ^ (-(1 / 2 : ℝ)) + |x| ^ 3 / n ^ 2 = εn at hNBn hε hεn hεn0
  generalize k ^ (-(1 / 2 : ℝ)) + |x - y| ^ 3 / k ^ 2 = εk at hNBk hεk hεk0
  have hm0 : 0 ≤ m := by rw [← hsm2]; positivity
  generalize ht : sm * a = t at hεn hεk hXle hX1 ⊢
  have ht0 : 0 ≤ t := by rw [← ht]; positivity
  have ht2 : n * t ^ 2 = m * L := by
    rw [← ht, mul_pow, hsm2, show n * (m * a ^ 2) = m * (n * a ^ 2) by ring, hna]
  have ht1 : t ≤ 1 := by
    refine (sq_le_sq₀ ht0 zero_le_one).mp ?_
    rw [one_pow]
    have h' : n * t ^ 2 ≤ n * 1 := by rw [ht2]; linarith
    exact le_of_mul_le_mul_left h' hn
  have htt : t ^ 2 ≤ t := by rw [sq]; exact mul_le_of_le_one_left ht0 ht1
  have hmt : m ≤ n * t ^ 2 := by rw [ht2]; exact le_mul_of_one_le_right hm0 hL1
  have hρ := rho_facts hρ0 hρ2 hk hnmk hk2 hm0 hmt htt
  have hW1 : 1 ≤ 1 + z + z ^ 2 := by have := sq_nonneg z; linarith
  have hW3 : 1 + z + z ^ 2 ≤ 3 * L ^ 2 := by
    have h1 : z ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hz hzL 2
    have h2 : L ≤ L ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith) hL1
    have h3 : 1 ≤ L ^ 2 := by linarith
    linarith
  have hX1' : |X| ≤ 1 := by
    calc |X| ≤ t / v * (C + 1) ^ 2 * (1 + z + z ^ 2) := hXle
      _ ≤ t / v * (C + 1) ^ 2 * (3 * L ^ 2) := by gcongr
      _ = (3 * t * (C + 1) ^ 2 * L ^ 2) / v := by ring
      _ ≤ 1 := by rw [div_le_one hv]; exact hX1
  obtain ⟨hR0, hR4, hR1⟩ := R_facts hρ hXle hX1'
  have hcomb := combine_lclt hCL hgn0 hR0 hεn0 hεk0 hNBn hNBk hε
  have hB := bracket_le hCL hC ht0 hW1 hR4 hR1 hεn hεk hεk0
  have hNB0 : 0 ≤ NBn := by
    have h1 := (abs_le.mp hNBn).1
    have h2 : CL * gn * εn ≤ gn / 2 := by
      calc CL * gn * εn = gn * (CL * εn) := by ring
        _ ≤ gn * (1 / 2) := mul_le_mul_of_nonneg_left hε hgn0
        _ = gn / 2 := by ring
    linarith
  calc |NBk - NBn| ≤ 2 * NBn * (CL * (ρ * Real.exp X) * εk + |ρ * Real.exp X - 1| + CL * εn) :=
        hcomb
    _ ≤ 2 * NBn * (Acoef v CL C * t * (1 + z + z ^ 2)) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = 2 * Acoef v CL C * NBn * t * (1 + z + z ^ 2) := by ring

end SumMixBAux

end ND

end GGMCollatz
