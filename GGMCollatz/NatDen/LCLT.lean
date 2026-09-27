import GGMCollatz.NatDen.Statements
import GGMCollatz.NatDen.LCLTAux

/-!
# (LCLT) Local limit theorem for sums of `G(μ)` (negative binomial)

`lclt`: for `|s - μn| ≤ n^{3/5}`, `P(s_n = s) = g(n,s)(1 + O(n^{-1/2} + |s-μn|³/n²))`.

Proof (the accompanying paper omits the details; here it is organized as follows):

1. From the closed form of the negative binomial `P(s_n = s) = C(s-1, n-1)(p-1)^n p^{-s}` (`iidSum_geomP_apply`),
   when `m = s - n ≥ 1`, `log P = log s! - log n! - log m! + log n - log s + n log(p-1) - s log p`.
2. Two-sided Stirling `0 ≤ log k! - stir k ≤ 1/(12k)` (`LCLTAux.log_factorial_sub_stir`).
3. The identity `LCLTAux.lclt_log_identity`: the difference between the logarithms of the Stirling main part and of the
   Gaussian main term is `μn·phi(u) - (μ-1)n·phi(v) - log(1+u)/2 - log(1+v)/2` (`u = d/(μn)`, `v = d/((μ-1)n)`, `d = s - μn`).
4. With `2(p-1)|d| ≤ n` (from `n ≥ (2p)^5` and `|d| ≤ n^{3/5}`), `|u|, |v| ≤ 1/2`, and the remainder is
   `O(|d|³/n² + |d|/n + 1/n)` (`LCLTAux.lclt_rem_bound`). `|d|/n ≤ n^{-1/2} + |d|³/n²`, `1/n ≤ n^{-1/2}`.
5. `|e^E - 1| ≤ |E|e^{|E|}` and `|E| ≤ 2K`.
6. The finitely many `n < (2p)^5` are absorbed into the constant using `nb ≤ 1` and a positive lower bound for the Gaussian main term.
-/

open Real

namespace GGMCollatz

namespace ND

open LCLTAux

/-! The auxiliary declarations are put in `ND.LCLTAux` to avoid name clashes with the other leaf files filled in parallel. -/

namespace LCLTAux

/-! ### Closed forms of `nb` and `gauss` -/

/-- Closed form of `nb` (real): `C(s-1, n-1)(p-1)^n p^{-s}` (`n, s ≥ 1`). -/
theorem nb_eq {p : ℕ} (hp : 2 ≤ p) (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) :
    nb p n s = ((s - 1).choose (n - 1) : ℝ) * ((p : ℝ) - 1) ^ n * ((p : ℝ)⁻¹) ^ s := by
  unfold nb
  rw [iidSum_geomP_apply hp n s hn hs, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]

theorem nb_nonneg (p n s : ℕ) : 0 ≤ nb p n s := ENNReal.toReal_nonneg

theorem nb_le_one (p n s : ℕ) : nb p n s ≤ 1 := by
  unfold nb
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one _ _)

/-- For `m ≥ 1`, write `log P(s_n = n + m)` in terms of factorials. -/
theorem log_nb {p : ℕ} (hp : 2 ≤ p) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Real.log (nb p n (n + m)) =
      Real.log ((n + m).factorial : ℝ) - Real.log (n.factorial : ℝ) - Real.log (m.factorial : ℝ)
        + Real.log n - Real.log ((n : ℝ) + m) + n * Real.log ((p : ℝ) - 1)
        - ((n : ℝ) + m) * Real.log p := by
  have hP0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hP1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [nb_eq hp (k + 1) (k + 1 + m) hn (by omega)]
  have e1 : k + 1 + m - 1 = k + m := by omega
  have e2 : k + 1 - 1 = k := by omega
  rw [e1, e2]
  -- `C(k+m, k) = (k+1)(k+1+m)! / ((k+1+m)(k+1)! m!)`
  have hnat := Nat.choose_mul_factorial_mul_factorial (n := k + m) (k := k) (by omega)
  rw [show k + m - k = m by omega] at hnat
  have hC : ((k + m).choose k : ℝ) * (k.factorial : ℝ) * (m.factorial : ℝ)
      = ((k + m).factorial : ℝ) := by exact_mod_cast hnat
  have hf1 : ((k + 1 + m).factorial : ℝ) = ((k + m : ℕ) + 1 : ℝ) * ((k + m).factorial : ℝ) := by
    rw [show k + 1 + m = (k + m) + 1 by omega, Nat.factorial_succ]
    push_cast; ring
  have hf2 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hkf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hmf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hkmf : (0 : ℝ) < (k + m).factorial := by exact_mod_cast Nat.factorial_pos (k + m)
  have hCpos : (0 : ℝ) < ((k + m).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hlogC : Real.log ((k + m).choose k : ℝ)
      = Real.log ((k + m).factorial : ℝ) - Real.log (k.factorial : ℝ) - Real.log (m.factorial : ℝ) := by
    rw [← hC, Real.log_mul (by positivity) hmf.ne', Real.log_mul hCpos.ne' hkf.ne']
    ring
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkm1 : (0 : ℝ) < ((k + m : ℕ) : ℝ) + 1 := by positivity
  have ha : ((k + m : ℕ) : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) + (m : ℝ) := by push_cast; ring
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    hlogC, Real.log_pow, Real.log_pow, Real.log_inv, hf1, hf2,
    Real.log_mul hkm1.ne' hkmf.ne', Real.log_mul hk1.ne' hkf.ne', ha]
  push_cast
  ring

/-- The Gaussian main term is positive. -/
theorem gauss_pos {p : ℕ} (hp : 2 ≤ p) (n : ℕ) (hn : 1 ≤ n) (s : ℝ) : 0 < gauss p n s := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hσ : 0 < sig2 p := by unfold sig2; apply div_pos <;> nlinarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gauss
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- `log` of the Gaussian main term. -/
theorem log_gauss {p : ℕ} (hp : 2 ≤ p) (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    Real.log (gauss p n s) = -(1 / 2) * Real.log (2 * π * sig2 p * n)
      - (s - muP p * n) ^ 2 / (2 * sig2 p * n) := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hσ : 0 < sig2 p := by unfold sig2; apply div_pos <;> nlinarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gauss
  rw [Real.log_mul (Real.rpow_pos_of_pos (by positivity) _).ne' (Real.exp_pos _).ne',
    Real.log_rpow (by positivity), Real.log_exp]
  ring

/-! ### Real-number auxiliaries -/

/-- `t = n^{1/5}`: `t ≥ 1`, `t⁵ = n`, `n^{3/5} = t³`. -/
theorem exists_fifth_root (n : ℕ) (hn : 1 ≤ n) :
    ∃ t : ℝ, 1 ≤ t ∧ t ^ 5 = n ∧ (n : ℝ) ^ (3 / 5 : ℝ) = t ^ 3 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨(n : ℝ) ^ ((1 : ℝ) / 5), Real.one_le_rpow hn' (by norm_num), ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num

/-- `n^{-1/2} = (√n)⁻¹`. -/
theorem rpow_neg_half_eq (x : ℝ) (hx : 0 ≤ x) : x ^ (-(1 / 2 : ℝ)) = (√x)⁻¹ := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow]

/-- `1/n ≤ (√n)⁻¹` (`n ≥ 1`). -/
theorem inv_le_inv_sqrt (x : ℝ) (hx : 1 ≤ x) : 1 / x ≤ (√x)⁻¹ := by
  have hr : 1 ≤ √x := by rw [Real.one_le_sqrt]; exact hx
  have hrr : √x * √x = x := Real.mul_self_sqrt (by linarith)
  have e : 1 / x = (√x)⁻¹ * (√x)⁻¹ := by
    rw [← mul_inv, hrr, one_div]
  rw [e]
  have : (√x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  have h0 : 0 < (√x)⁻¹ := by positivity
  nlinarith

/-- `D/n ≤ (√n)⁻¹ + D³/n²` (`n ≥ 1`, `D ≥ 0`). -/
theorem div_le_inv_sqrt_add (x D : ℝ) (hx : 1 ≤ x) (hD : 0 ≤ D) :
    D / x ≤ (√x)⁻¹ + D ^ 3 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hr0 : 0 < √x := Real.sqrt_pos.mpr hx0
  have hrr : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hX : 0 ≤ D ^ 3 / x ^ 2 := by positivity
  have hI : 0 ≤ (√x)⁻¹ := by positivity
  rcases le_or_gt D (√x) with h | h
  · -- `D ≤ √n`: `D/n ≤ √n/n = (√n)⁻¹`
    have e : (√x)⁻¹ * x = √x := by
      calc (√x)⁻¹ * x = (√x)⁻¹ * (√x * √x) := by rw [hrr]
        _ = √x := by field_simp
    have : D / x ≤ (√x)⁻¹ := by
      rw [div_le_iff₀ hx0, e]
      exact h
    linarith
  · -- `D > √n`: `D³/n² ≥ D·n/n² = D/n`
    have hD2 : x ≤ D ^ 2 := by nlinarith
    have : D / x ≤ D ^ 3 / x ^ 2 := by
      rw [div_le_div_iff₀ hx0 (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hD hx0.le) (sub_nonneg.mpr hD2)]
    linarith

/-! ### Large `n` -/

/-- **The case of large `n`**: if `2(p-1)|d| ≤ n`, then
`|log P(s_n = s) - log g(n,s)| ≤ (4 + 4(P-1)²)|d|³/n² + P|d|/n + 2P/n` (`P = p`, `d = s - μn`). -/
theorem lclt_log_large {p : ℕ} (hp : 2 ≤ p) (n s : ℕ) (hn : 1 ≤ n)
    (hsmall : 2 * ((p : ℝ) - 1) * |(s : ℝ) - muP p * n| ≤ n) :
    |Real.log (nb p n s) - Real.log (gauss p n s)| ≤
      (4 + 4 * ((p : ℝ) - 1) ^ 2) * (|(s : ℝ) - muP p * n| ^ 3 / (n : ℝ) ^ 2)
        + (p : ℝ) * (|(s : ℝ) - muP p * n| / n) + 2 * (p : ℝ) / n := by
  set P : ℝ := (p : ℝ) with hPdef
  have hP2 : (2 : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast hp
  have hP : 1 < P := by linarith
  have hP1 : (0 : ℝ) < P - 1 := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set d : ℝ := (s : ℝ) - muP p * n with hd
  have hμ : muP p = P / (P - 1) := rfl
  -- `s - n = n/(P-1) + d ≥ n/(2(P-1)) > 0`
  have hsn : (s : ℝ) - n = n / (P - 1) + d := by
    rw [hd, hμ]; field_simp; ring
  have hdlow : -(n / (2 * (P - 1))) ≤ d := by
    have h1 : |d| ≤ n / (2 * (P - 1)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith [neg_abs_le d]
  have hmlow : n / (2 * (P - 1)) ≤ (s : ℝ) - n := by
    rw [hsn]
    have : n / (P - 1) = 2 * (n / (2 * (P - 1))) := by field_simp
    linarith
  have hmpos : (0 : ℝ) < (s : ℝ) - n := lt_of_lt_of_le (by positivity) hmlow
  have hns : n < s := by
    have : (n : ℝ) < s := by linarith
    exact_mod_cast this
  obtain ⟨m, rfl⟩ : ∃ m, s = n + m := ⟨s - n, by omega⟩
  have hm : 1 ≤ m := by omega
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmcast : ((n + m : ℕ) : ℝ) = (n : ℝ) + m := by push_cast; ring
  rw [hmcast] at hd hmlow
  have hmlow' : n / (2 * (P - 1)) ≤ (m : ℝ) := by linarith
  -- decomposition of the logarithm
  rw [log_nb hp n m hn hm, log_gauss hp n hn, hmcast]
  set θs := Real.log ((n + m).factorial : ℝ) - stir ((n : ℝ) + m) with hθs
  set θn := Real.log (n.factorial : ℝ) - stir n with hθn
  set θm := Real.log (m.factorial : ℝ) - stir m with hθm
  have hbs := abs_log_factorial_sub_stir (n + m) (by omega)
  have hbn := abs_log_factorial_sub_stir n hn
  have hbm := abs_log_factorial_sub_stir m hm
  rw [hmcast] at hbs
  rw [← hθs] at hbs
  rw [← hθn] at hbn
  rw [← hθm] at hbm
  set u : ℝ := d / (muP p * n) with hu
  set v : ℝ := d * (P - 1) / n with hv
  have hid := lclt_log_identity P n m (muP p) (sig2 p) d u v hP hn' hm' hμ rfl hd hu hv
  have hrem := lclt_rem_bound P n (muP p) d u v hP hn' hμ hu hv hsmall
  -- difference = right-hand side of the identity + (θs - θn - θm)
  have hsplit : Real.log ((n + m).factorial : ℝ) - Real.log (n.factorial : ℝ)
        - Real.log (m.factorial : ℝ) + Real.log n - Real.log ((n : ℝ) + m) + n * Real.log (P - 1)
        - ((n : ℝ) + m) * Real.log P
        - (-(1 / 2) * Real.log (2 * π * sig2 p * n) - ((n : ℝ) + m - muP p * n) ^ 2 / (2 * sig2 p * n))
      = (muP p * n * phi u - (1 / (P - 1)) * n * phi v - Real.log (1 + u) / 2
          - Real.log (1 + v) / 2) + (θs - θn - θm) := by
    rw [← hid, hθs, hθn, hθm, hd]
    ring
  rw [hsplit]
  -- Stirling errors
  have h1s : 1 / ((n : ℝ) + m) ≤ 1 / n := one_div_le_one_div_of_le hn' (by linarith)
  have h1m : 1 / (m : ℝ) ≤ 2 * (P - 1) / n := by
    rw [div_le_div_iff₀ hm' hn']
    rw [div_le_iff₀ (by positivity)] at hmlow'
    linarith
  have hθ : |θs - θn - θm| ≤ 2 * P / n := by
    have e : 2 * P / n = 1 / n + 1 / n + 2 * (P - 1) / n := by field_simp; ring
    rw [e]
    have a1 := abs_le.mp hbs
    have a2 := abs_le.mp hbn
    have a3 := abs_le.mp hbm
    rw [abs_le]
    constructor <;> linarith
  calc |(muP p * n * phi u - (1 / (P - 1)) * n * phi v - Real.log (1 + u) / 2
          - Real.log (1 + v) / 2) + (θs - θn - θm)|
      ≤ |muP p * n * phi u - (1 / (P - 1)) * n * phi v - Real.log (1 + u) / 2
          - Real.log (1 + v) / 2| + |θs - θn - θm| := abs_add_le _ _
    _ ≤ _ := by linarith

/-! ### Lower bound for the Gaussian main term (small `n`) -/

/-- If `n ≤ N` and `d² ≤ Nn`, then `(2πσN)^{-1/2} e^{-N/(2σ)} ≤ (2πσn)^{-1/2} e^{-d²/(2σn)}`. -/
theorem gauss_lb_aux (σ n N d : ℝ) (hσ : 0 < σ) (hn : 0 < n) (hnN : n ≤ N)
    (hd2 : d ^ 2 ≤ N * n) :
    (2 * π * σ * N) ^ (-(1 / 2 : ℝ)) * Real.exp (-N / (2 * σ))
      ≤ (2 * π * σ * n) ^ (-(1 / 2 : ℝ)) * Real.exp (-d ^ 2 / (2 * σ * n)) := by
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (by norm_num)
  · apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hd2 (by positivity : (0 : ℝ) ≤ 2 * σ)
    nlinarith
  · exact (Real.exp_pos _).le
  · exact (Real.rpow_pos_of_pos (by positivity) _).le

/-! ### The two cases -/

/-- The constant `K = 4 + 4(P-1)² + 3P` (`P = p`). -/
noncomputable def lcltK (p : ℕ) : ℝ := 4 + 4 * ((p : ℝ) - 1) ^ 2 + 3 * (p : ℝ)

/-- The threshold for small `n`: `N₀ = (2p)⁵`. -/
def lcltN0 (p : ℕ) : ℕ := (2 * p) ^ 5

/-- Lower bound for the Gaussian main term at small `n`: `g₀ = (2πσ²N₀)^{-1/2} e^{-N₀/(2σ²)}`. -/
noncomputable def lcltG0 (p : ℕ) : ℝ :=
  (2 * π * sig2 p * (lcltN0 p : ℝ)) ^ (-(1 / 2 : ℝ)) * Real.exp (-(lcltN0 p : ℝ) / (2 * sig2 p))

theorem sig2_pos {p : ℕ} (hp : 2 ≤ p) : 0 < sig2 p := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold sig2; apply div_pos <;> nlinarith

theorem lcltK_pos {p : ℕ} (hp : 2 ≤ p) : 0 < lcltK p := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold lcltK; positivity

theorem lcltN0_one_le (p : ℕ) (hp : 2 ≤ p) : (1 : ℝ) ≤ lcltN0 p := by
  have : 1 ≤ lcltN0 p := Nat.one_le_pow _ _ (by omega)
  exact_mod_cast this

theorem lcltG0_pos {p : ℕ} (hp : 2 ≤ p) : 0 < lcltG0 p := by
  have hσ := sig2_pos hp
  have h1 := lcltN0_one_le p hp
  unfold lcltG0
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- **Large `n`** (`n ≥ (2p)⁵`): `|nb - g| ≤ K e^{2K} g (n^{-1/2} + |d|³/n²)`. -/
theorem lclt_case_large {p : ℕ} (hp : 2 ≤ p) (n s : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht1 : 1 ≤ t)
    (ht5 : t ^ 5 = n) (hs : |(s : ℝ) - muP p * n| ≤ t ^ 3) (hN : lcltN0 p ≤ n) :
    |nb p n s - gauss p n s| ≤ lcltK p * Real.exp (2 * lcltK p) * gauss p n s *
      ((n : ℝ) ^ (-(1 / 2 : ℝ)) + |(s : ℝ) - muP p * n| ^ 3 / (n : ℝ) ^ 2) := by
  set P : ℝ := (p : ℝ) with hPdef
  have hP2 : (2 : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast hp
  have hP1 : (0 : ℝ) < P - 1 := by linarith
  set K := lcltK p with hK
  have hK0 : 0 < K := lcltK_pos hp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n := by linarith
  set d : ℝ := (s : ℝ) - muP p * n with hd
  set D : ℝ := |d| with hD
  have hD0 : 0 ≤ D := abs_nonneg d
  set X : ℝ := D ^ 3 / (n : ℝ) ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  set h : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ)) with hh
  have hh' : h = (√(n : ℝ))⁻¹ := rpow_neg_half_eq _ hn'.le
  have hh0 : 0 ≤ h := by rw [hh']; positivity
  have hinv : 1 / (n : ℝ) ≤ h := by rw [hh']; exact inv_le_inv_sqrt _ hn1
  have hg := gauss_pos hp n hn (s : ℝ)
  set g := gauss p n (s : ℝ) with hgdef
  have hNr : (((2 * p) ^ 5 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN
  have ht2p : 2 * P ≤ t := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) (by linarith)
    rw [ht5]
    calc (2 * P) ^ 5 = (((2 * p) ^ 5 : ℕ) : ℝ) := by rw [hPdef]; push_cast; ring
      _ ≤ n := hNr
  have hsmall : 2 * (P - 1) * D ≤ n := by
    rw [← ht5]
    have h1 : 2 * (P - 1) ≤ t ^ 2 := by nlinarith
    calc 2 * (P - 1) * D ≤ t ^ 2 * t ^ 3 := mul_le_mul h1 hs hD0 (by positivity)
      _ = t ^ 5 := by ring
  have hX1 : X ≤ 1 := by
    rw [hX, div_le_one (by positivity), ← ht5]
    calc D ^ 3 ≤ (t ^ 3) ^ 3 := pow_le_pow_left₀ hD0 hs 3
      _ = t ^ 9 := by ring
      _ ≤ t ^ 10 := pow_le_pow_right₀ ht1 (by norm_num)
      _ = (t ^ 5) ^ 2 := by ring
  have hh1 : h ≤ 1 := by
    rw [hh]; exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hE := lclt_log_large hp n s hn hsmall
  have hY := div_le_inv_sqrt_add (n : ℝ) D hn1 hD0
  rw [← hh', ← hX] at hY
  set E := Real.log (nb p n s) - Real.log g with hEdef
  have hEK : |E| ≤ K * (h + X) := by
    have hP0 : 0 ≤ P := by linarith
    have hY' := mul_le_mul_of_nonneg_left hY hP0
    have hinv' := mul_le_mul_of_nonneg_left hinv (by linarith : 0 ≤ 2 * P)
    have e2 : 2 * P / n = 2 * P * (1 / n) := by ring
    rw [e2] at hE
    have hK' : K = 4 + 4 * (P - 1) ^ 2 + 3 * P := rfl
    have : (4 + 4 * (P - 1) ^ 2) * X + P * (h + X) + 2 * P * h ≤ K * (h + X) := by
      rw [hK']; nlinarith
    linarith
  have hE2 : |E| ≤ 2 * K := by
    calc |E| ≤ K * (h + X) := hEK
      _ ≤ K * 2 := by apply mul_le_mul_of_nonneg_left (by linarith) hK0.le
      _ = 2 * K := by ring
  -- `nb` is positive (since `s > n`)
  have hnbpos : 0 < nb p n s := by
    have hμ : muP p = P / (P - 1) := rfl
    have hsn : (s : ℝ) - n = n / (P - 1) + d := by
      rw [hd, hμ]; field_simp; ring
    have h1 : D ≤ n / (2 * (P - 1)) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hq : n / (P - 1) = 2 * (n / (2 * (P - 1))) := by field_simp
    have hlt : (n : ℝ) < s := by
      have := neg_abs_le d
      have : 0 < n / (2 * (P - 1)) := by positivity
      linarith
    have hns : n < s := by exact_mod_cast hlt
    rw [nb_eq hp n s hn (by omega)]
    have hc : (0 : ℝ) < ((s - 1).choose (n - 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
    positivity
  -- `nb - g = g(e^E - 1)`
  have hnbE : nb p n s = g * Real.exp E := by
    rw [hEdef, Real.exp_sub, Real.exp_log hnbpos, Real.exp_log hg]
    field_simp
  calc |nb p n s - g| = g * |Real.exp E - 1| := by
        rw [hnbE, show g * Real.exp E - g = g * (Real.exp E - 1) by ring, abs_mul,
          abs_of_pos hg]
    _ ≤ g * (|E| * Real.exp |E|) :=
        mul_le_mul_of_nonneg_left (abs_exp_sub_one_le_mul E) hg.le
    _ ≤ g * ((K * (h + X)) * Real.exp (2 * K)) := by
        apply mul_le_mul_of_nonneg_left _ hg.le
        exact mul_le_mul hEK (Real.exp_le_exp.mpr hE2) (Real.exp_pos _).le (by positivity)
    _ = K * Real.exp (2 * K) * g * (h + X) := by ring

/-- **Small `n`** (`n < (2p)⁵`): `|nb - g| ≤ N₀(1/g₀ + 1) g (n^{-1/2} + |d|³/n²)`. -/
theorem lclt_case_small {p : ℕ} (hp : 2 ≤ p) (n s : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht1 : 1 ≤ t)
    (ht5 : t ^ 5 = n) (hs : |(s : ℝ) - muP p * n| ≤ t ^ 3) (hN : n < lcltN0 p) :
    |nb p n s - gauss p n s| ≤ (lcltN0 p : ℝ) * (1 / lcltG0 p + 1) * gauss p n s *
      ((n : ℝ) ^ (-(1 / 2 : ℝ)) + |(s : ℝ) - muP p * n| ^ 3 / (n : ℝ) ^ 2) := by
  have hσ := sig2_pos hp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n := by linarith
  set N0 : ℕ := lcltN0 p with hN0
  have hNr : (n : ℝ) < N0 := by exact_mod_cast hN
  set g0 := lcltG0 p with hg0
  have hg0pos : 0 < g0 := lcltG0_pos hp
  set d : ℝ := (s : ℝ) - muP p * n with hd
  set D : ℝ := |d| with hD
  have hD0 : 0 ≤ D := abs_nonneg d
  set X : ℝ := D ^ 3 / (n : ℝ) ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  set h : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ)) with hh
  have hh' : h = (√(n : ℝ))⁻¹ := rpow_neg_half_eq _ hn'.le
  have hh0 : 0 ≤ h := by rw [hh']; positivity
  have hinv : 1 / (n : ℝ) ≤ h := by rw [hh']; exact inv_le_inv_sqrt _ hn1
  have hg := gauss_pos hp n hn (s : ℝ)
  set g := gauss p n (s : ℝ) with hgdef
  -- `d² ≤ N₀ n`
  have hd2 : d ^ 2 ≤ (N0 : ℝ) * n := by
    have hD2 : D ^ 2 ≤ (t ^ 3) ^ 2 := pow_le_pow_left₀ hD0 hs 2
    have ht : (t ^ 3) ^ 2 ≤ (t ^ 5) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ ht1 (by norm_num)) 2
    rw [ht5] at ht
    have hdD : d ^ 2 = D ^ 2 := by rw [hD, sq_abs]
    have hnn : (n : ℝ) ^ 2 ≤ (N0 : ℝ) * n := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hNr.le hn'.le
    rw [hdD]
    exact hD2.trans (ht.trans hnn)
  have hgg0 : g0 ≤ g := gauss_lb_aux (sig2 p) n N0 d hσ hn' hNr.le hd2
  have hnb0 := nb_nonneg p n s
  have hnb1 := nb_le_one p n s
  have habs : |nb p n s - g| ≤ 1 + g := by
    rw [abs_le]; constructor <;> linarith
  have h1 : 1 ≤ g / g0 := by rw [le_div_iff₀ hg0pos]; linarith
  have hNh : 1 ≤ (N0 : ℝ) * h := by
    have h2 : 1 / (n : ℝ) ≤ h := hinv
    rw [div_le_iff₀ hn'] at h2
    have h3 : h * n ≤ h * N0 := mul_le_mul_of_nonneg_left hNr.le hh0
    linarith
  have hA : 0 ≤ (1 / g0 + 1) * g := by positivity
  calc |nb p n s - g| ≤ 1 + g := habs
    _ ≤ g / g0 + g := by linarith
    _ = (1 / g0 + 1) * g := by field_simp
    _ ≤ (1 / g0 + 1) * g * ((N0 : ℝ) * h) := le_mul_of_one_le_right hA hNh
    _ = (N0 : ℝ) * (1 / g0 + 1) * g * h := by ring
    _ ≤ (N0 : ℝ) * (1 / g0 + 1) * g * (h + X) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        positivity

end LCLTAux

/-! ### Main theorem -/

/-- **(LCLT)**. -/
theorem lclt {p : ℕ} (hp : 2 ≤ p) : lclt_statement p := by
  have hK0 : 0 < lcltK p := lcltK_pos hp
  have hg0 : 0 < lcltG0 p := lcltG0_pos hp
  have hN1 := lcltN0_one_le p hp
  set C1 : ℝ := lcltK p * Real.exp (2 * lcltK p) with hC1
  set C2 : ℝ := (lcltN0 p : ℝ) * (1 / lcltG0 p + 1) with hC2
  have hC1pos : 0 < C1 := mul_pos hK0 (Real.exp_pos _)
  have hC2pos : 0 < C2 := by positivity
  refine ⟨C1 + C2, by linarith, ?_⟩
  intro n hn s hs
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨t, ht1, ht5, ht3⟩ := exists_fifth_root n hn
  rw [ht3] at hs
  have hg := gauss_pos hp n hn (s : ℝ)
  set R : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ)) + |(s : ℝ) - muP p * n| ^ 3 / (n : ℝ) ^ 2 with hRdef
  have hR : 0 ≤ gauss p n s * R := by
    have : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hn'.le _
    positivity
  have key : ∀ c : ℝ, c ≤ C1 + C2 → |nb p n s - gauss p n s| ≤ c * gauss p n s * R →
      |nb p n s - gauss p n s| ≤ (C1 + C2) * gauss p n s * R := by
    intro c hc h
    calc |nb p n s - gauss p n s| ≤ c * gauss p n s * R := h
      _ = c * (gauss p n s * R) := by ring
      _ ≤ (C1 + C2) * (gauss p n s * R) := mul_le_mul_of_nonneg_right hc hR
      _ = (C1 + C2) * gauss p n s * R := by ring
  rcases le_or_gt (lcltN0 p) n with hN | hN
  · exact key C1 (by linarith) (lclt_case_large hp n s hn t ht1 ht5 hs hN)
  · exact key C2 (by linarith) (lclt_case_small hp n s hn t ht1 ht5 hs hN)

end ND

end GGMCollatz
