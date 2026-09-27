import GGMCollatz.NatDen.StarBAux

/-!
# Assembly of (B): the top conversion (Lemma 8.2 of the paper) and the power rate in natural density (Theorem 8.4 of the paper)

`mainB_of_D`: `mainB_statement` from (D.1), (D.2'), the window bound of (A) (`Asm.uniform` in
`Assembly/Uniform.lean`, from GGM Prop. 3.5) and the seed theorem (`Family.seed`).

## Map of the proof

1. **Choice of the window width `α`**: (D.1) and (D.2') hold only for windows with `α ∈ (1, α₀]`, and the one-step
   recursion assumed by `Asm.uniform` holds for windows with `α² < 1 + c`, where `c` is the exponent of Prop. 3.5.
   Take `α := 1 + min(min(c,1)/3, α₁ - 1, α₂ - 1)`; `stepHyp_of_prop35_alpha` (`TopConv.lean`) gives
   `StepHyp F α …`, and `Asm.uniform` gives `P(N₀, y) ≤ K_A N₀^{-c'}` (for all `y > 0`).
2. **The top conversion, Lemma 8.2 of the paper** (`unif_bad_le`, `count_top` in `TopConv.lean`): if `x ≥ X_D` and `N₀ ≤ x`, then
   `#{N ∈ ℕ_p ∩ [1, x^{α²}] | S_min(N) > N₀} ≤ x^α + x^{α²}(K_nh x^{-c_nh} + K_tv (log x)^{-c_tv} + P(N₀, x^α))`.
   First-passage decomposition `P_unif(S_min > N₀) = P_unif(T_x = ∞) + P_unif(Pass_x ∈ A)`; the difference of the
   probabilities of `A` is at most the total variation; on the logarithmic window `P(Pass_x ∈ A) ≤ P(N₀, x^α)`.
   The count is `#W × (uniform probability)`, with `#W ≤ x^{α²}`.
3. **The power rate on `ℕ_p`** (`np_large`, `np_bound`): `L = ⌊log_p N₀⌋`, `v = e^{c_B L/4}`.
   * `X ≤ e^{α² v}`: by the seed (`count_seed`) and `arith_small`, `≤ C_B(α²/log p + 1)² X (L+1)e^{-c₁L}`.
   * `X > e^{α² v}`: apply 2. with `x := X^{1/α²} ≥ e^v ≥ max(X₁, X₂, N₀)`; using `x^{-a} ≤ e^{-av} ≤ a^{-1}e^{-c_B L/4}`
     (`exp_neg_mul_exp_le`) and `(log x)^{-c_tv} ≤ v^{-c_tv}` (`Asm.arith_err`), get `≤ X(A (L+1)e^{-c₁L} + K_A N₀^{-c'})`.
   * If `L` is small (`L ≤ M`), the trivial bound `≤ X`. `(L+1)e^{-c₁L}` is turned into a power of `N₀` by `Asm.rate_to_N0`.
4. **General `N`** (`count_C_le`): `N = p^k N'`, `C_min(N) > N₀ ⇒ S_min(N') > N₀`, giving `∑_k K (X/p^k) N₀^{-c}`,
   and `∑_k p^{-k} ≤ p/(p-1)` (`Asm.sum_inv_pow_le`).

**Choice of parameters** (as in Section 8 of the paper): `v := e^{c_B L/4}`. Since the seed count is
bounded shell by shell using `p^M ≤ X`, a factor of the number of shells survives squared, and this choice absorbs it
(as in `Uniform.lean` for (A)). The rate is `c₁ = c_B min(1/4, c_tv/4)`, and the final exponent is
`min(c₁/(2 log p), c')`.
The paper's window width is "condition (α) and `α² < 1 + c^G`"; here it is chosen by `α ≤ α₀` from the statements of
(D.1) and (D.2') and by `α² < 1 + c` (`c` the exponent of `prop35_statement`).
-/

namespace GGMCollatz

namespace ND

open Asm

variable (F : Family)

open Classical in
/-- **The bound on `ℕ_p`, case of large `L`**. With `v = e^{c_B L/4}`, `e^v ≥ X₁, X₂, N₀` and `X ≥ 1`,
`#{N ∈ ℕ_p ∩ [1, X] | S_min(N) > N₀} ≤ X (A (L+1)e^{-c₁L} + K_A N₀^{-c'})`. -/
theorem np_large {α : ℝ} (hα : 1 < α)
    {cB CB : ℝ} (hcB : 0 < cB) (hCB : 0 ≤ CB) {L₀ : ℕ}
    (hseed : ∀ L M : ℕ, L₀ ≤ L → L ≤ M →
      (((Finset.Ico (F.p ^ M) (F.p ^ (M + 1))).filter
          (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)).card : ℝ)
        ≤ CB * (F.p : ℝ) ^ M * ((M : ℝ) + 1) * ((L : ℝ) + 1) * Real.exp (-(cB * L)))
    {KA c' : ℝ} (hKA : 0 ≤ KA)
    (hU : ∀ N₀ : ℕ, 1 ≤ N₀ → ∀ y : ℝ, 0 < y → F.windowProb α N₀ y ≤ KA * (N₀ : ℝ) ^ (-c'))
    {cnh Knh X₁ : ℝ} (hcnh : 0 < cnh) (hKnh : 0 ≤ Knh)
    (hnh : ∀ x : ℝ, X₁ ≤ x →
      Family.expect (unifWin F (x ^ α) ((x ^ α) ^ α)) (Set.indicator {N | ¬ F.passes ⌊x⌋₊ N} 1)
        ≤ Knh * x ^ (-cnh))
    {ctv Ktv X₂ : ℝ} (hctv : 0 < ctv) (hKtv : 0 ≤ Ktv)
    (htv : ∀ x : ℝ, X₂ ≤ x →
      Family.dTV ((unifWin F (x ^ α) ((x ^ α) ^ α)).map (F.passLoc ⌊x⌋₊))
          ((F.logUnif (x ^ α) ((x ^ α) ^ α)).map (F.passLoc ⌊x⌋₊))
        ≤ Ktv * Real.log x ^ (-ctv))
    {c₁ : ℝ} (hc₁a : c₁ ≤ cB / 4) (hc₁b : c₁ ≤ cB * ctv / 4)
    {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (hL0 : L₀ ≤ Nat.log F.p N₀)
    (hX1v : X₁ ≤ Real.exp (Real.exp (cB * Nat.log F.p N₀ / 4)))
    (hX2v : X₂ ≤ Real.exp (Real.exp (cB * Nat.log F.p N₀ / 4)))
    (hNv : (N₀ : ℝ) ≤ Real.exp (Real.exp (cB * Nat.log F.p N₀ / 4)))
    {X : ℝ} (hX : 1 ≤ X) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N)).card : ℝ) ≤
      X * ((CB * (α ^ 2 / Real.log F.p + 1) ^ 2 + 1 / (α - 1) + Knh / cnh + Ktv) *
        (((Nat.log F.p N₀ : ℝ) + 1) * Real.exp (-(c₁ * Nat.log F.p N₀))) + KA * (N₀ : ℝ) ^ (-c')) := by
  set L := Nat.log F.p N₀ with hLdef
  set v := Real.exp (cB * L / 4) with hvdef
  set R := ((L : ℝ) + 1) * Real.exp (-(c₁ * L)) with hRdef
  set lp := Real.log F.p with hlpdef
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hp1 : 1 < F.p := F.one_lt_p
  have hlp : 0 < lp := Real.log_pos (by linarith)
  have hα1 : 0 < α - 1 := by linarith
  have hα0 : 0 < α := by linarith
  have hL0' : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hv1 : 1 ≤ v := by rw [hvdef]; exact Real.one_le_exp (by positivity)
  have hv0 : 0 < v := by linarith
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hX0 : 0 < X := by linarith
  have hN0pos : (0 : ℝ) < N₀ := by exact_mod_cast (by omega : 0 < N₀)
  have hNc : 0 ≤ KA * (N₀ : ℝ) ^ (-c') := mul_nonneg hKA (Real.rpow_nonneg hN0pos.le _)
  have hT1 : 0 ≤ CB * (α ^ 2 / lp + 1) ^ 2 := by positivity
  have hT2 : 0 ≤ 1 / (α - 1) := by positivity
  have hT3 : 0 ≤ Knh / cnh := div_nonneg hKnh hcnh.le
  -- `e^{-c_B L/4} ≤ R`
  have hrate : Real.exp (-(cB * L / 4)) ≤ R := exp_neg_le_rate hL0' hc₁a
  by_cases hXs : X ≤ Real.exp (α ^ 2 * v)
  · -- (i) small `X`: the seed
    have hc := count_seed F hCB hseed hN₀ hL0 hX0.le
    rw [← hLdef] at hc
    set lm := Nat.log F.p ⌊X⌋₊ with hlm
    have hfl : ⌊X⌋₊ ≠ 0 := by have := Nat.floor_pos.mpr hX; omega
    have hlm' : (lm : ℝ) ≤ α ^ 2 * v / lp := by
      have h1 : F.p ^ lm ≤ ⌊X⌋₊ := Nat.pow_log_le_self F.p hfl
      have h2 : (F.p : ℝ) ^ lm ≤ X := by
        have : ((F.p ^ lm : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h1
        push_cast at this
        exact le_trans this (Nat.floor_le hX0.le)
      have h3 := Real.log_le_log (by positivity) (le_trans h2 hXs)
      rw [Real.log_pow, Real.log_exp] at h3
      rw [le_div_iff₀ hlp]
      linarith
    have ha := arith_small (α := α) (c₁ := c₁) hlp hCB hX0.le hL0' hcB.le (by linarith) (Nat.cast_nonneg lm)
      hlm'
    rw [← hRdef] at ha
    have hAR : CB * (α ^ 2 / lp + 1) ^ 2 * R ≤
        (CB * (α ^ 2 / lp + 1) ^ 2 + 1 / (α - 1) + Knh / cnh + Ktv) * R := by
      apply mul_le_mul_of_nonneg_right _ hR0; linarith
    calc _ ≤ _ := hc
      _ ≤ CB * (α ^ 2 / lp + 1) ^ 2 * X * R := ha
      _ = X * (CB * (α ^ 2 / lp + 1) ^ 2 * R) := by ring
      _ ≤ X * ((CB * (α ^ 2 / lp + 1) ^ 2 + 1 / (α - 1) + Knh / cnh + Ktv) * R +
            KA * (N₀ : ℝ) ^ (-c')) := by
          apply mul_le_mul_of_nonneg_left _ hX0.le; linarith
  · -- (ii) large `X`: the top conversion
    push Not at hXs
    set x := X ^ ((α ^ 2)⁻¹) with hxdef
    have hx0 : 0 < x := Real.rpow_pos_of_pos hX0 _
    have hxX2 : x ^ (α ^ 2) = X := by
      rw [hxdef, ← Real.rpow_mul hX0.le, inv_mul_cancel₀ (by positivity), Real.rpow_one]
    have hxX : (x ^ α) ^ α = X := by
      rw [← Real.rpow_mul hx0.le, ← sq, hxX2]
    have hvx : Real.exp v ≤ x := by
      have hlogX : α ^ 2 * v < Real.log X := by
        rw [Real.lt_log_iff_exp_lt hX0]; exact hXs
      have h1 : v < Real.log x := by
        rw [hxdef, Real.log_rpow hX0, inv_mul_eq_div, lt_div_iff₀ (by positivity)]
        linarith
      exact ((Real.lt_log_iff_exp_lt hx0).mp h1).le
    have hx1 : 1 ≤ x := le_trans (Real.one_le_exp hv0.le) hvx
    have hct := count_top F α x hx0.le hN₀ (le_trans hNv hvx)
    have b1 := hnh x (le_trans hX1v hvx)
    have b2 := htv x (le_trans hX2v hvx)
    have b3 := hU N₀ hN₀ (x ^ α) (Real.rpow_pos_of_pos hx0 _)
    have hY0 : 0 ≤ (x ^ α) ^ α := by positivity
    have hct' := le_trans hct (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add b1 b2) b3) hY0))
    rw [hxX] at hct'
    -- `x^{-a} ≤ a^{-1} R`
    have key : ∀ a : ℝ, 0 < a → x ^ (-a) ≤ (1 / a) * R := by
      intro a ha
      have h1 : x ^ (-a) ≤ (Real.exp v) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos v) hvx (by linarith)
      have h2 : (Real.exp v) ^ (-a) = Real.exp (-(a * Real.exp (cB * L / 4))) := by
        rw [← Real.exp_mul, hvdef]; ring_nf
      have h3 := exp_neg_mul_exp_le ha (cB * L / 4)
      have h4 : (1 / a) * Real.exp (-(cB * L / 4)) ≤ (1 / a) * R :=
        mul_le_mul_of_nonneg_left hrate (by positivity)
      linarith
    -- `x^α ≤ X x^{-(α-1)}`
    have t1 : x ^ α ≤ X * ((1 / (α - 1)) * R) := by
      have e : x ^ α = x ^ (α ^ 2) * x ^ (α - α ^ 2) := by
        rw [← Real.rpow_add hx0]; ring_nf
      have h1 : x ^ (α - α ^ 2) ≤ x ^ (-(α - 1)) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
      rw [e, hxX2]
      exact mul_le_mul_of_nonneg_left (le_trans h1 (key (α - 1) hα1)) hX0.le
    have t2 : Knh * x ^ (-cnh) ≤ Knh / cnh * R := by
      have := mul_le_mul_of_nonneg_left (key cnh hcnh) hKnh
      rw [div_eq_mul_one_div]
      linarith
    have t3 : Ktv * Real.log x ^ (-ctv) ≤ Ktv * R := by
      have hlx : v ≤ Real.log x := by
        rw [Real.le_log_iff_exp_le hx0]; exact hvx
      have h1 : Real.log x ^ (-ctv) ≤ v ^ (-ctv) :=
        Real.rpow_le_rpow_of_nonpos hv0 hlx (by linarith)
      have h2 := arith_err (c := ctv) (KE := 1) (L := (L : ℝ)) zero_le_one hL0' hc₁b
      rw [one_mul, one_mul, ← hvdef] at h2
      exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hKtv
    calc _ ≤ _ := hct'
      _ ≤ X * ((1 / (α - 1)) * R) + X * (Knh / cnh * R + Ktv * R + KA * (N₀ : ℝ) ^ (-c')) := by
          have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add t2 t3) (le_refl
            (KA * (N₀ : ℝ) ^ (-c')))) hX0.le
          linarith
      _ ≤ X * ((CB * (α ^ 2 / lp + 1) ^ 2 + 1 / (α - 1) + Knh / cnh + Ktv) * R +
            KA * (N₀ : ℝ) ^ (-c')) := by
          have h0 : 0 ≤ X * (CB * (α ^ 2 / lp + 1) ^ 2 * R) := by positivity
          have e : X * ((CB * (α ^ 2 / lp + 1) ^ 2 + 1 / (α - 1) + Knh / cnh + Ktv) * R +
              KA * (N₀ : ℝ) ^ (-c')) = X * ((1 / (α - 1)) * R) +
                X * (Knh / cnh * R + Ktv * R + KA * (N₀ : ℝ) ^ (-c')) +
                X * (CB * (α ^ 2 / lp + 1) ^ 2 * R) := by ring
          rw [e]
          linarith

/-- **The power rate in natural density on `ℕ_p`** (the `ℕ_p` part of steps (i)(ii)(iii) of the accompanying paper). -/
theorem np_bound (h1 : noHit_statement F) (h2 : tvPass_statement F) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ N₀ : ℕ, 1 ≤ N₀ → ∀ X : ℝ, 0 ≤ X →
      (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N)).card : ℝ) ≤
        K * X * (N₀ : ℝ) ^ (-c) := by
  classical
  obtain ⟨α₁, hα₁, hD1⟩ := h1
  obtain ⟨α₂, hα₂, hD2⟩ := h2
  obtain ⟨c35, hc35, hstep⟩ := stepHyp_of_prop35_alpha F F.prop35
  -- 1. the window width
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = min (min c35 1 / 3) (min (α₁ - 1) (α₂ - 1)) := ⟨_, rfl⟩
  have hmin0 : 0 < min c35 1 := lt_min hc35 one_pos
  have hm0 : 0 < m := by
    rw [hmdef]
    exact lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hm1 : m ≤ min c35 1 / 3 := by rw [hmdef]; exact min_le_left _ _
  have hmα₁ : m ≤ α₁ - 1 := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmα₂ : m ≤ α₂ - 1 := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hmc : m ≤ c35 / 3 := by
    have := min_le_left c35 1; linarith
  have hm13 : m ≤ 1 / 3 := by
    have := min_le_right c35 1; linarith
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 1 + m := ⟨_, rfl⟩
  have hα : 1 < α := by rw [hαdef]; linarith
  have hαα₁ : α ≤ α₁ := by rw [hαdef]; linarith
  have hαα₂ : α ≤ α₂ := by rw [hαdef]; linarith
  have hα2c : α ^ 2 < 1 + c35 := by rw [hαdef]; nlinarith
  obtain ⟨Cs, hCs, hS⟩ := hstep α hα hα2c
  obtain ⟨KA, c', hKA, hc', hU⟩ := Asm.uniform F hα hc35 hCs hS
  obtain ⟨cnh, Knh, hcnh, hKnh, hev1⟩ := hD1 α hα hαα₁
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp hev1
  obtain ⟨ctv, Ktv, hctv, hKtv, hev2⟩ := hD2 α hα hαα₂
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.mp hev2
  obtain ⟨cB, hcB, CB, hCB, L₀, hseed⟩ := F.seed
  have hp1 : 1 < F.p := F.one_lt_p
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hlp : 0 < Real.log F.p := Real.log_pos (by linarith)
  -- 2. the rate
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = cB * min (1 / 4) (ctv / 4) := ⟨_, rfl⟩
  have hmn0 : 0 < min (1 / 4 : ℝ) (ctv / 4) := lt_min (by norm_num) (by linarith)
  have hc₁ : 0 < c₁ := by rw [hc₁def]; exact mul_pos hcB hmn0
  have hc₁a : c₁ ≤ cB / 4 := by
    have := mul_le_mul_of_nonneg_left (min_le_left (1 / 4 : ℝ) (ctv / 4)) hcB.le
    rw [hc₁def]; linarith
  have hc₁b : c₁ ≤ cB * ctv / 4 := by
    have := mul_le_mul_of_nonneg_left (min_le_right (1 / 4 : ℝ) (ctv / 4)) hcB.le
    rw [hc₁def]; linarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (c₁ / (2 * Real.log F.p)) c' := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact lt_min (by positivity) hc'
  have hcc₁ : c ≤ c₁ / (2 * Real.log F.p) := by rw [hcdef]; exact min_le_left _ _
  have hcc' : c ≤ c' := by rw [hcdef]; exact min_le_right _ _
  -- 3. the constants
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ,
      A = CB * (α ^ 2 / Real.log F.p + 1) ^ 2 + 1 / (α - 1) + Knh / cnh + Ktv := ⟨_, rfl⟩
  have hA : 0 ≤ A := by
    have : 0 < α - 1 := by linarith
    rw [hAdef]; have := div_nonneg hKnh.le hcnh.le; positivity
  obtain ⟨Kbig, hKbig⟩ : ∃ Kbig : ℝ, Kbig = A * ((1 + 2 / c₁) * Real.exp (c₁ / 2)) + KA :=
    ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = max L₀ (max ⌈64 * Real.log F.p / cB ^ 2⌉₊
      ⌈4 * max X₁ X₂ / cB⌉₊) := ⟨_, rfl⟩
  refine ⟨max (max Kbig 1) (((F.p : ℝ) ^ (M + 1)) ^ c), c,
    lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_left _ _)), hc, ?_⟩
  intro N₀ hN₀ X hX
  have hN0pos : (0 : ℝ) < N₀ := by exact_mod_cast (by omega : 0 < N₀)
  have hNpow : 0 < (N₀ : ℝ) ^ (-c) := Real.rpow_pos_of_pos hN0pos _
  set cnt := (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N)).card : ℝ)
    with hcnt
  have hcntX : cnt ≤ X := by
    have h1 := Finset.card_filter_le (Finset.Icc 1 ⌊X⌋₊) (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N)
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    exact le_trans (Nat.cast_le.mpr h1) (Nat.floor_le hX)
  by_cases hsmall : Nat.log F.p N₀ < M + 1
  · -- `L` small: trivial since `N₀ < p^{M+1}`
    exact small_L_bound hp1 hc hN₀ hsmall (le_max_right _ _) hX hcntX
  · push Not at hsmall
    set L := Nat.log F.p N₀ with hLdef
    have hceil : ∀ z : ℝ, ⌈z⌉₊ ≤ M → z ≤ (L : ℝ) := by
      intro z hz
      have h1 : (⌈z⌉₊ : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans hz (by omega)
      linarith [Nat.le_ceil z]
    have hL0 : L₀ ≤ L := by
      have : L₀ ≤ M := by rw [hMdef]; exact le_max_left _ _
      omega
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have hLc := hceil (64 * Real.log F.p / cB ^ 2) (by
      rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _))
    have hLX := hceil (4 * max X₁ X₂ / cB) (by
      rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_right _ _))
    obtain ⟨hXs, hN0v⟩ := exp_thresholds hp1 hcB N₀ hL1 hLc hLX
    -- if `X < 1` the count is 0
    by_cases hX1 : X < 1
    · have hfl : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr hX1
      have h0 : cnt = 0 := by
        rw [hcnt, hfl]; simp
      rw [h0]; positivity
    push Not at hX1
    have hbig := np_large F hα hcB hCB.le hseed hKA.le hU hcnh hKnh.le
      (fun x hx => hX₁ x hx) hctv hKtv.le (fun x hx => hX₂ x hx) hc₁a hc₁b hN₀ hL0
      (le_trans (le_max_left _ _) hXs) (le_trans (le_max_right _ _) hXs) hN0v hX1
    rw [← hAdef] at hbig
    have hin := combine_rate hp1 hA hKA.le hc₁ hcc₁ hcc' hN₀
    rw [← hKbig] at hin
    have hKK : Kbig ≤ max (max Kbig 1) (((F.p : ℝ) ^ (M + 1)) ^ c) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    calc cnt ≤ _ := hbig
      _ ≤ X * (Kbig * (N₀ : ℝ) ^ (-c)) := mul_le_mul_of_nonneg_left hin hX
      _ ≤ X * (max (max Kbig 1) (((F.p : ℝ) ^ (M + 1)) ^ c) * (N₀ : ℝ) ^ (-c)) := by
          gcongr
      _ = _ := by ring

/-- **Assembly of (B)**: from (D.1) and (D.2'). -/
theorem mainB_of_D (h1 : noHit_statement F) (h2 : tvPass_statement F) : F.mainB_statement := by
  classical
  obtain ⟨K, c, hK, hc, hNp⟩ := np_bound F h1 h2
  have hp1 : 1 < F.p := F.one_lt_p
  have hp1' : (1 : ℝ) < F.p := by exact_mod_cast hp1
  have hpp : 0 < (F.p : ℝ) / ((F.p : ℝ) - 1) := div_pos (by linarith) (by linarith)
  refine ⟨K * ((F.p : ℝ) / ((F.p : ℝ) - 1)), c, mul_pos hK hpp, hc, ?_⟩
  intro N₀ hN₀ X hX
  have hX0 : 0 ≤ X := by linarith
  have hN0pos : (0 : ℝ) < N₀ := by exact_mod_cast (by omega : 0 < N₀)
  have hNpow : 0 ≤ (N₀ : ℝ) ^ (-c) := Real.rpow_nonneg hN0pos.le _
  have h1 := count_C_le F N₀ hX0
  have h2 : ∀ k ∈ Finset.range (⌊X⌋₊ + 1),
      (((Finset.Icc 1 ⌊X / (F.p : ℝ) ^ k⌋₊).filter
          (fun N => N % F.p ≠ 0 ∧ N₀ < F.Smin N)).card : ℝ) ≤
        K * X * (N₀ : ℝ) ^ (-c) * ((F.p : ℝ) ^ k)⁻¹ := by
    intro k _
    have hpk : (0 : ℝ) < (F.p : ℝ) ^ k := by have := F.p_pos; positivity
    have := hNp N₀ hN₀ (X / (F.p : ℝ) ^ k) (div_nonneg hX0 hpk.le)
    calc _ ≤ _ := this
      _ = K * X * (N₀ : ℝ) ^ (-c) * ((F.p : ℝ) ^ k)⁻¹ := by rw [div_eq_mul_inv]; ring
  have h3 := sum_inv_pow_le hp1' (⌊X⌋₊ + 1)
  have hKX : 0 ≤ K * X * (N₀ : ℝ) ^ (-c) := by positivity
  calc (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < F.Cmin N)).card : ℝ)
      ≤ _ := h1
    _ ≤ ∑ k ∈ Finset.range (⌊X⌋₊ + 1), K * X * (N₀ : ℝ) ^ (-c) * ((F.p : ℝ) ^ k)⁻¹ :=
        Finset.sum_le_sum h2
    _ = K * X * (N₀ : ℝ) ^ (-c) * ∑ k ∈ Finset.range (⌊X⌋₊ + 1), ((F.p : ℝ) ^ k)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ K * X * (N₀ : ℝ) ^ (-c) * ((F.p : ℝ) / ((F.p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left h3 hKX
    _ = K * ((F.p : ℝ) / ((F.p : ℝ) - 1)) * X * (N₀ : ℝ) ^ (-c) := by ring

end ND

end GGMCollatz
