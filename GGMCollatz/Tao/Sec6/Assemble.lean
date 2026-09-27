import GGMCollatz.Tao.Sec6.Step

/-!
# Proposition 5.1 ⇒ polynomial decay of the oscillation between adjacent levels (assembly of GGM §5 Step 1)

Derived from `TaoCollatz/Sec6/MixingMain.lean` (`osc_mainHigh_bound_at`) and
`TaoCollatz/Sec6/MixingFromDecay.lean` (`osc_syracZ_high_regime_at`) of gotrevor/tao-collatz
(Apache-2.0), commit 15efca2; generalized to the GGM family (p, q, r).

`osc_step_bound`: under Proposition 5.1, for every `B > 0` there are `C` and `N₀` such that for `N ≥ N₀`,
`Osc_{N-1,N}(𝒮_N) ≤ C N^{-B}`. Choice of constants (`L = log N`, `θ = log_p q < s < μ`):

* component cap `K_c = K₁ L`, window margin `K_w = K₂ L`, threshold `T = Nθ - K₃ L` (`K₃ = K₁ + K₂ + 1`).
* error: `P(¬globalGood) ≤ N p e^{-(B+2)L} + N e^{-(B+2)L}` (`K₁ = (B+2)/log p`, `K₂ = (B+2)/t`).
* main term: each piece `≤ C_{A'} j^{-A'} √(q^N p^{-l}) ≤ C_{A'} (δ₀N/2)^{-A'} N^{K₃ log p / 2}`
  (`j = N - 1 - k ≥ δ₀N/2`, `δ₀ = 1 - θ/s`), number of pieces `≤ N (K_c + 1)`, `A' = B + 2 + K₃ log p / 2`.
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- `(N : ℝ)^x = e^{x log N}` (`N ≥ 1`). -/
theorem natCast_rpow_eq_exp_mix {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    (N : ℝ) ^ x = Real.exp (x * Real.log N) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hN), mul_comm]

open Classical in
/-- **Proposition 5.1 ⇒ decay of the oscillation between adjacent levels** (GGM §5 Step 1). -/
theorem osc_step_bound (h51 : F.prop51_statement) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      F.osc (N - 1) N (Nat.sub_le N 1) (fun Y => ((F.syracZ N) Y).toReal)
        ≤ C * (N : ℝ) ^ (-B) := by
  -- constants
  set s : ℝ := F.sMix with hsdef
  have hs0 : 0 < s := F.sMix_pos
  obtain ⟨t, ht0, hmgf⟩ := F.geomP_mgf_lower s hs0 F.sMix_lt_muMix
  set lp : ℝ := Real.log (F.p : ℝ) with hlpdef
  have hlp : 0 < lp := F.log_p_pos_mix
  set θ : ℝ := F.thetaMix with hθdef
  have hθ1 : 1 < θ := F.one_lt_thetaMix
  have hθs : θ < s := F.thetaMix_lt_sMix
  set K₁ : ℝ := (B + 2) / lp with hK₁
  set K₂ : ℝ := (B + 2) / t with hK₂
  have hK₁0 : 0 < K₁ := by positivity
  have hK₂0 : 0 < K₂ := by positivity
  set K₃ : ℝ := K₁ + K₂ + 1 with hK₃
  have hK₃0 : 0 < K₃ := by positivity
  set δ₀ : ℝ := 1 - θ / s with hδ₀
  have hδ₀0 : 0 < δ₀ := by
    rw [hδ₀, sub_pos, div_lt_one hs0]; exact hθs
  set A' : ℝ := B + 2 + K₃ * lp / 2 with hA'
  have hA'0 : 0 < A' := by positivity
  obtain ⟨Cd, hCd, hdec⟩ := h51 A' hA'0
  set ρ : ℝ := (F.q : ℝ) / (F.p : ℝ) ^ s with hρdef
  have hρ : (F.q : ℝ) < (F.p : ℝ) ^ s := F.q_lt_p_rpow_sMix
  have hps0 : 0 < (F.p : ℝ) ^ s := Real.rpow_pos_of_pos F.pCast_pos s
  have h1ρ : 0 < 1 - ρ := by rw [hρdef, sub_pos, div_lt_one hps0]; exact hρ
  set Br : ℝ := (F.rBound : ℝ) with hBr
  have hBr0 : 0 ≤ Br := by rw [hBr]; exact_mod_cast F.rBound_nonneg
  set ε : ℝ := (1 - ρ) / (2 * Br + 1) with hεdef
  have hε0 : 0 < ε := by positivity
  have hBrε : 2 * Br * ε < 1 - ρ := by
    rw [hεdef, mul_div_assoc', div_lt_iff₀ (by positivity)]
    have h : (1 - ρ) * (2 * Br + 1) = 2 * Br * (1 - ρ) + (1 - ρ) := by ring
    linarith
  set Cmain : ℝ := (K₁ + 1) * Cd * (δ₀ / 2) ^ (-A') with hCmain
  set Cerr : ℝ := 2 * ((F.p : ℝ) + 1) with hCerr
  have hCmain0 : 0 < Cmain := by positivity
  have hCerr0 : 0 < Cerr := by rw [hCerr]; linarith [F.pCast_pos]
  -- `N₀`
  set N₀ : ℕ := max (max ⌈(2 / (θ / (2 * K₃))) ^ 2⌉₊ ⌈Real.exp (1 / (lp * ε))⌉₊)
    (max ⌈2 / δ₀⌉₊ 1) with hN₀
  refine ⟨Cmain + Cerr, by linarith, N₀, fun N hN => ?_⟩
  have hNa' : ⌈(2 / (θ / (2 * K₃))) ^ 2⌉₊ ≤ N :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNb' : ⌈Real.exp (1 / (lp * ε))⌉₊ ≤ N :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNc' : ⌈2 / δ₀⌉₊ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hNa : (2 / (θ / (2 * K₃))) ^ 2 ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hNa')
  have hNb : Real.exp (1 / (lp * ε)) ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hNb')
  have hNc : 2 / δ₀ ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hNc')
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set L : ℝ := Real.log (N : ℝ) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hNR
  have hLN : L ≤ (N : ℝ) := by
    have := Real.log_le_sub_one_of_pos hN0; linarith
  -- (a) `K₃ L < θ N`
  have hlogθ : K₃ * L < θ * N := by
    have h := Mix.log_le_mul_self (c := θ / (2 * K₃)) (by positivity) hNa
    rw [← hLdef] at h
    have h2 : K₃ * L ≤ θ * N / 2 := by
      calc K₃ * L ≤ K₃ * (θ / (2 * K₃) * N) := mul_le_mul_of_nonneg_left h hK₃0.le
        _ = θ * N / 2 := by field_simp
    have : 0 < θ * N := by positivity
    linarith
  -- (b) `2 Br e^{-lp L} < 1 - ρ`
  have hexpL : 2 * Br * Real.exp (-(lp * L)) < 1 - ρ := by
    have hL : 1 / (lp * ε) ≤ L := by
      rw [hLdef, Real.le_log_iff_exp_le hN0]; exact hNb
    have h := Mix.exp_neg_le_of_ge hlp hε0 hL
    calc 2 * Br * Real.exp (-(lp * L)) ≤ 2 * Br * ε := mul_le_mul_of_nonneg_left h (by positivity)
      _ < 1 - ρ := hBrε
  -- (c) `δ₀ N ≥ 2`
  have hδN : 2 ≤ δ₀ * N := by
    rw [div_le_iff₀ hδ₀0] at hNc; linarith
  -- constants of the events
  set T : ℝ := N * θ - K₃ * L with hTdef
  have hT0 : 0 < T := by rw [hTdef]; linarith
  set Kc : ℝ := K₁ * L with hKc
  set Kw : ℝ := K₂ * L with hKw
  have hKc0 : 0 ≤ Kc := by positivity
  have hKw0 : 0 ≤ Kw := by positivity
  set Kset : Finset ℕ := (Finset.range N).filter (fun k => s * k < T + Kw) with hKset
  set Lset : Finset ℕ := Finset.Ioc ⌊T⌋₊ ⌊T + Kc⌋₊ with hLset
  set S : Finset (ℕ × ℕ) := Kset ×ˢ Lset with hS
  set main := F.mainDensity N (ggmW T s Kw) S with hmain
  have hcross : T ≤ s * N - Kw := by
    have h1 : (N : ℝ) * θ ≤ s * N := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hθs.le hN0.le
    have h2 : K₂ * L ≤ K₃ * L := mul_le_mul_of_nonneg_right (by rw [hK₃]; linarith) hL0
    rw [hTdef, hKw]; linarith
  -- splitting
  refine le_trans (F.osc_syracZ_split_le (N - 1) N (Nat.sub_le N 1) main) ?_
  -- the error term
  have herr : 2 * ∑ Y, |(F.syracZ N Y).toReal - main Y| ≤ Cerr * (N : ℝ) ^ (-B) := by
    rw [hmain, F.sum_abs_syracZ_sub_main_eq]
    have hPsum : Summable fun v : Fin N → ℕ × ℕ => (((stepLaw F.p).iid N) v).toReal :=
      ENNReal.summable_toReal ((stepLaw F.p).iid N).tsum_coe_ne_top
    have hmask : ∀ (Q : (Fin N → ℕ × ℕ) → Prop) [DecidablePred Q],
        Summable (fun v => if Q v then (0 : ℝ) else (((stepLaw F.p).iid N) v).toReal) := by
      intro Q _
      exact Summable.of_nonneg_of_le (fun v => by split_ifs <;> simp)
        (fun v => by split_ifs <;> simp) hPsum
    have hmono : (∑' v : Fin N → ℕ × ℕ, if mainEvent N T s Kw S v then 0
          else (((stepLaw F.p).iid N) v).toReal)
        ≤ ∑' v : Fin N → ℕ × ℕ, if globalGood N s Kc Kw v then 0
          else (((stepLaw F.p).iid N) v).toReal := by
      refine (hmask _).tsum_le_tsum (fun v => ?_) (hmask _)
      by_cases hg : globalGood N s Kc Kw v
      · obtain ⟨k, l, hkN, hk, hTl, hlT, hpiece⟩ := globalGood_piece N T s Kc Kw v hT0 hKw0
          hcross hg
        have hmem : (k, l) ∈ S := by
          rw [hS, Finset.mem_product]
          refine ⟨?_, ?_⟩
          · rw [hKset, Finset.mem_filter, Finset.mem_range]; exact ⟨hkN, hk⟩
          · rw [hLset, Finset.mem_Ioc]
            exact ⟨(Nat.floor_lt hT0.le).mpr hTl, (Nat.le_floor_iff (by linarith)).mpr hlT⟩
        rw [if_pos ⟨(k, l), hmem, hpiece⟩, if_pos hg]
      · rw [if_neg hg]
        split_ifs <;> simp
    have hprob := F.prob_not_globalGood_le N s t Kc Kw ht0.le hmgf hKc0
    have hx₁ : Kc * lp = (B + 2) * L := by rw [hKc, hK₁]; field_simp
    have hx₂ : t * Kw = (B + 2) * L := by rw [hKw, hK₂]; field_simp
    rw [hx₁, hx₂] at hprob
    have hNexp : (N : ℝ) = Real.exp L := (Real.exp_log hN0).symm
    have hbound : (N : ℝ) * ((F.p : ℝ) * Real.exp (-((B + 2) * L)))
        + N * Real.exp (-((B + 2) * L)) ≤ ((F.p : ℝ) + 1) * Real.exp (-(B * L)) := by
      have h1 : (N : ℝ) * Real.exp (-((B + 2) * L)) ≤ Real.exp (-(B * L)) := by
        rw [hNexp, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : L + -((B + 2) * L) = -(B * L) - L := by ring
        rw [this]; linarith
      have h2 := mul_le_mul_of_nonneg_left h1 F.pCast_pos.le
      calc (N : ℝ) * ((F.p : ℝ) * Real.exp (-((B + 2) * L))) + N * Real.exp (-((B + 2) * L))
          = (F.p : ℝ) * ((N : ℝ) * Real.exp (-((B + 2) * L)))
            + N * Real.exp (-((B + 2) * L)) := by ring
        _ ≤ (F.p : ℝ) * Real.exp (-(B * L)) + Real.exp (-(B * L)) := add_le_add h2 h1
        _ = ((F.p : ℝ) + 1) * Real.exp (-(B * L)) := by ring
    rw [natCast_rpow_eq_exp_mix hN1]
    rw [show -B * L = -(B * L) by ring]
    calc 2 * (∑' v : Fin N → ℕ × ℕ, if mainEvent N T s Kw S v then 0
          else (((stepLaw F.p).iid N) v).toReal)
        ≤ 2 * (((F.p : ℝ) + 1) * Real.exp (-(B * L))) := by linarith
      _ = Cerr * Real.exp (-(B * L)) := by rw [hCerr]; ring
  -- the main term
  have hmainb : F.osc (N - 1) N (Nat.sub_le N 1) main ≤ Cmain * (N : ℝ) ^ (-B) := by
    set U : ℝ := Cd * (δ₀ * N / 2) ^ (-A') * Real.exp (K₃ * L * lp / 2) with hU
    have hU0 : 0 ≤ U := by positivity
    have hterm : ∀ kl ∈ S, ∀ hkn : kl.1 < N,
        F.osc (N - 1) (N - 1 - kl.1 + (kl.1 + 1)) (by rw [cutEq hkn]; exact Nat.sub_le N 1)
          (F.condDensW (N - 1 - kl.1) (kl.1 + 1) kl.2 (ggmW T s Kw kl.1 kl.2)) ≤ U := by
      rintro ⟨k, l⟩ hkl hkn
      simp only at hkn ⊢
      rw [hS, Finset.mem_product, hKset, Finset.mem_filter, Finset.mem_range, hLset,
        Finset.mem_Ioc] at hkl
      obtain ⟨⟨_, hk⟩, hl1, hl2⟩ := hkl
      have hTl : T < (l : ℝ) := (Nat.floor_lt hT0.le).mp hl1
      have hlT : (l : ℝ) ≤ T + Kc := (Nat.le_floor_iff (by linarith)).mp hl2
      -- length of the head
      set j : ℕ := N - 1 - k with hjdef
      have hjR : (j : ℝ) = N - 1 - k := by
        rw [hjdef, Nat.cast_sub (by omega), Nat.cast_sub hN1]; simp
      have hkθ : (k : ℝ) < N * θ / s := by
        rw [lt_div_iff₀ hs0]
        have hK₁L : 0 ≤ K₁ * L := mul_nonneg hK₁0.le hL0
        have : T + Kw ≤ N * θ := by
          rw [hTdef, hKw, hK₃]
          have : (N : ℝ) * θ - (K₁ + K₂ + 1) * L + K₂ * L = N * θ - K₁ * L - L := by ring
          rw [this]; linarith
        linarith
      have hjδ : δ₀ * N / 2 ≤ (j : ℝ) := by
        rw [hjR]
        have h1 : (N : ℝ) * θ / s = N * (1 - δ₀) := by rw [hδ₀]; field_simp; ring
        rw [h1] at hkθ
        have : (N : ℝ) * (1 - δ₀) = N - δ₀ * N := by ring
        rw [this] at hkθ
        linarith
      have hj1 : 1 ≤ j := by
        have : (1 : ℝ) ≤ j := by linarith
        exact_mod_cast this
      have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
      -- budget
      have hbudget : 2 * (F.rBound : ℝ) * (F.p : ℝ) ^ ((l : ℝ) + Kw)
          < (1 - (F.q : ℝ) / (F.p : ℝ) ^ s) * (F.q : ℝ) ^ N := by
        have hpow : (F.p : ℝ) ^ ((l : ℝ) + Kw)
            ≤ (F.q : ℝ) ^ N * Real.exp (-(lp * L)) := by
          rw [F.p_rpow_eq_exp_mix, F.q_pow_eq_exp_mix, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          rw [← hlpdef, ← hθdef]
          have : (l : ℝ) + Kw ≤ N * θ - L := by
            rw [hKw]; rw [hTdef, hKc, hK₃] at hlT
            have : (N : ℝ) * θ - (K₁ + K₂ + 1) * L + K₁ * L + K₂ * L = N * θ - L := by ring
            linarith
          have h := mul_le_mul_of_nonneg_right this hlp.le
          have : (N * θ - L) * lp = N * θ * lp + -(lp * L) := by ring
          linarith
        have hq0 : 0 < (F.q : ℝ) ^ N := pow_pos F.qCast_pos N
        calc 2 * (F.rBound : ℝ) * (F.p : ℝ) ^ ((l : ℝ) + Kw)
            ≤ 2 * Br * ((F.q : ℝ) ^ N * Real.exp (-(lp * L))) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = (2 * Br * Real.exp (-(lp * L))) * (F.q : ℝ) ^ N := by ring
          _ < (1 - ρ) * (F.q : ℝ) ^ N := mul_lt_mul_of_pos_right hexpL hq0
      -- decay of the head
      set D : ℝ := Cd * (j : ℝ) ^ (-A') with hDdef
      have hD0 : 0 ≤ D := by positivity
      have hunif : ∀ ξ : ZMod (F.q ^ (N - 1 - k + (k + 1))), ¬ F.q ∣ ξ.val →
          ‖((stepLaw F.p).iid (N - 1 - k)).cexpect (fun vh => ZMod.stdAddChar
              (-(((F.q : ZMod (F.q ^ (N - 1 - k + (k + 1)))) ^ (k + 1)
                * F.roff (N - 1 - k + (k + 1)) vh
                * ((F.p : ZMod (F.q ^ (N - 1 - k + (k + 1))))⁻¹) ^ l) * ξ)))‖ ≤ D := by
        intro ξ hξ
        rw [F.head_factor_eq_charFn (j := N - 1 - k) (P := k + 1) l ξ]
        exact hdec j hj1 _ (F.not_dvd_val_unit_castHom hj1 l ξ hξ)
      have hpiece := F.osc_piece_le N k l hkn T s Kw hs0.le hρ hbudget D hD0 hunif
        (by rw [cutEq hkn]; exact Nat.sub_le N 1)
      refine le_trans hpiece ?_
      -- `D √(q^N p^{-l}) ≤ U`
      have hDle : D ≤ Cd * (δ₀ * N / 2) ^ (-A') := by
        rw [hDdef]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hjδ (by linarith)) hCd.le
      have hsq : Real.sqrt ((F.q : ℝ) ^ N * ((F.p : ℝ)⁻¹) ^ l)
          ≤ Real.exp (K₃ * L * lp / 2) := by
        have hinner : (F.q : ℝ) ^ N * ((F.p : ℝ)⁻¹) ^ l ≤ Real.exp (K₃ * L * lp) := by
          rw [F.q_pow_eq_exp_mix, inv_pow, ← Real.exp_log (pow_pos F.pCast_pos l),
            Real.log_pow, ← Real.exp_neg, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          rw [← hlpdef, ← hθdef]
          have : N * θ - K₃ * L < l := by rw [← hTdef]; exact hTl
          have h := mul_le_mul_of_nonneg_right this.le hlp.le
          have e1 : (N * θ - K₃ * L) * lp = N * θ * lp - K₃ * L * lp := by ring
          have e2 : (l : ℝ) * lp = (l : ℕ) * Real.log F.p := by rw [hlpdef]
          linarith
        calc Real.sqrt ((F.q : ℝ) ^ N * ((F.p : ℝ)⁻¹) ^ l)
            ≤ Real.sqrt (Real.exp (K₃ * L * lp)) := Real.sqrt_le_sqrt hinner
          _ = Real.exp (K₃ * L * lp / 2) := by
            rw [show Real.exp (K₃ * L * lp / 2) = Real.sqrt (Real.exp (K₃ * L * lp / 2)
                * Real.exp (K₃ * L * lp / 2)) from
                (Real.sqrt_mul_self (Real.exp_pos _).le).symm, ← Real.exp_add, add_halves]
      calc D * Real.sqrt ((F.q : ℝ) ^ N * ((F.p : ℝ)⁻¹) ^ l)
          ≤ (Cd * (δ₀ * N / 2) ^ (-A')) * Real.exp (K₃ * L * lp / 2) :=
            mul_le_mul hDle hsq (Real.sqrt_nonneg _) (by positivity)
        _ = U := by rw [hU]
    have hosc := F.osc_mainDensity_le N (N - 1) (Nat.sub_le N 1) (ggmW T s Kw) S
      (fun _ => U) hterm (fun _ _ => hU0)
    refine le_trans hosc ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    -- number of pieces
    have hcardK : (Kset.card : ℝ) ≤ N := by
      have : Kset.card ≤ N := by
        rw [hKset]; exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])
      exact_mod_cast this
    have hcardL : (Lset.card : ℝ) ≤ Kc + 1 := by
      rw [hLset, Nat.card_Ioc]
      have hmono : ⌊T⌋₊ ≤ ⌊T + Kc⌋₊ := Nat.floor_mono (by linarith)
      rw [Nat.cast_sub hmono]
      have h1 : (⌊T + Kc⌋₊ : ℝ) ≤ T + Kc := Nat.floor_le (by linarith)
      have h2 : T - 1 < (⌊T⌋₊ : ℝ) := by have := Nat.lt_floor_add_one T; linarith
      linarith
    have hcardS : (S.card : ℝ) ≤ (K₁ + 1) * (N : ℝ) ^ 2 := by
      rw [hS, Finset.card_product, Nat.cast_mul]
      calc (Kset.card : ℝ) * Lset.card ≤ N * (Kc + 1) :=
            mul_le_mul hcardK hcardL (Nat.cast_nonneg _) (by positivity)
        _ ≤ (K₁ + 1) * (N : ℝ) ^ 2 := by
            rw [hKc]
            have h1 : K₁ * L ≤ K₁ * N := mul_le_mul_of_nonneg_left hLN hK₁0.le
            have h2 : (N : ℝ) * (K₁ * L + 1) ≤ N * (K₁ * N + N) :=
              mul_le_mul_of_nonneg_left (by linarith) hN0.le
            calc (N : ℝ) * (K₁ * L + 1) ≤ N * (K₁ * N + N) := h2
              _ = (K₁ + 1) * (N : ℝ) ^ 2 := by ring
    -- computing the exponent
    have hrpow : (δ₀ * N / 2) ^ (-A') = (δ₀ / 2) ^ (-A') * (N : ℝ) ^ (-A') := by
      rw [show δ₀ * N / 2 = (δ₀ / 2) * N by ring, Real.mul_rpow (by positivity) hN0.le]
    have hexp : (N : ℝ) ^ 2 * ((N : ℝ) ^ (-A') * Real.exp (K₃ * L * lp / 2))
        = (N : ℝ) ^ (-B) := by
      rw [natCast_rpow_eq_exp_mix hN1, natCast_rpow_eq_exp_mix hN1,
        show (N : ℝ) ^ 2 = Real.exp (2 * L) by
          rw [show 2 * L = (2 : ℕ) * L by norm_num, Real.exp_nat_mul, Real.exp_log hN0],
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hA']; ring
    calc (S.card : ℝ) * U
        ≤ (K₁ + 1) * (N : ℝ) ^ 2 * U := mul_le_mul_of_nonneg_right hcardS hU0
      _ = Cmain * ((N : ℝ) ^ 2 * ((N : ℝ) ^ (-A') * Real.exp (K₃ * L * lp / 2))) := by
          rw [hU, hrpow, hCmain]; ring
      _ = Cmain * (N : ℝ) ^ (-B) := by rw [hexp]
  calc F.osc (N - 1) N (Nat.sub_le N 1) main + 2 * ∑ Y, |(F.syracZ N Y).toReal - main Y|
      ≤ Cmain * (N : ℝ) ^ (-B) + Cerr * (N : ℝ) ^ (-B) := add_le_add hmainb herr
    _ = (Cmain + Cerr) * (N : ℝ) ^ (-B) := by ring

end Family

end GGMCollatz
