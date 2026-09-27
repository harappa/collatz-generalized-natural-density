/- Portions Copyright (c) 2026 Idris Ali Shaik (FirstPassageLinearTransport, Apache License 2.0).
   Modified: generalized to the maps of Goncalves, Greenfeld and Madrid. See NOTICE. -/
import GGMCollatz.Seed.Potential
import GGMCollatz.Seed.Fiber

/-!
# Seed (Theorem 4.1 of the paper), part 4: the chain and the counting

The chain, direct passage and counting, and item 5 of the seed argument in the accompanying paper.
The counterparts of `FirstPassage` and `RecertificationRun` of Idris Ali Shaik's
`FirstPassageLinearTransport` (Apache-2.0), and of the assembly in this project's `FixedBarrier.lean`,
rewritten and generalized to the GGM family.

Deviation from the accompanying paper (changes that give the same conclusion more briefly):

* The stage threshold is `p^m` (the lower end of the shell `I_m`) instead of `p^{⌊r^{Sh} m⌋}`. Each
  stage descends by one shell. The condition for a good point is `C~^m(n) < p^m` (the complement of
  `bad`), and only the upper envelope is used.
* The loss is estimated by a crude upper bound (time `≤ M^2`) instead of a telescoping sum over the
  stage thresholds. The polynomial factor is absorbed in the final case distinction (trivial if
  `M + 1 ≥ e^{cL}`).

* `chain`: if the orbit of `n ∈ I_m` stays `≥ p^L` forever, then for some `j ∈ [L, m]` and time
  `t ≤ m^2`, `C~^t(n) ∈ bad j`, and before `t` the orbit stays `≥ p^{j+1}` (direct passage).
* `count_le`: `#{n ∈ I_M | the orbit stays ≥ p^L forever} ≤ K(1+4R)/(1-ξ) (M+1)^6 p^M ξ^L`.
-/

namespace GGMCollatz

namespace Family

variable (F : Family)

open Finset

/-- Chain: the first bad point of the sequence of first passages descending one shell at a time. -/
theorem chain {L : ℕ} (hL : (F.Rb : ℝ) ≤ ((F.q : ℝ) - F.p) * (F.p : ℝ) ^ L) :
    ∀ m n, F.p ^ m ≤ n → n < F.p ^ (m + 1) → (∀ k, F.p ^ L ≤ F.Ct^[k] n) →
      ∃ j, L ≤ j ∧ j ≤ m ∧ ∃ t ≤ m ^ 2,
        F.Ct^[t] n ∈ F.bad j ∧ ∀ k < t, F.p ^ (j + 1) ≤ F.Ct^[k] n := by
  have hp1 : 1 < F.p := F.one_lt_p
  have hp0 : 0 < F.p := F.p_pos
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n hlo hhi horb
  have h0 : F.p ^ L ≤ n := by simpa using horb 0
  have hLm : L ≤ m := by
    have : F.p ^ L < F.p ^ (m + 1) := lt_of_le_of_lt h0 hhi
    have := (Nat.pow_lt_pow_iff_right hp1).1 this
    omega
  by_cases hbad : F.p ^ m ≤ F.Ct^[m] n
  · refine ⟨m, hLm, le_refl m, 0, Nat.zero_le _, ?_, ?_⟩
    · simpa [F.mem_bad] using ⟨⟨hlo, hhi⟩, hbad⟩
    · intro k hk; omega
  rw [not_le] at hbad
  classical
  have hex : ∃ h, F.Ct^[h] n < F.p ^ m := ⟨m, hbad⟩
  obtain ⟨h, hhdef⟩ : ∃ h, h = Nat.find hex := ⟨_, rfl⟩
  have hh_spec : F.Ct^[h] n < F.p ^ m := by rw [hhdef]; exact Nat.find_spec hex
  have hh_le : h ≤ m := by rw [hhdef]; exact Nat.find_min' hex hbad
  have hh_min : ∀ k < h, F.p ^ m ≤ F.Ct^[k] n := by
    intro k hk
    have := Nat.find_min hex (by rw [← hhdef]; exact hk)
    exact not_lt.1 this
  have hh0 : h ≠ 0 := by
    intro h0; rw [h0] at hh_spec; simp at hh_spec; omega
  obtain ⟨h', hh'⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  -- The last step is a division step
  set x := F.Ct^[h'] n with hx
  have hxm : F.p ^ m ≤ x := hh_min h' (by omega)
  have hCtx : F.Ct x = F.Ct^[h] n := by rw [hh', Function.iterate_succ_apply']
  have hxdiv : x % F.p = 0 := by
    by_contra hne
    have hgrow : x ≤ F.Ct x := by
      apply F.le_Ct_of_mod_ne_zero hne
      have hpL : (F.p : ℝ) ^ L ≤ (x : ℝ) := by
        have : F.p ^ L ≤ x := le_trans (Nat.pow_le_pow_right hp0 hLm) hxm
        exact_mod_cast this
      have hqp : (0 : ℝ) ≤ (F.q : ℝ) - F.p := by
        have : (F.p : ℝ) < F.q := by exact_mod_cast F.p_lt_q
        linarith
      have := mul_le_mul_of_nonneg_left hpL hqp
      linarith
    rw [hCtx] at hgrow
    omega
  set n' := F.Ct^[h] n with hn'
  have hn'orb : ∀ k, F.p ^ L ≤ F.Ct^[k] n' := by
    intro k
    have := horb (k + h)
    rwa [Function.iterate_add_apply] at this
  have hn'L : F.p ^ L ≤ n' := by simpa using hn'orb 0
  have hLm' : L < m := by
    have : F.p ^ L < F.p ^ m := lt_of_le_of_lt hn'L hh_spec
    exact (Nat.pow_lt_pow_iff_right hp1).1 this
  have hn'lo : F.p ^ (m - 1) ≤ n' := by
    rw [← hCtx, F.Ct_of_mod_eq_zero hxdiv]
    apply (Nat.le_div_iff_mul_le hp0).2
    rw [← pow_succ, show m - 1 + 1 = m by omega]
    exact hxm
  have hn'hi : n' < F.p ^ (m - 1 + 1) := by
    rw [show m - 1 + 1 = m by omega]; exact hh_spec
  obtain ⟨j, hLj, hjm, t', ht', hbadj, hk'⟩ :=
    ih (m - 1) (by omega) n' hn'lo hn'hi hn'orb
  refine ⟨j, hLj, by omega, t' + h, ?_, ?_, ?_⟩
  · have : (m - 1) ^ 2 + m ≤ m ^ 2 := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith
    have : t' ≤ (m - 1) ^ 2 := ht'
    omega
  · rw [Function.iterate_add_apply]; exact hbadj
  · intro k hk
    by_cases hkh : k < h
    · have := hh_min k hkh
      exact le_trans (Nat.pow_le_pow_right hp0 (by omega)) this
    · have := hk' (k - h) (by omega)
      rw [hn', ← Function.iterate_add_apply, show k - h + h = k by omega] at this
      exact this

/-- Counting (the counting in the accompanying paper): split according to the first bad point of the
chain, and bound by the number of elements of the fibres and the density of the bad set. -/
theorem count_le {ξ K : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hK : 0 ≤ K)
    (hbad : ∀ m, ((F.bad m).card : ℝ) ≤ K * (F.p : ℝ) ^ m * ξ ^ m) {L M : ℕ}
    (hL3 : (F.Rb : ℝ) ≤ (F.p : ℝ) ^ L) (hL2 : 4 * (M : ℝ) ^ 2 * F.Rb ≤ (F.p : ℝ) ^ (L + 2))
    [DecidablePred (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)] :
    (((Ico (F.p ^ M) (F.p ^ (M + 1))).filter (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n)).card : ℝ)
      ≤ K * (1 + 4 * F.Rb) / (1 - ξ) * ((M : ℝ) + 1) ^ 6 * (F.p : ℝ) ^ M * ξ ^ L := by
  classical
  have hp2 : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hp : (0 : ℝ) < F.p := by linarith
  have hp1r : (1 : ℝ) ≤ F.p := by linarith
  have hR0 : (0 : ℝ) ≤ F.Rb := by positivity
  have hqp : (1 : ℝ) ≤ (F.q : ℝ) - F.p := by
    have : F.p + 1 ≤ F.q := F.p_lt_q
    have : ((F.p + 1 : ℕ) : ℝ) ≤ F.q := by exact_mod_cast this
    push_cast at this; linarith
  have hL1 : (F.Rb : ℝ) ≤ ((F.q : ℝ) - F.p) * (F.p : ℝ) ^ L := by
    have : (F.p : ℝ) ^ L ≤ ((F.q : ℝ) - F.p) * (F.p : ℝ) ^ L := by
      have := pow_nonneg hp.le L
      nlinarith
    linarith
  set S := (Ico (F.p ^ M) (F.p ^ (M + 1))).filter (fun n => ∀ k, F.p ^ L ≤ F.Ct^[k] n) with hS
  -- Fibres
  let Fib : ℕ → ℕ → ℕ → Finset ℕ := fun j t y =>
    (Ico (F.p ^ M) (F.p ^ (M + 1))).filter
      (fun n => F.Ct^[t] n = y ∧ ∀ k < t, F.p ^ (j + 1) ≤ F.Ct^[k] n)
  have hsub : S ⊆ (Icc L M).biUnion (fun j => (range (M ^ 2 + 1)).biUnion
      (fun t => (F.bad j).biUnion (fun y => Fib j t y))) := by
    intro n hn
    rw [hS, mem_filter, mem_Ico] at hn
    obtain ⟨⟨hlo, hhi⟩, horb⟩ := hn
    obtain ⟨j, hLj, hjM, t, ht, hbadj, hk⟩ := F.chain hL1 M n hlo hhi horb
    simp only [mem_biUnion, mem_Icc, mem_range]
    refine ⟨j, ⟨hLj, hjM⟩, t, by omega, F.Ct^[t] n, hbadj, ?_⟩
    exact mem_filter.2 ⟨mem_Ico.2 ⟨hlo, hhi⟩, rfl, hk⟩
  -- Number of elements of the fibres
  have hfib : ∀ j ∈ Icc L M, ∀ t ∈ range (M ^ 2 + 1), ∀ y,
      ((Fib j t y).card : ℝ)
        ≤ ((M : ℝ) ^ 2 + 1) * (1 + 4 * (M : ℝ) ^ 2 * (F.Rb / (F.p : ℝ) ^ (j + 2)) * (F.p : ℝ) ^ (M + 1)) := by
    intro j hj t ht y
    rw [mem_Icc] at hj
    rw [mem_range] at ht
    have htM : (t : ℝ) ≤ (M : ℝ) ^ 2 := by
      have : t ≤ M ^ 2 := by omega
      exact_mod_cast this
    have hpj : (F.p : ℝ) ^ L ≤ (F.p : ℝ) ^ j := pow_le_pow_right₀ hp1r hj.1
    have hpj2 : (F.p : ℝ) ^ (L + 2) ≤ (F.p : ℝ) ^ (j + 2) := pow_le_pow_right₀ hp1r (by omega)
    have hpj2pos : (0 : ℝ) < (F.p : ℝ) ^ (j + 2) := by positivity
    set a := (F.Rb : ℝ) / (F.p : ℝ) ^ (j + 2) with ha
    have ha0 : 0 ≤ a := by positivity
    have hRY : (F.Rb : ℝ) ≤ ((F.q : ℝ) - F.p) * ((F.p ^ (j + 1) : ℕ) : ℝ) := by
      push_cast
      have : (F.p : ℝ) ^ L ≤ (F.p : ℝ) ^ (j + 1) := pow_le_pow_right₀ hp1r (by omega)
      have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ (F.q : ℝ) - F.p)
      linarith
    have haY : (F.Rb : ℝ) = a * F.p * ((F.p ^ (j + 1) : ℕ) : ℝ) := by
      rw [ha]; push_cast; field_simp; ring
    have ha1 : a ≤ 1 := by
      rw [ha, div_le_one hpj2pos]
      have : (F.p : ℝ) ^ L ≤ (F.p : ℝ) ^ (j + 2) := pow_le_pow_right₀ hp1r (by omega)
      linarith
    have hta : (t : ℝ) * a ≤ 1 / 4 := by
      have h1 : (t : ℝ) * a ≤ (M : ℝ) ^ 2 * a := mul_le_mul_of_nonneg_right htM ha0
      have h2 : (M : ℝ) ^ 2 * a * (4 * (F.p : ℝ) ^ (j + 2)) = 4 * (M : ℝ) ^ 2 * F.Rb := by
        rw [ha]; field_simp
      have h3 : 4 * (M : ℝ) ^ 2 * F.Rb ≤ 1 / 4 * (4 * (F.p : ℝ) ^ (j + 2)) := by
        have : 1 / 4 * (4 * (F.p : ℝ) ^ (j + 2)) = (F.p : ℝ) ^ (j + 2) := by ring
        linarith
      have h4 : (M : ℝ) ^ 2 * a ≤ 1 / 4 := by
        rw [← h2] at h3
        exact le_of_mul_le_mul_right h3 (by positivity)
      linarith
    have key := F.card_fiber_le hRY haY ha0 ha1 M t y hta
    refine le_trans key ?_
    have ht1 : (t : ℝ) + 1 ≤ (M : ℝ) ^ 2 + 1 := by linarith
    have hin : 1 + 4 * t * a * (F.p : ℝ) ^ (M + 1) ≤ 1 + 4 * (M : ℝ) ^ 2 * a * (F.p : ℝ) ^ (M + 1) := by
      have := mul_le_mul_of_nonneg_right htM (by positivity : (0 : ℝ) ≤ 4 * a * (F.p : ℝ) ^ (M + 1))
      nlinarith
    have h0 : 0 ≤ 1 + 4 * t * a * (F.p : ℝ) ^ (M + 1) := by positivity
    calc ((t : ℝ) + 1) * (1 + 4 * t * a * (F.p : ℝ) ^ (M + 1))
        ≤ ((M : ℝ) ^ 2 + 1) * (1 + 4 * (M : ℝ) ^ 2 * a * (F.p : ℝ) ^ (M + 1)) :=
          mul_le_mul ht1 hin h0 (by positivity)
      _ = _ := by ring
  -- Contribution of each `j`
  have hj : ∀ j ∈ Icc L M,
      ∑ t ∈ range (M ^ 2 + 1), ∑ y ∈ F.bad j, ((Fib j t y).card : ℝ)
        ≤ K * (1 + 4 * F.Rb) * ((M : ℝ) + 1) ^ 6 * (F.p : ℝ) ^ M * ξ ^ j := by
    intro j hjmem
    have hjM : j ≤ M := (mem_Icc.1 hjmem).2
    set V := ((M : ℝ) ^ 2 + 1) * (1 + 4 * (M : ℝ) ^ 2 * (F.Rb / (F.p : ℝ) ^ (j + 2)) * (F.p : ℝ) ^ (M + 1))
      with hV
    have hV0 : 0 ≤ V := by positivity
    have h1 : ∑ t ∈ range (M ^ 2 + 1), ∑ y ∈ F.bad j, ((Fib j t y).card : ℝ)
        ≤ ∑ _t ∈ range (M ^ 2 + 1), ((F.bad j).card : ℝ) * V := by
      apply sum_le_sum
      intro t ht
      calc ∑ y ∈ F.bad j, ((Fib j t y).card : ℝ) ≤ ∑ _y ∈ F.bad j, V :=
            sum_le_sum (fun y _ => hfib j hjmem t ht y)
        _ = ((F.bad j).card : ℝ) * V := by rw [sum_const, nsmul_eq_mul]
    refine le_trans h1 ?_
    rw [sum_const, card_range, nsmul_eq_mul]
    -- `p^j V ≤ (M^2+1) p^M (1 + 4 M^2 R)`
    have hpjM : (F.p : ℝ) ^ j ≤ (F.p : ℝ) ^ M := pow_le_pow_right₀ hp1r hjM
    have hpp : (F.p : ℝ) ^ j * (F.p : ℝ) ^ (M + 1) ≤ (F.p : ℝ) ^ (j + 2) * (F.p : ℝ) ^ M := by
      rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hp1r (by omega)
    have hpjV : (F.p : ℝ) ^ j * V ≤ ((M : ℝ) ^ 2 + 1) * ((F.p : ℝ) ^ M * (1 + 4 * (M : ℝ) ^ 2 * F.Rb)) := by
      have hpj2pos : (0 : ℝ) < (F.p : ℝ) ^ (j + 2) := by positivity
      have e1 : (F.p : ℝ) ^ j * (4 * (M : ℝ) ^ 2 * (F.Rb / (F.p : ℝ) ^ (j + 2)) * (F.p : ℝ) ^ (M + 1))
          = 4 * (M : ℝ) ^ 2 * F.Rb * ((F.p : ℝ) ^ j * (F.p : ℝ) ^ (M + 1) / (F.p : ℝ) ^ (j + 2)) := by
        field_simp
      have e2 : (F.p : ℝ) ^ j * (F.p : ℝ) ^ (M + 1) / (F.p : ℝ) ^ (j + 2) ≤ (F.p : ℝ) ^ M := by
        rw [div_le_iff₀ hpj2pos]; linarith
      have e3 : (F.p : ℝ) ^ j * (4 * (M : ℝ) ^ 2 * (F.Rb / (F.p : ℝ) ^ (j + 2)) * (F.p : ℝ) ^ (M + 1))
          ≤ 4 * (M : ℝ) ^ 2 * F.Rb * (F.p : ℝ) ^ M := by
        rw [e1]; exact mul_le_mul_of_nonneg_left e2 (by positivity)
      rw [hV]
      have : (F.p : ℝ) ^ j * (1 + 4 * (M : ℝ) ^ 2 * (F.Rb / (F.p : ℝ) ^ (j + 2)) * (F.p : ℝ) ^ (M + 1))
          ≤ (F.p : ℝ) ^ M * (1 + 4 * (M : ℝ) ^ 2 * F.Rb) := by
        rw [mul_add, mul_one, mul_add, mul_one]; linarith
      calc (F.p : ℝ) ^ j * (((M : ℝ) ^ 2 + 1) * (1 + 4 * (M : ℝ) ^ 2 * (F.Rb / (F.p : ℝ) ^ (j + 2))
            * (F.p : ℝ) ^ (M + 1)))
          = ((M : ℝ) ^ 2 + 1) * ((F.p : ℝ) ^ j * (1 + 4 * (M : ℝ) ^ 2 * (F.Rb / (F.p : ℝ) ^ (j + 2))
            * (F.p : ℝ) ^ (M + 1))) := by ring
        _ ≤ ((M : ℝ) ^ 2 + 1) * ((F.p : ℝ) ^ M * (1 + 4 * (M : ℝ) ^ 2 * F.Rb)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
    have hbj := hbad j
    have hM1 : (M : ℝ) ^ 2 + 1 ≤ ((M : ℝ) + 1) ^ 2 := by
      have : (0 : ℝ) ≤ M := by positivity
      nlinarith
    have hM2 : 1 + 4 * (M : ℝ) ^ 2 * F.Rb ≤ (1 + 4 * F.Rb) * ((M : ℝ) + 1) ^ 2 := by
      have : (0 : ℝ) ≤ M := by positivity
      nlinarith
    have hξj : 0 ≤ ξ ^ j := by positivity
    calc ((M ^ 2 + 1 : ℕ) : ℝ) * (((F.bad j).card : ℝ) * V)
        ≤ ((M : ℝ) ^ 2 + 1) * ((K * (F.p : ℝ) ^ j * ξ ^ j) * V) := by
          push_cast
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hbj hV0
      _ = ((M : ℝ) ^ 2 + 1) * (K * ξ ^ j * ((F.p : ℝ) ^ j * V)) := by ring
      _ ≤ ((M : ℝ) ^ 2 + 1) * (K * ξ ^ j *
            (((M : ℝ) ^ 2 + 1) * ((F.p : ℝ) ^ M * (1 + 4 * (M : ℝ) ^ 2 * F.Rb)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hpjV (by positivity)
      _ = K * ξ ^ j * (F.p : ℝ) ^ M * (((M : ℝ) ^ 2 + 1) ^ 2 * (1 + 4 * (M : ℝ) ^ 2 * F.Rb)) := by
          ring
      _ ≤ K * ξ ^ j * (F.p : ℝ) ^ M * ((((M : ℝ) + 1) ^ 2) ^ 2 * ((1 + 4 * F.Rb) * ((M : ℝ) + 1) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul (pow_le_pow_left₀ (by positivity) hM1 2) hM2 (by positivity)
            (by positivity)
      _ = K * (1 + 4 * F.Rb) * ((M : ℝ) + 1) ^ 6 * (F.p : ℝ) ^ M * ξ ^ j := by ring
  -- Total
  have hcard : (S.card : ℝ) ≤ ∑ j ∈ Icc L M, ∑ t ∈ range (M ^ 2 + 1),
      ∑ y ∈ F.bad j, ((Fib j t y).card : ℝ) := by
    have h1 := card_le_card hsub
    have h2 := card_biUnion_le (s := Icc L M) (t := fun j => (range (M ^ 2 + 1)).biUnion
      (fun t => (F.bad j).biUnion (fun y => Fib j t y)))
    have h3 : ∀ j ∈ Icc L M, ((range (M ^ 2 + 1)).biUnion
        (fun t => (F.bad j).biUnion (fun y => Fib j t y))).card
          ≤ ∑ t ∈ range (M ^ 2 + 1), ∑ y ∈ F.bad j, (Fib j t y).card := by
      intro j _
      refine le_trans card_biUnion_le (sum_le_sum (fun t _ => card_biUnion_le))
    have h4 := le_trans h1 (le_trans h2 (sum_le_sum h3))
    exact_mod_cast h4
  refine le_trans hcard (le_trans (sum_le_sum hj) ?_)
  rw [← mul_sum]
  have hgeom : ∑ j ∈ Icc L M, ξ ^ j ≤ ξ ^ L / (1 - ξ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    exact geom_sum_Ico_le_of_lt_one hξ0.le hξ1
  have hA : 0 ≤ K * (1 + 4 * F.Rb) * ((M : ℝ) + 1) ^ 6 * (F.p : ℝ) ^ M := by positivity
  calc K * (1 + 4 * F.Rb) * ((M : ℝ) + 1) ^ 6 * (F.p : ℝ) ^ M * ∑ j ∈ Icc L M, ξ ^ j
      ≤ K * (1 + 4 * F.Rb) * ((M : ℝ) + 1) ^ 6 * (F.p : ℝ) ^ M * (ξ ^ L / (1 - ξ)) :=
        mul_le_mul_of_nonneg_left hgeom hA
    _ = K * (1 + 4 * F.Rb) / (1 - ξ) * ((M : ℝ) + 1) ^ 6 * (F.p : ℝ) ^ M * ξ ^ L := by
        field_simp

end Family

end GGMCollatz
