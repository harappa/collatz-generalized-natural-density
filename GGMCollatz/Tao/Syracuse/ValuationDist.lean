import GGMCollatz.Inter
import GGMCollatz.Tao.Prob.LocalInstances

/-!
# The distribution of valuations (GGM Proposition 3.1, counterpart of tao-collatz's node C5)

Derived from `TaoCollatz/Syracuse/ValuationDist.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family (p, q, r). GGM (arXiv:2111.06170) §3, Proposition 3.1 (`prop:heuristic`),
Lemmas 3.2, 3.3 (`lem:SRperiodic`, `lem:Vsetsingleton`).

The proof follows the shape of tao-collatz's proof of Proposition 1.9 (truncation and pushforward). Instead of
GGM's original proof (the Stirling estimate `lem:stirling` and Janson's tail bound):

1. **Truncation**: map a valuation sequence `a` to `some a` if the total valuation `|a| < n'`, and to `none`
   otherwise (`truncateVec`). If `p ∤ N`, the truncated valuation sequence is determined by `N mod p^{n'}` alone
   (GGM Lemma 3.2, `valDig_stable_below'`), so the `X` side becomes a pushforward of `X mod p^{n'}`, and the
   total variation does not increase (`PMF.dTV_map_le`).
2. **Exact computation on uniform residues**: under the uniform distribution on residues `mod p^{n'}` not
   divisible by `p`, if `|a| < n'` then `P(a⁽ⁿ⁾ = a) = (p-1)^n p^{-|a|}` (the mass of `G(μ)^n`). **In GGM the
   digit sequence (the residues `R`) also determines the residue class, so the event `a⁽ⁿ⁾ = a` is a union of
   `(p-1)^{n+1}` classes `mod p^{|a|+1}`** (GGM Lemma 3.3, `valDig_eq_iff_residue`). Each class contains
   `p^{n' - |a| - 1}` residues, and there are `(p-1)p^{n'-1}` residues not divisible by `p`
   (`card_valVec_fiber`).
3. **Tail**: the probability that the total valuation of `G(μ)^n` exceeds `n' ≥ (μ + c₀)n` is exponentially
   small (`geomP_tail_bound`, Chernoff).

The main theorem is `GGMCollatz.Family.prop33` (`prop33_statement` in `GGMCollatz/Inter.lean`).
-/

open scoped ENNReal

/-! ### General PMF lemmas (independent of `p`, `q`, `r`; the lemmas of the same names in tao-collatz) -/

namespace PMF

theorem tsum_toReal_eq_one' {α : Type*} (p : PMF α) :
    ∑' x, (p x).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x), p.tsum_coe,
    ENNReal.toReal_one]

open Classical in
/-- Pushforward does not increase the total variation. -/
theorem dTV_map_le {α β : Type*} (p q : PMF α) (f : α → β) :
    (p.map f).dTV (q.map f) ≤ p.dTV q := by
  let r : α → ℝ := fun a => (p a).toReal - (q a).toReal
  have hp : Summable fun a => (p a).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hq : Summable fun a => (q a).toReal :=
    ENNReal.summable_toReal q.tsum_coe_ne_top
  have hr : Summable r := hp.sub hq
  have habs : Summable fun a => |r a| := hr.abs
  have hreal (s : PMF α) (b : β) :
      ((s.map f) b).toReal = ∑' a, if b = f a then (s a).toReal else 0 := by
    rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
    · exact tsum_congr fun a => by
        rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero]
    · intro a
      split
      · exact s.apply_ne_top a
      · exact ENNReal.zero_ne_top
  have hfiber (b : β) : Summable fun a => if b = f a then r a else 0 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun a => norm_nonneg _) ?_ habs)
    intro a
    split <;> simp [Real.norm_eq_abs]
  have hfiber_abs (b : β) : Summable fun a => if b = f a then |r a| else 0 := by
    refine Summable.of_nonneg_of_le (fun a => by positivity) ?_ habs
    intro a
    split <;> simp
  have hdiff (b : β) :
      ((p.map f) b).toReal - ((q.map f) b).toReal =
        ∑' a, if b = f a then r a else 0 := by
    have hpf : Summable fun a => if b = f a then (p a).toReal else 0 := by
      refine Summable.of_nonneg_of_le (fun a => by positivity) ?_ hp
      intro a
      split <;> simp [ENNReal.toReal_nonneg]
    have hqf : Summable fun a => if b = f a then (q a).toReal else 0 := by
      refine Summable.of_nonneg_of_le (fun a => by positivity) ?_ hq
      intro a
      split <;> simp [ENNReal.toReal_nonneg]
    rw [hreal p b, hreal q b, ← hpf.tsum_sub hqf]
    refine tsum_congr fun a => ?_
    dsimp only [r]
    split <;> simp
  have hpoint (b : β) :
      |((p.map f) b).toReal - ((q.map f) b).toReal| ≤
        ∑' a, if b = f a then |r a| else 0 := by
    rw [hdiff b]
    have hnorm : Summable fun a => ‖if b = f a then r a else 0‖ := by
      refine (hfiber_abs b).congr fun a => ?_
      split <;> simp [Real.norm_eq_abs]
    calc
      |∑' a, if b = f a then r a else 0| = ‖∑' a, if b = f a then r a else 0‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∑' a, ‖if b = f a then r a else 0‖ := norm_tsum_le_tsum_norm hnorm
      _ = ∑' a, if b = f a then |r a| else 0 := tsum_congr fun a => by
        split <;> simp [Real.norm_eq_abs]
  have hprod : Summable fun ba : β × α =>
      if ba.1 = f ba.2 then |r ba.2| else 0 := by
    have hswap : Summable fun ab : α × β =>
        if ab.2 = f ab.1 then |r ab.1| else 0 := by
      rw [summable_prod_of_nonneg (fun ab => by positivity)]
      constructor
      · intro a
        exact summable_of_ne_finset_zero (s := {f a}) fun b hb => by
          rw [if_neg (by simpa using hb)]
      · have hi : (fun a => ∑' b, if b = f a then |r a| else 0) = fun a => |r a| := by
          funext a
          rw [tsum_eq_single (f a)]
          · simp
          · intro b hb
            rw [if_neg hb]
        rw [hi]
        exact habs
    refine ((Equiv.prodComm β α).summable_iff.mpr hswap).congr fun ba => ?_
    rfl
  have hout : Summable fun b => ∑' a, if b = f a then |r a| else 0 :=
    (summable_prod_of_nonneg (fun ba : β × α => by positivity)).mp hprod |>.2
  have hcol (a : α) : Summable fun b => if b = f a then |r a| else 0 :=
    summable_of_ne_finset_zero (s := {f a}) fun b hb => by
      rw [if_neg (by simpa using hb)]
  unfold PMF.dTV
  calc
    (∑' b, |((p.map f) b).toReal - ((q.map f) b).toReal|) ≤
        ∑' b, ∑' a, if b = f a then |r a| else 0 :=
      (Summable.of_nonneg_of_le (fun b => abs_nonneg _) hpoint
        hout).tsum_le_tsum hpoint hout
    _ = ∑' a, ∑' b, if b = f a then |r a| else 0 :=
      (Summable.tsum_comm' hprod (fun b => hfiber_abs b) hcol).symm
    _ = ∑' a, |r a| := by
      refine tsum_congr fun a => ?_
      rw [tsum_eq_single (f a)]
      · simp
      · intro b hb
        rw [if_neg hb]
    _ = ∑' a, |(p a).toReal - (q a).toReal| := rfl

/-- Two PMFs on `Option` are equal if they agree on `some`. -/
theorem option_ext' {α : Type*} (p q : PMF (Option α))
    (h : ∀ a, p (some a) = q (some a)) : p = q := by
  classical
  apply PMF.ext
  intro x
  rcases x with _ | a
  · let rp := ∑' x, @ite ℝ≥0∞ (x = none) (Classical.propDecidable _) 0 (p x)
    let rq := ∑' x, @ite ℝ≥0∞ (x = none) (Classical.propDecidable _) 0 (q x)
    have hrest : rp = rq := by
      dsimp only [rp, rq]
      apply tsum_congr
      intro x
      rcases x with _ | a
      · simp
      · simp [h a]
    have hp := ENNReal.tsum_eq_add_tsum_ite (f := fun x => p x) none
    have hq := ENNReal.tsum_eq_add_tsum_ite (f := fun x => q x) none
    rw [p.tsum_coe] at hp
    rw [q.tsum_coe] at hq
    change 1 = p none + rp at hp
    change 1 = q none + rq at hq
    have hq' : 1 = q none + rp :=
      hq.trans (congrArg (fun t => q none + t) hrest.symm)
    have hfinite : rp ≠ ∞ := by
      apply ne_top_of_le_ne_top ENNReal.one_ne_top
      calc
        rp ≤ p none + rp := le_add_self
        _ = 1 := hp.symm
    apply (ENNReal.add_right_inj hfinite).mp
    simpa only [add_comm] using hp.symm.trans hq'
  · exact h a

/-- Pushforwards by functions that agree on the support are equal. -/
theorem map_congr_support' {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hpa : p a = 0 := not_ne_iff.mp (mt (p.mem_support_iff a).mpr ha)
    simp [hpa]

/-- Expectation of a nonnegative observable under a pushforward. -/
theorem expect_map_of_nonneg {α β : Type*} (p : PMF α) (f : α → β) (g : β → ℝ)
    (hg : ∀ b, 0 ≤ g b) : (p.map f).expect g = p.expect (g ∘ f) := by
  unfold PMF.expect
  rw [← PMF.toReal_tsum_mul_ofReal (p.map f) g hg, PMF.tsum_map_mul]
  simpa only [Function.comp_apply] using
    PMF.toReal_tsum_mul_ofReal p (fun a => g (f a)) (fun a => hg (f a))

end PMF

namespace GGMCollatz

/-! ### Truncation (independent of `p`, `q`, `r`) -/

/-- Truncation of a valuation sequence: `some a` if the total valuation `|a| < k`, and `none` otherwise. -/
noncomputable def truncateVec (n k : ℕ) (a : Fin n → ℕ) : Option (Fin n → ℕ) :=
  if pre a n < k then some a else none

theorem PMF.map_truncateVec_some {n : ℕ} (p : PMF (Fin n → ℕ)) (k : ℕ)
    (a : Fin n → ℕ) :
    (p.map (truncateVec n k)) (some a) = if pre a n < k then p a else 0 := by
  classical
  rw [_root_.PMF.map_apply]
  by_cases hL : pre a n < k
  · rw [if_pos hL, tsum_eq_single a]
    · simp [truncateVec, hL]
    · intro b hb
      rw [if_neg]
      intro heq
      by_cases hbL : pre b n < k
      · simp only [truncateVec, hbL, if_pos, Option.some.injEq] at heq
        exact hb heq.symm
      · simp [truncateVec, hbL] at heq
  · rw [if_neg hL]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    split_ifs with heq
    · by_cases hbL : pre b n < k
      · simp only [truncateVec, hbL, if_pos, Option.some.injEq] at heq
        exact (hL (heq ▸ hbL)).elim
      · simp [truncateVec, hbL] at heq
    · rfl

/-- **Total variation bound via truncation**: `dTV(P, Q) ≤ 2 dTV(truncated P, truncated Q) + 2 Q(|a| ≥ k)`. -/
theorem PMF.dTV_le_of_truncateVec {n : ℕ} (p q : _root_.PMF (Fin n → ℕ)) (k : ℕ) :
    p.dTV q ≤ 2 * (p.map (truncateVec n k)).dTV (q.map (truncateVec n k)) +
      2 * ∑' a, if k ≤ pre a n then (q a).toReal else 0 := by
  classical
  let D : ℝ := (p.map (truncateVec n k)).dTV (q.map (truncateVec n k))
  let tail (r : _root_.PMF (Fin n → ℕ)) : ℝ :=
    ∑' a, if k ≤ pre a n then (r a).toReal else 0
  have mass_summable (r : _root_.PMF (Fin n → ℕ)) : Summable fun a => (r a).toReal :=
    ENNReal.summable_toReal r.tsum_coe_ne_top
  have tail_summable (r : _root_.PMF (Fin n → ℕ)) :
      Summable fun a => if k ≤ pre a n then (r a).toReal else 0 :=
    Summable.of_nonneg_of_le
      (fun a => by split <;> simp [ENNReal.toReal_nonneg])
      (fun a => by split <;> simp [ENNReal.toReal_nonneg]) (mass_summable r)
  have diff_summable (r s : _root_.PMF (Fin n → ℕ)) :
      Summable fun a => |(r a).toReal - (s a).toReal| :=
    ((mass_summable r).sub (mass_summable s)).abs
  have map_diff_summable : Summable fun x =>
      |((p.map (truncateVec n k)) x).toReal -
        ((q.map (truncateVec n k)) x).toReal| :=
    ((ENNReal.summable_toReal (p.map (truncateVec n k)).tsum_coe_ne_top).sub
      (ENNReal.summable_toReal (q.map (truncateVec n k)).tsum_coe_ne_top)).abs
  have hlow : (∑' a, if pre a n < k then |(p a).toReal - (q a).toReal| else 0) ≤ D := by
    have hcomp : (fun a => |((p.map (truncateVec n k)) (some a)).toReal -
        ((q.map (truncateVec n k)) (some a)).toReal|) =
        fun a => if pre a n < k then |(p a).toReal - (q a).toReal| else 0 := by
      funext a
      rw [PMF.map_truncateVec_some, PMF.map_truncateVec_some]
      by_cases hL : pre a n < k <;> simp [hL]
    rw [← hcomp]
    exact tsum_comp_le_tsum_of_inj map_diff_summable (fun x => abs_nonneg _)
      (Option.some_injective _)
  have hnone (r : _root_.PMF (Fin n → ℕ)) :
      ((r.map (truncateVec n k)) none).toReal = tail r := by
    rw [_root_.PMF.map_apply, ENNReal.tsum_toReal_eq]
    · dsimp only [tail]
      apply tsum_congr
      intro a
      by_cases hL : pre a n < k
      · simp [truncateVec, hL, show ¬k ≤ pre a n by omega]
      · simp [truncateVec, hL, show k ≤ pre a n by omega]
    · intro a
      split
      · exact r.apply_ne_top a
      · exact ENNReal.zero_ne_top
  have htailp : tail p ≤ tail q + D := by
    have hpoint : |((p.map (truncateVec n k)) none).toReal -
        ((q.map (truncateVec n k)) none).toReal| ≤ D := by
      dsimp only [D, _root_.PMF.dTV]
      exact map_diff_summable.le_tsum none (fun _ _ => abs_nonneg _)
    rw [hnone p, hnone q] at hpoint
    linarith [le_abs_self (tail p - tail q)]
  have hsplit : p.dTV q =
      (∑' a, if pre a n < k then |(p a).toReal - (q a).toReal| else 0) +
      (∑' a, if k ≤ pre a n then |(p a).toReal - (q a).toReal| else 0) := by
    unfold _root_.PMF.dTV
    rw [← (Summable.of_nonneg_of_le
      (fun a => by split <;> positivity)
      (fun a => by split <;> simp) (diff_summable p q)).tsum_add
      (Summable.of_nonneg_of_le
        (fun a => by split <;> positivity)
        (fun a => by split <;> simp) (diff_summable p q))]
    apply tsum_congr
    intro a
    by_cases hL : pre a n < k
    · have hn : ¬k ≤ pre a n := by omega
      simp [hL, hn]
    · have hn : k ≤ pre a n := Nat.le_of_not_gt hL
      simp [hL, hn]
  have hhigh : (∑' a, if k ≤ pre a n then |(p a).toReal - (q a).toReal| else 0) ≤
      tail p + tail q := by
    dsimp only [tail]
    have hs := (tail_summable p).add (tail_summable q)
    have hpoint : ∀ a,
        (if k ≤ pre a n then |(p a).toReal - (q a).toReal| else 0) ≤
          (if k ≤ pre a n then (p a).toReal else 0) +
            (if k ≤ pre a n then (q a).toReal else 0) := by
      intro a
      by_cases ha : k ≤ pre a n
      · simp only [ha, if_pos]
        rw [abs_le]
        have hp0 : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
        have hq0 : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
        constructor <;> linarith
      · simp [ha]
    have hsumdiff : Summable fun a =>
        if k ≤ pre a n then |(p a).toReal - (q a).toReal| else 0 :=
      Summable.of_nonneg_of_le (fun a => by positivity) hpoint hs
    calc
      (∑' a, if k ≤ pre a n then |(p a).toReal - (q a).toReal| else 0) ≤
          ∑' a, ((if k ≤ pre a n then (p a).toReal else 0) +
            (if k ≤ pre a n then (q a).toReal else 0)) :=
        hsumdiff.tsum_le_tsum hpoint hs
      _ = (∑' a, if k ≤ pre a n then (p a).toReal else 0) +
          ∑' a, if k ≤ pre a n then (q a).toReal else 0 :=
        (tail_summable p).tsum_add (tail_summable q)
  rw [hsplit]
  change _ ≤ 2 * D + 2 * tail q
  linarith

/-! ### The tail of the total valuation of `G(μ)^n` -/

/-- Writing the tail of the total valuation of an i.i.d. sequence as the tail of the law of the sum `iidSum`
(`μ` is an arbitrary PMF on ℕ). -/
theorem iid_overflow_eq (μ : _root_.PMF ℕ) (n k : ℕ) :
    (∑' a : Fin n → ℕ, if k ≤ pre a n then ((μ.iid n) a).toReal else 0) =
      (∑' L : ℕ, if k ≤ L then ((iidSum μ n) L).toReal else 0) := by
  let E : Set ℕ := {L | k ≤ L}
  have hmap := _root_.PMF.expect_map_of_nonneg (μ.iid n) (fun a => ∑ i, a i)
    (Set.indicator E 1) (fun L => Set.indicator_nonneg (fun _ _ => zero_le_one) L)
  rw [show (μ.iid n).map (fun a => ∑ i, a i) = iidSum μ n from rfl] at hmap
  unfold _root_.PMF.expect at hmap
  simpa only [Function.comp_apply, E, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply,
    mul_ite, mul_one, mul_zero, pre_eq_fin_sum] using hmap.symm

/-- If `n' ≥ (μ + c₀)n`, the probability that the total valuation of `G(μ)^n` is at least `n'` is at most
`C_geomTail·G_{1+n}(c·c₀n)`. -/
theorem geomP_overflow_le_Gweight {p : ℕ} (hp : 2 ≤ p) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (n k : ℕ) (hsize : (muP p + c₀) * n ≤ (k : ℝ)) :
    (∑' a : Fin n → ℕ, if k ≤ pre a n then (((geomP p).iid n) a).toReal else 0) ≤
      C_geomTail * Gweight (1 + n) (c_geomTail * (c₀ * n)) := by
  rw [iid_overflow_eq]
  have hdom : ∀ L : ℕ,
      (if k ≤ L then ((iidSum (geomP p) n) L).toReal else 0) ≤
        if c₀ * n ≤ |(L : ℝ) - muP p * n| then ((iidSum (geomP p) n) L).toReal else 0 := by
    intro L
    by_cases hL : k ≤ L
    · have hLR : (k : ℝ) ≤ L := by exact_mod_cast hL
      have hdev : c₀ * n ≤ (L : ℝ) - muP p * n := by linarith
      rw [if_pos hL, if_pos (le_trans hdev (le_abs_self _))]
    · rw [if_neg hL]
      positivity
  have hsum : Summable fun L : ℕ =>
      if c₀ * n ≤ |(L : ℝ) - muP p * n| then ((iidSum (geomP p) n) L).toReal else 0 :=
    Summable.of_nonneg_of_le (fun L => by split <;> positivity)
      (fun L => by split <;> simp [ENNReal.toReal_nonneg])
      (ENNReal.summable_toReal (iidSum (geomP p) n).tsum_coe_ne_top)
  exact le_trans ((Summable.of_nonneg_of_le (fun L => by split <;> positivity) hdom
    hsum).tsum_le_tsum hdom hsum)
    (geomP_tail_bound_atC hp n (c₀ * n) (mul_nonneg hc₀.le (Nat.cast_nonneg n)))

/-! ### Converting the exponential decay (base `p`) -/

/-- `min(d²/2, d)`. -/
noncomputable def linearDecay (d : ℝ) : ℝ := min (d ^ 2 / 2) d

theorem linearDecay_pos {d : ℝ} (hd : 0 < d) : 0 < linearDecay d := by
  unfold linearDecay
  exact lt_min (div_pos (sq_pos_of_pos hd) (by norm_num)) hd

theorem Gweight_linear_le (d : ℝ) (hd : 0 < d) (n : ℕ) :
    Gweight (1 + n) (d * n) ≤ 2 * Real.exp (-linearDecay d * n) := by
  rcases n with _ | n
  · norm_num [Gweight]
  have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hden : 0 < (1 : ℝ) + (n + 1 : ℕ) := by positivity
  have hgamma1 : linearDecay d ≤ d ^ 2 / 2 := min_le_left _ _
  have hgamma2 : linearDecay d ≤ d := min_le_right _ _
  have hquad : linearDecay d * (n + 1 : ℕ) ≤
      (d * (n + 1 : ℕ)) ^ 2 / (1 + (n + 1 : ℕ)) := by
    apply (le_div_iff₀ hden).2
    calc
      linearDecay d * (n + 1 : ℕ) * (1 + (n + 1 : ℕ)) ≤
          (d ^ 2 / 2) * (n + 1 : ℕ) * (1 + (n + 1 : ℕ)) := by gcongr
      _ ≤ (d ^ 2 / 2) * (n + 1 : ℕ) * (2 * (n + 1 : ℕ)) := by
        gcongr; linarith
      _ = (d * (n + 1 : ℕ)) ^ 2 := by ring
  have hlin : linearDecay d * (n + 1 : ℕ) ≤ |d * (n + 1 : ℕ)| := by
    rw [abs_of_pos (mul_pos hd (by positivity))]
    gcongr
  unfold Gweight
  have he1 : Real.exp (-(d * (n + 1 : ℕ)) ^ 2 / (1 + (n + 1 : ℕ))) ≤
      Real.exp (-linearDecay d * (n + 1 : ℕ)) :=
    Real.exp_le_exp.mpr (by
      rw [show -(d * (n + 1 : ℕ)) ^ 2 / (1 + (n + 1 : ℕ)) =
        -((d * (n + 1 : ℕ)) ^ 2 / (1 + (n + 1 : ℕ))) by ring]
      linarith)
  have he2 : Real.exp (-|d * (n + 1 : ℕ)|) ≤
      Real.exp (-linearDecay d * (n + 1 : ℕ)) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp (-(d * (n + 1 : ℕ)) ^ 2 / (1 + (n + 1 : ℕ))) +
        Real.exp (-|d * (n + 1 : ℕ)|) ≤
      Real.exp (-linearDecay d * (n + 1 : ℕ)) +
        Real.exp (-linearDecay d * (n + 1 : ℕ)) := add_le_add he1 he2
    _ = 2 * Real.exp (-linearDecay d * (n + 1 : ℕ)) := by ring

/-- `min(log p, min(d²/2, d))`. -/
noncomputable def finalDecay (p : ℕ) (d : ℝ) : ℝ := min (Real.log p) (linearDecay d)

theorem finalDecay_pos {p : ℕ} (hp : 2 ≤ p) {d : ℝ} (hd : 0 < d) : 0 < finalDecay p d := by
  unfold finalDecay
  have : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  exact lt_min (Real.log_pos this) (linearDecay_pos hd)

theorem exp_linearDecay_le_rpow {p : ℕ} (hp : 2 ≤ p) (d : ℝ) (n : ℕ) :
    Real.exp (-linearDecay d * n) ≤
      (p : ℝ) ^ (-(finalDecay p d / Real.log p) * (n : ℝ)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  rw [Real.rpow_def_of_pos (by linarith)]
  have hlog : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  have heq : Real.log p * (-(finalDecay p d / Real.log p) * (n : ℝ)) =
      -finalDecay p d * n := by field_simp
  rw [heq]
  apply Real.exp_le_exp.mpr
  have hle : finalDecay p d ≤ linearDecay d := min_le_right _ _
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

theorem rpow_neg_nat_le {p : ℕ} (hp : 2 ≤ p) (d : ℝ) (hd : 0 < d) (n k : ℕ)
    (hnk : (n : ℝ) ≤ k) :
    (p : ℝ) ^ (-(k : ℝ)) ≤
      (p : ℝ) ^ (-(finalDecay p d / Real.log p) * (n : ℝ)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  apply Real.rpow_le_rpow_of_exponent_le hp1.le
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hrho : finalDecay p d ≤ Real.log p := min_le_left _ _
  have hc1 : finalDecay p d / Real.log p ≤ 1 := (div_le_one hlog).2 hrho
  have hc10 : 0 ≤ finalDecay p d / Real.log p :=
    (div_nonneg (finalDecay_pos hp hd).le hlog.le)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

namespace Family

variable (F : Family)

/-! ### Counting residues (the counting form of GGM Lemma 3.3) -/

/-- Among the residues modulo `p^n`, exactly `p^{n-k}` reduce to `r` modulo `p^k` (`k ≤ n`). -/
theorem card_zmod_pow_cast_fiber (n k : ℕ) (hkn : k ≤ n) (r : ZMod (F.p ^ k)) :
    (Finset.univ.filter fun z : ZMod (F.p ^ n) =>
      ZMod.cast z = r).card = F.p ^ (n - k) := by
  let m := F.p ^ k
  let q := F.p ^ (n - k)
  have hm0 : 0 < m := pow_pos F.p_pos k
  have hpow : F.p ^ n = m * q := by
    dsimp [m, q]
    rw [← pow_add]
    congr 1
    omega
  let f : ZMod (F.p ^ n) → ℕ := fun z => z.val / m
  let g : ℕ → ZMod (F.p ^ n) := fun j => r.val + m * j
  rw [show F.p ^ (n - k) = (Finset.range q).card by simp [q]]
  apply Finset.card_nbij' f g
  · intro z hz
    change f z ∈ Finset.range q
    rw [Finset.mem_range]
    have hzlt : z.val < m * q := by simpa [← hpow] using z.val_lt
    exact (Nat.div_lt_iff_lt_mul hm0).2 (by simpa [Nat.mul_comm] using hzlt)
  · intro j hj
    change j ∈ Finset.range q at hj
    change g j ∈ Finset.univ.filter fun z : ZMod (F.p ^ n) => ZMod.cast z = r
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ _
    · rw [Finset.mem_range] at hj
      have hrlt : r.val < m := by simpa [m] using r.val_lt
      have hg : g j = (r.val + m * j : ℕ) := by simp [g, Nat.cast_add, Nat.cast_mul]
      rw [hg]
      rw [← ZMod.natCast_zmod_val r]
      rw [ZMod.cast_natCast (by simpa [m] using pow_dvd_pow F.p hkn)]
      rw [ZMod.natCast_eq_natCast_iff']
      simp [m, Nat.add_mod, Nat.mod_eq_of_lt hrlt]
  · intro z hz
    change z ∈ Finset.univ.filter (fun z : ZMod (F.p ^ n) => ZMod.cast z = r) at hz
    rw [Finset.mem_filter] at hz
    have hcast := hz.2
    rw [← ZMod.natCast_zmod_val z, ← ZMod.natCast_zmod_val r] at hcast
    rw [ZMod.cast_natCast (by simpa [m] using pow_dvd_pow F.p hkn)] at hcast
    rw [ZMod.natCast_eq_natCast_iff'] at hcast
    have hrlt : r.val < m := by simpa [m] using r.val_lt
    have hmod : z.val % m = r.val := by
      simpa [m, Nat.mod_eq_of_lt hrlt] using hcast
    apply ZMod.val_injective
    simp only [f]
    have hzdecomp := (Nat.mod_add_div z.val m).symm
    rw [hmod] at hzdecomp
    have hlt : r.val + m * (z.val / m) < F.p ^ n := by
      rw [← hzdecomp]
      exact z.val_lt
    have hg : g (z.val / m) = (r.val + m * (z.val / m) : ℕ) := by
      simp [g, Nat.cast_add, Nat.cast_mul]
    rw [hg, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    exact hzdecomp.symm
  · intro j hj
    change j ∈ Finset.range q at hj
    rw [Finset.mem_range] at hj
    simp only [f]
    have hrlt : r.val < m := by simpa [m] using r.val_lt
    have hval : r.val + m * j < F.p ^ n := by
      rw [hpow]
      nlinarith
    have hg : g j = (r.val + m * j : ℕ) := by simp [g, Nat.cast_add, Nat.cast_mul]
    rw [hg, ZMod.val_natCast, Nat.mod_eq_of_lt hval]
    rw [Nat.add_mul_div_left _ _ hm0, Nat.div_eq_of_lt hrlt, zero_add]

/-- Lemma 3.3 in the form for residues modulo `p^{n'}`: if `|a| < n'`, then (`p ∤ z`, valuation sequence `a`,
digit sequence `j`) is equivalent to `z mod p^{|a|+1} = valuationResidue n a j`. -/
theorem valDig_iff_cast (n n' : ℕ) (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i)
    (j : Fin (n + 1) → ℕ) (hj : ∀ i, 0 < j i ∧ j i < F.p) (hL : pre a n < n')
    (z : ZMod (F.p ^ n')) :
    (z.val % F.p ≠ 0 ∧ F.valVec z.val n = a ∧ F.digVec z.val (n + 1) = j) ↔
      (ZMod.cast z : ZMod (F.p ^ (pre a n + 1))) = F.valuationResidue n a j := by
  have hdvd : F.p ^ (pre a n + 1) ∣ F.p ^ n' := pow_dvd_pow _ (by omega)
  have hcast : (ZMod.cast z : ZMod (F.p ^ (pre a n + 1))) =
      (z.val : ZMod (F.p ^ (pre a n + 1))) := by
    calc (ZMod.cast z : ZMod (F.p ^ (pre a n + 1)))
        = ZMod.cast (z.val : ZMod (F.p ^ n')) :=
          congrArg (fun w : ZMod (F.p ^ n') => (ZMod.cast w : ZMod (F.p ^ (pre a n + 1))))
            (ZMod.natCast_zmod_val z).symm
      _ = (z.val : ZMod (F.p ^ (pre a n + 1))) :=
          ZMod.cast_natCast (R := ZMod (F.p ^ (pre a n + 1))) hdvd z.val
  rw [hcast]
  exact F.valDig_eq_iff_residue z.val n a ha j hj

/-- **The counting form of Lemma 3.3**: if `|a| < n'`, the number of residues `mod p^{n'}` not divisible by `p`
with valuation sequence `a` is `(p-1)^{n+1} p^{n' - |a| - 1}` (one class `mod p^{|a|+1}` for each digit sequence
`j ∈ {1,…,p-1}^{n+1}`). -/
theorem card_valVec_fiber (n n' : ℕ) (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i) (hL : pre a n < n') :
    (Finset.univ.filter fun z : ZMod (F.p ^ n') =>
      z.val % F.p ≠ 0 ∧ F.valVec z.val n = a).card
      = (F.p - 1) ^ (n + 1) * F.p ^ (n' - (pre a n + 1)) := by
  classical
  set S := (Finset.univ.filter fun z : ZMod (F.p ^ n') =>
      z.val % F.p ≠ 0 ∧ F.valVec z.val n = a) with hS
  set J : Finset (Fin (n + 1) → ℕ) := Fintype.piFinset fun _ => Finset.Ioo 0 F.p with hJdef
  have hJ : ∀ z ∈ S, F.digVec z.val (n + 1) ∈ J := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    rw [hJdef, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Ioo]
    exact F.digVec_pos_lt hz.2.1 (n + 1) i
  rw [Finset.card_eq_sum_card_fiberwise hJ]
  have hfib : ∀ j ∈ J, (S.filter fun z => F.digVec z.val (n + 1) = j).card
      = F.p ^ (n' - (pre a n + 1)) := by
    intro j hj
    have hj' : ∀ i, 0 < j i ∧ j i < F.p := by
      intro i
      have := (Fintype.mem_piFinset.mp hj) i
      simpa [Finset.mem_Ioo] using this
    rw [← F.card_zmod_pow_cast_fiber n' (pre a n + 1) (by omega) (F.valuationResidue n a j)]
    congr 1
    ext z
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← F.valDig_iff_cast n n' a ha j hj' hL z]
    tauto
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hJdef,
    Fintype.card_piFinset]
  simp [Nat.card_Ioo]

/-- There are `(p-1)p^{n'-1}` residues `mod p^{n'}` not divisible by `p` (`n' ≥ 1`). -/
theorem card_npMod (n' : ℕ) (hn' : 1 ≤ n') :
    (Finset.univ.filter fun z : ZMod (F.p ^ n') => z.val % F.p ≠ 0).card
      = (F.p - 1) * F.p ^ (n' - 1) := by
  have h := F.card_valVec_fiber 0 n' (fun i => i.elim0) (fun i => i.elim0) (by simp; omega)
  simp only [pre_zero, zero_add, pow_one] at h
  rw [← h]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    exact ⟨hz, funext fun i => i.elim0⟩
  · intro hz
    exact hz.1

theorem card_npMod_pos (n' : ℕ) (hn' : 1 ≤ n') :
    0 < (Finset.univ.filter fun z : ZMod (F.p ^ n') => z.val % F.p ≠ 0).card := by
  rw [F.card_npMod n' hn']
  have := F.two_le_p
  exact Nat.mul_pos (by omega) (pow_pos F.p_pos _)

/-- The mass of `unifNpMod`: `((p-1)p^{n'-1})⁻¹` if `p ∤ z`, and 0 otherwise (`n' ≥ 1`). -/
theorem unifNpMod_apply (n' : ℕ) (hn' : 1 ≤ n') (z : ZMod (F.p ^ n')) :
    F.unifNpMod n' z
      = if z.val % F.p ≠ 0 then (((F.p - 1) * F.p ^ (n' - 1) : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  classical
  have hne : (Finset.univ.filter fun z : ZMod (F.p ^ n') => z.val % F.p ≠ 0).Nonempty :=
    Finset.card_pos.mp (F.card_npMod_pos n' hn')
  unfold unifNpMod
  rw [dif_pos (by convert hne), PMF.uniformOfFinset_apply]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h
  · congr 2
    rw [← F.card_npMod n' hn']
  · rfl

/-- Residues in the support of `unifNpMod` are not divisible by `p` (`n' ≥ 1`). -/
theorem unifNpMod_support_val (n' : ℕ) (hn' : 1 ≤ n') (z : ZMod (F.p ^ n'))
    (hz : z ∈ (F.unifNpMod n').support) : z.val % F.p ≠ 0 := by
  classical
  rw [PMF.mem_support_iff, F.unifNpMod_apply n' hn' z] at hz
  by_contra h
  exact hz (if_neg (not_not.mpr h))

/-! ### The law of the valuation sequence on uniform residues -/

/-- **On uniform residues, the mass of the valuation sequence is that of `G(μ)^n`** (`|a| < n'`, components ≥ 1):
`(p-1)^{n+1} p^{n'-|a|-1} / ((p-1)p^{n'-1}) = (p-1)^n p^{-|a|}`. -/
theorem unifNpMod_map_valVec_apply (n n' : ℕ) (a : Fin n → ℕ) (ha : ∀ i, 1 ≤ a i)
    (hL : pre a n < n') :
    ((F.unifNpMod n').map fun z => F.valVec z.val n) a = (PMF.iid (geomP F.p) n) a := by
  classical
  have hn' : 1 ≤ n' := by omega
  set c : ℝ≥0∞ := (((F.p - 1) * F.p ^ (n' - 1) : ℕ) : ℝ≥0∞)⁻¹ with hc
  rw [PMF.map_apply]
  have hterm : ∀ z : ZMod (F.p ^ n'),
      (@ite ℝ≥0∞ (a = F.valVec z.val n) (Classical.propDecidable _) (F.unifNpMod n' z) 0)
        = if (z.val % F.p ≠ 0 ∧ F.valVec z.val n = a) then c else 0 := by
    intro z
    rw [F.unifNpMod_apply n' hn' z]
    by_cases h1 : z.val % F.p ≠ 0
    · by_cases h2 : F.valVec z.val n = a
      · have e1 : a = F.valVec z.val n := h2.symm
        have e2 : z.val % F.p ≠ 0 ∧ F.valVec z.val n = a := ⟨h1, h2⟩
        rw [if_pos e1, if_pos h1, if_pos e2]
      · have e1 : ¬ a = F.valVec z.val n := fun h => h2 h.symm
        have e2 : ¬ (z.val % F.p ≠ 0 ∧ F.valVec z.val n = a) := fun h => h2 h.2
        rw [if_neg e1, if_neg e2]
    · have e2 : ¬ (z.val % F.p ≠ 0 ∧ F.valVec z.val n = a) := fun h => h1 h.1
      rw [if_neg e2, if_neg h1]
      split_ifs <;> rfl
  rw [tsum_congr hterm, tsum_fintype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    F.card_valVec_fiber n n' a ha hL, iid_geomP_apply_of_pos F.two_le_p n a ha,
    ← pre_eq_fin_sum, hc]
  have hn1 : n' - 1 = pre a n + (n' - (pre a n + 1)) := by omega
  rw [hn1]
  simp only [Nat.cast_mul, Nat.cast_pow]
  set A : ℝ≥0∞ := ((F.p - 1 : ℕ) : ℝ≥0∞) with hA
  set P : ℝ≥0∞ := (F.p : ℝ≥0∞) with hP
  set e := n' - (pre a n + 1)
  set s := pre a n
  have hA0 : A ≠ 0 := natCast_sub_one_ne_zero F.two_le_p
  have hP0 : P ≠ 0 := by rw [hP]; exact_mod_cast F.p_ne_zero
  set X : ℝ≥0∞ := A * P ^ e with hX
  have hX0 : X ≠ 0 := mul_ne_zero hA0 (pow_ne_zero _ hP0)
  have hXt : X ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  have hPs0 : P ^ s ≠ 0 := pow_ne_zero _ hP0
  have hPst : P ^ s ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  calc A ^ (n + 1) * P ^ e * (A * P ^ (s + e))⁻¹
      = A ^ n * X * (P ^ s * X)⁻¹ := by
        rw [hX, pow_add, pow_succ]
        ring_nf
    _ = A ^ n * X * ((P ^ s)⁻¹ * X⁻¹) := by
        rw [ENNReal.mul_inv (Or.inl hPs0) (Or.inl hPst)]
    _ = A ^ n * (P ^ s)⁻¹ * (X * X⁻¹) := by ring
    _ = A ^ n * (P⁻¹) ^ s := by
        rw [ENNReal.mul_inv_cancel hX0 hXt, mul_one, ENNReal.inv_pow]

/-- On uniform residues, an `a` with a zero component has no mass (`n' ≥ 1`). -/
theorem unifNpMod_map_valVec_apply_eq_zero_of_not_pos (n n' : ℕ) (hn' : 1 ≤ n')
    (a : Fin n → ℕ) (ha : ¬ ∀ i, 1 ≤ a i) :
    ((F.unifNpMod n').map fun z => F.valVec z.val n) a = 0 := by
  classical
  rw [PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  split_ifs with hz
  · rw [F.unifNpMod_apply n' hn' z]
    by_cases h1 : z.val % F.p ≠ 0
    · exfalso
      apply ha
      rw [hz]
      exact F.valVec_pos h1 n
    · rw [if_neg h1]
  · rfl

/-! ### The truncated valuation sequence is determined by the residue modulo `p^k` alone (GGM Lemma 3.2) -/

/-- The truncated valuation sequence of the residue `z mod p^k`. -/
noncomputable def truncateVal (n k : ℕ) (z : ZMod (F.p ^ k)) : Option (Fin n → ℕ) :=
  truncateVec n k (F.valVec z.val n)

/-- If `p ∤ N`, the truncated valuation sequence of `N mod p^k` is that of `N` (GGM Lemma 3.2,
`valDig_stable_below'`). -/
theorem truncateVal_natCast (N n k : ℕ) (hN : N % F.p ≠ 0) :
    F.truncateVal n k (N : ZMod (F.p ^ k)) = truncateVec n k (F.valVec N n) := by
  unfold truncateVal truncateVec
  set M := ((N : ZMod (F.p ^ k))).val with hMdef
  have hmod : N % F.p ^ k = M % F.p ^ k := by
    rw [hMdef, ZMod.val_natCast, Nat.mod_mod]
  by_cases hL : pre (F.valVec N n) n < k
  · have hL' : F.valSum N n < k := by rwa [F.pre_valVec (le_refl n)] at hL
    have hv := (F.valDig_stable_below' hN hmod hL').2.1
    rw [hv]
  · have hLM : ¬ pre (F.valVec M n) n < k := by
      intro h
      have hk : 1 ≤ k := by omega
      have hdvd : F.p ∣ F.p ^ k := dvd_pow_self _ (by omega)
      have hM : M % F.p ≠ 0 := by
        rw [← Nat.mod_mod_of_dvd M hdvd, ← hmod, Nat.mod_mod_of_dvd N hdvd]
        exact hN
      have h' : F.valSum M n < k := by rwa [F.pre_valVec (le_refl n)] at h
      have hv := (F.valDig_stable_below' hM hmod.symm h').2.1
      rw [← hv] at h
      exact hL h
    rw [if_neg hL, if_neg hLM]

/-- After truncation, the valuation sequence on uniform residues and `G(μ)^n` have the same law. -/
theorem truncated_uniform_eq_geom (n k : ℕ) :
    (((F.unifNpMod k).map fun z => F.valVec z.val n).map (truncateVec n k)) =
      ((geomP F.p).iid n).map (truncateVec n k) := by
  apply PMF.option_ext'
  intro a
  rw [PMF.map_truncateVec_some, PMF.map_truncateVec_some]
  by_cases hL : pre a n < k
  · rw [if_pos hL, if_pos hL]
    by_cases ha : ∀ i, 1 ≤ a i
    · exact F.unifNpMod_map_valVec_apply n k a ha hL
    · rw [F.unifNpMod_map_valVec_apply_eq_zero_of_not_pos n k (by omega) a ha,
        iid_geomP_apply_eq_zero_of_not_pos F.two_le_p n a ha]
  · rw [if_neg hL, if_neg hL]

/-- The total variation of the truncated valuation sequences is at most the total variation between
`X mod p^k` and the uniform distribution. -/
theorem truncated_val_dTV_le (X : PMF ℕ) (n k : ℕ)
    (hnp : ∀ N ∈ X.support, N % F.p ≠ 0) :
    ((X.map fun N => F.valVec N n).map (truncateVec n k)).dTV
        (((geomP F.p).iid n).map (truncateVec n k)) ≤
      PMF.dTV (X.map fun N => (N : ZMod (F.p ^ k))) (F.unifNpMod k) := by
  let castMod : ℕ → ZMod (F.p ^ k) := fun N => (N : ZMod (F.p ^ k))
  have hX : (X.map fun N => F.valVec N n).map (truncateVec n k) =
      (PMF.map castMod X).map (F.truncateVal n k) := by
    calc
      (X.map fun N => F.valVec N n).map (truncateVec n k) =
          X.map (truncateVec n k ∘ fun N => F.valVec N n) :=
        PMF.map_comp (p := X) (f := fun N => F.valVec N n) (truncateVec n k)
      _ = X.map (F.truncateVal n k ∘ castMod) := by
        apply PMF.map_congr_support'
        intro N hN
        exact (F.truncateVal_natCast N n k (hnp N hN)).symm
      _ = (PMF.map castMod X).map (F.truncateVal n k) := by
        exact (PMF.map_comp (p := X) (f := castMod) (F.truncateVal n k)).symm
  have hU : ((F.unifNpMod k).map fun z => F.valVec z.val n).map (truncateVec n k) =
      (F.unifNpMod k).map (F.truncateVal n k) := by
    rw [PMF.map_comp]
    rfl
  rw [hX, ← F.truncated_uniform_eq_geom n k, hU]
  -- Because of the type ascription `(N : ZMod _)`, the statement's `X.map fun N => (N : ZMod _)`
  -- unfolds to `PMF.map (fun z => z) (lift of X)` (the same situation as in tao-collatz).
  change _ ≤ (PMF.map (fun z : ZMod (F.p ^ k) => z) (PMF.map castMod X)).dTV (F.unifNpMod k)
  rw [show (fun z : ZMod (F.p ^ k) => z) = id by rfl, PMF.map_id]
  exact PMF.dTV_map_le (PMF.map castMod X) (F.unifNpMod k) (F.truncateVal n k)

/-! ### GGM Proposition 3.1 -/

/-- **GGM Proposition 3.1** (distribution of valuations): if the distribution modulo `p^{n'}` of numbers not
divisible by `p` is within `K p^{-n'}` of uniform, and `n' ≥ (μ + c₀)n`, then the valuation sequence `a⁽ⁿ⁾` is
within `C p^{-c₁ n}` of `G(μ)^n` (`c₁ = min(log p, min(d²/2, d))/log p`, `d = c₀/400`, `C = 2K + 8`). -/
theorem prop33 : F.prop33_statement := by
  intro c₀ K hc₀ hK
  have hp := F.two_le_p
  have hp1 : (1 : ℝ) < F.p := by exact_mod_cast (by omega : 1 < F.p)
  set d : ℝ := c_geomTail * c₀ with hd_def
  have hd : 0 < d := mul_pos c_geomTail_pos hc₀
  set c₁ : ℝ := finalDecay F.p d / Real.log F.p with hc₁_def
  have hc₁ : 0 < c₁ := div_pos (finalDecay_pos hp hd) (Real.log_pos hp1)
  set C : ℝ := 2 * K + 4 * C_geomTail with hC_def
  have hC : 0 < C := by rw [hC_def]; have := C_geomTail_pos; positivity
  refine ⟨c₁, C, hc₁, hC, ?_⟩
  intro n n' X hsize hnp hmod
  have hsize' : (muP F.p + c₀) * n ≤ (n' : ℝ) := hsize
  set P := X.map fun N => F.valVec N n with hPdef
  set Q := PMF.iid (geomP F.p) n with hQdef
  set T : ℝ := ∑' a : Fin n → ℕ, if n' ≤ pre a n then (Q a).toReal else 0 with hTdef
  have htrunc : (P.map (truncateVec n n')).dTV (Q.map (truncateVec n n')) ≤
      K * (F.p : ℝ) ^ (-(n' : ℝ)) :=
    (F.truncated_val_dTV_le X n n' hnp).trans hmod
  have hrec := PMF.dTV_le_of_truncateVec P Q n'
  have hoverG : T ≤ C_geomTail * Gweight (1 + n) (c_geomTail * (c₀ * n)) :=
    geomP_overflow_le_Gweight hp c₀ hc₀ n n' hsize'
  have harg : c_geomTail * (c₀ * (n : ℝ)) = d * n := by rw [hd_def]; ring
  have hoverExp : T ≤ 2 * C_geomTail * Real.exp (-linearDecay d * n) := by
    calc
      T ≤ C_geomTail * Gweight (1 + n) (c_geomTail * (c₀ * n)) := hoverG
      _ = C_geomTail * Gweight (1 + n) (d * n) := by rw [harg]
      _ ≤ C_geomTail * (2 * Real.exp (-linearDecay d * n)) := by
        gcongr
        · exact C_geomTail_pos.le
        · exact Gweight_linear_le d hd n
      _ = 2 * C_geomTail * Real.exp (-linearDecay d * n) := by ring
  have hn'n : (n : ℝ) ≤ n' := by
    have hmu := one_lt_muP hp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hresDecay : (F.p : ℝ) ^ (-(n' : ℝ)) ≤ (F.p : ℝ) ^ (-c₁ * (n : ℝ)) :=
    rpow_neg_nat_le hp d hd n n' hn'n
  have hgeomDecay : Real.exp (-linearDecay d * n) ≤ (F.p : ℝ) ^ (-c₁ * (n : ℝ)) :=
    exp_linearDecay_le_rpow hp d n
  have hCt := C_geomTail_pos
  calc
    P.dTV Q ≤ 2 * (P.map (truncateVec n n')).dTV (Q.map (truncateVec n n')) + 2 * T := hrec
    _ ≤ 2 * (K * (F.p : ℝ) ^ (-(n' : ℝ))) +
        2 * (2 * C_geomTail * Real.exp (-linearDecay d * n)) := by gcongr
    _ ≤ 2 * (K * (F.p : ℝ) ^ (-c₁ * (n : ℝ))) +
        2 * (2 * C_geomTail * (F.p : ℝ) ^ (-c₁ * (n : ℝ))) := by
      gcongr
    _ = C * (F.p : ℝ) ^ (-c₁ * (n : ℝ)) := by rw [hC_def]; ring

theorem rpow_decay_mono {p : ℕ} (hp : 2 ≤ p) {c c' : ℝ} (hcc' : c ≤ c') (n : ℕ) :
    (p : ℝ) ^ (-c' * (n : ℝ)) ≤ (p : ℝ) ^ (-c * (n : ℝ)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  apply Real.rpow_le_rpow_of_exponent_le hp1
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- **Tail of the total valuation** (counterpart of tao-collatz's Lemma 4.1; the `n` form of (ineq:atail) in
the proof of GGM Proposition 3.1): under the same hypotheses as Proposition 3.1, the probability that the total
valuation `|a⁽ⁿ⁾(X)|` is at least `n'` is at most `C p^{-cn}`. -/
theorem valuation_tail (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 0 < K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n n' : ℕ) (X : PMF ℕ),
      ((F.p : ℝ) / ((F.p : ℝ) - 1) + c₀) * n ≤ (n' : ℝ) →
      (∀ N ∈ X.support, N % F.p ≠ 0) →
      PMF.dTV (X.map fun N => (N : ZMod (F.p ^ n'))) (F.unifNpMod n')
        ≤ K * (F.p : ℝ) ^ (-(n' : ℝ)) →
      (X.map fun N => pre (F.valVec N n) n).expect (Set.indicator {L | n' ≤ L} 1)
        ≤ C * (F.p : ℝ) ^ (-c * (n : ℝ)) := by
  have hp := F.two_le_p
  have hp1 : (1 : ℝ) < F.p := by exact_mod_cast (by omega : 1 < F.p)
  obtain ⟨cd, Cd, hcd, hCd, hdist⟩ := F.prop33 c₀ K hc₀ hK
  set d : ℝ := c_geomTail * c₀ with hd_def
  have hd : 0 < d := mul_pos c_geomTail_pos hc₀
  set cg : ℝ := finalDecay F.p d / Real.log F.p with hcg_def
  have hcg : 0 < cg := div_pos (finalDecay_pos hp hd) (Real.log_pos hp1)
  set c : ℝ := min cd cg with hc_def
  set C : ℝ := Cd + 2 * C_geomTail with hC_def
  have hc : 0 < c := lt_min hcd hcg
  have hCt := C_geomTail_pos
  have hC : 0 < C := by rw [hC_def]; positivity
  refine ⟨c, C, hc, hC, ?_⟩
  intro n n' X hsize hnp hmod
  have hsize' : (muP F.p + c₀) * n ≤ (n' : ℝ) := hsize
  set P := X.map fun N => F.valVec N n with hPdef
  set Q := PMF.iid (geomP F.p) n with hQdef
  set E : Set (Fin n → ℕ) := {a | n' ≤ pre a n} with hEdef
  set T : ℝ := Q.expect (Set.indicator E 1) with hTdef
  have htarget :
      (X.map fun N => pre (F.valVec N n) n).expect (Set.indicator {L | n' ≤ L} 1) =
        P.expect (Set.indicator E 1) := by
    have hleft := PMF.expect_map_of_nonneg X (fun N => pre (F.valVec N n) n)
      (Set.indicator {L : ℕ | n' ≤ L} 1)
      (fun L => Set.indicator_nonneg (fun _ _ => zero_le_one) L)
    have hright := PMF.expect_map_of_nonneg X (fun N => F.valVec N n)
      (Set.indicator E 1) (fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) a)
    rw [hleft, hright]
    apply tsum_congr
    intro N
    congr 1
  have hqevent : T =
      ∑' a : Fin n → ℕ, if n' ≤ pre a n then (Q a).toReal else 0 := by
    rw [hTdef, hEdef]
    unfold PMF.expect
    apply tsum_congr
    intro a
    simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, mul_ite, mul_one, mul_zero]
  have hdistPQ : P.dTV Q ≤ Cd * (F.p : ℝ) ^ (-cd * (n : ℝ)) :=
    hdist n n' X hsize hnp hmod
  have hevent := PMF.abs_expect_indicator_sub_le_dTV P Q E
  have hXevent : P.expect (Set.indicator E 1) ≤ T + P.dTV Q := by
    rw [hTdef]
    linarith [le_abs_self (P.expect (Set.indicator E 1) - Q.expect (Set.indicator E 1))]
  have hoverG : T ≤ C_geomTail * Gweight (1 + n) (c_geomTail * (c₀ * n)) := by
    rw [hqevent]
    exact geomP_overflow_le_Gweight hp c₀ hc₀ n n' hsize'
  have harg : c_geomTail * (c₀ * (n : ℝ)) = d * n := by rw [hd_def]; ring
  have hoverExp : T ≤ 2 * C_geomTail * Real.exp (-linearDecay d * n) := by
    calc
      T ≤ C_geomTail * Gweight (1 + n) (c_geomTail * (c₀ * n)) := hoverG
      _ = C_geomTail * Gweight (1 + n) (d * n) := by rw [harg]
      _ ≤ C_geomTail * (2 * Real.exp (-linearDecay d * n)) := by
        gcongr
        exact Gweight_linear_le d hd n
      _ = 2 * C_geomTail * Real.exp (-linearDecay d * n) := by ring
  have hgeom : Real.exp (-linearDecay d * n) ≤ (F.p : ℝ) ^ (-cg * (n : ℝ)) :=
    exp_linearDecay_le_rpow hp d n
  have hcdmono : (F.p : ℝ) ^ (-cd * (n : ℝ)) ≤ (F.p : ℝ) ^ (-c * (n : ℝ)) :=
    rpow_decay_mono hp (min_le_left cd cg) n
  have hcgmono : (F.p : ℝ) ^ (-cg * (n : ℝ)) ≤ (F.p : ℝ) ^ (-c * (n : ℝ)) :=
    rpow_decay_mono hp (min_le_right cd cg) n
  rw [htarget]
  calc
    P.expect (Set.indicator E 1) ≤ T + P.dTV Q := hXevent
    _ ≤ 2 * C_geomTail * Real.exp (-linearDecay d * n) +
        Cd * (F.p : ℝ) ^ (-cd * (n : ℝ)) := add_le_add hoverExp hdistPQ
    _ ≤ 2 * C_geomTail * (F.p : ℝ) ^ (-c * (n : ℝ)) +
        Cd * (F.p : ℝ) ^ (-c * (n : ℝ)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hgeom.trans hcgmono) (by positivity)
      · exact mul_le_mul_of_nonneg_left hcdmono hCd.le
    _ = C * (F.p : ℝ) ^ (-c * (n : ℝ)) := by rw [hC_def]; ring

end Family

end GGMCollatz
