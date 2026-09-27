import GGMCollatz.Tao.Sec7.FW79Enc

/-!
# GGM §7: bridge from the walk to the first-passage law (a component of Lemma 7.9, part 2)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/ManyTriangles.lean`
(`tsum_toReal_mul_le`, `tsum_bind_toReal`, `tsum_map_toReal`, `fpDist_tsum_toReal`, `encStep_shift`,
`encExpect_block_le`); generalized to the GGM family (p, q, r). Modified.

* `pmf_tsum_toReal_mul_le`, `pmf_tsum_bind_toReal`, `pmf_tsum_map_toReal`: tools for real sums against a `PMF`.
* `fpDist_mass_toReal`: `∑' (fpDist s e).toReal = 1`.
* `encStep_shift`: translation of the starting point.
* `encExpect_block_le` (**bridge**): from a state with budget `s = barrier - pos₂` to the barrier, the walk until it crosses
  the barrier is invisible to the convolution (no encounter occurs, and intermediate white points are discarded by monotonicity), so the expectation is
  dominated via the first-passage endpoint law `fpDist s`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace FW

/-- The `PMF` sum of an observable with values in `[0, B]` is `≤ B` (`tsum_toReal_mul_le` of tao-collatz). -/
theorem pmf_tsum_toReal_mul_le {α : Type*} (p : PMF α) (g : α → ℝ)
    (hg0 : ∀ e, 0 ≤ g e) {B : ℝ} (hgB : ∀ e, g e ≤ B) :
    ∑' e, (p e).toReal * g e ≤ B := by
  have hsum : Summable (fun e => (p e).toReal) :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)
  have hle : ∀ e, (p e).toReal * g e ≤ (p e).toReal * B :=
    fun e => mul_le_mul_of_nonneg_left (hgB e) ENNReal.toReal_nonneg
  have hsumR : Summable (fun e => (p e).toReal * B) := hsum.mul_right _
  have hsumL : Summable (fun e => (p e).toReal * g e) :=
    Summable.of_nonneg_of_le
      (fun e => mul_nonneg ENNReal.toReal_nonneg (hg0 e)) hle hsumR
  calc ∑' e, (p e).toReal * g e ≤ ∑' e, (p e).toReal * B :=
        Summable.tsum_le_tsum hle hsumL hsumR
    _ = B := by
        rw [tsum_mul_right, ← ENNReal.tsum_toReal_eq (fun e => PMF.apply_ne_top _ _),
          p.tsum_coe, ENNReal.toReal_one, one_mul]

/-- Fubini for real sums against `bind` (`tsum_bind_toReal` of tao-collatz). -/
theorem pmf_tsum_bind_toReal {α β : Type*} (p : PMF α) (K : α → PMF β) (g : β → ℝ)
    (hg0 : ∀ e, 0 ≤ g e) {B : ℝ} (hgB : ∀ e, g e ≤ B) :
    ∑' e, ((p.bind K) e).toReal * g e
      = ∑' a, (p a).toReal * ∑' e, ((K a) e).toReal * g e := by
  rw [← PMF.toReal_tsum_mul_ofReal (p.bind K) g hg0, PMF.tsum_bind_mul,
    ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (calc ∑' e, (K a) e * ENNReal.ofReal (g e)
            ≤ ∑' e, (K a) e * ENNReal.ofReal B :=
              ENNReal.tsum_le_tsum fun e =>
                mul_le_mul_right (ENNReal.ofReal_le_ofReal (hgB e)) _
          _ = ENNReal.ofReal B := by
              rw [ENNReal.tsum_mul_right, (K a).tsum_coe, one_mul])))]
  exact tsum_congr fun a => by
    rw [ENNReal.toReal_mul, PMF.toReal_tsum_mul_ofReal (K a) g hg0]

/-- Reindexing real sums against a pushforward (`tsum_map_toReal` of tao-collatz). -/
theorem pmf_tsum_map_toReal {α β : Type*} (p : PMF α) (φ : α → β) (g : β → ℝ)
    (hg0 : ∀ e, 0 ≤ g e) :
    ∑' e, ((p.map φ) e).toReal * g e = ∑' a, (p a).toReal * g (φ a) := by
  rw [← PMF.toReal_tsum_mul_ofReal (p.map φ) g hg0, PMF.tsum_map_mul,
    PMF.toReal_tsum_mul_ofReal p (fun a => g (φ a)) (fun a => hg0 _)]

end FW

namespace Family

namespace FW

variable (F : Family)

/-- `∑' (fpDist s e).toReal = 1`. -/
theorem fpDist_mass_toReal (s : ℕ) : ∑' e : ℕ × ℤ, (F.fpDist s e).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun e => PMF.apply_ne_top _ _), (F.fpDist s).tsum_coe,
    ENNReal.toReal_one]

/-- Translation of the starting point (`encStep_shift` of tao-collatz). -/
theorem encStep_shift {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (st : EncState) (d e : ℕ × ℤ) :
    encStep F T R g ⟨st.pos + d, st.barrier, st.count, st.cumWhite, st.banked⟩ e
      = encStep F T R g st (d + e) := by
  have hpe : st.pos + d + e = st.pos + (d + e) := add_assoc _ _ _
  unfold encStep
  dsimp only
  rw [hpe]

/-- **Bridge from the walk to the first-passage law** (`encExpect_block_le` of tao-collatz): from a state `st` with budget
`s = barrier - pos₂`, for every horizon `Tw` and every `f` with values in `[0, B]` dominating the continuation after the step
crossing the barrier and `encVal st`, we have `encExpect Tw st ≤ Σ' fpDist s (e) f e`. -/
theorem encExpect_block_le {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) :
    ∀ s : ℕ, ∀ st : EncState, (s : ℤ) = st.barrier - st.pos.2 →
    ∀ Tw : ℕ,
    ∀ f : ℕ × ℤ → ℝ, (∀ e, 0 ≤ f e) → ∀ B : ℝ, (∀ e, f e ≤ B) →
    (∀ e : ℕ × ℤ, encVal κ R st ≤ f e) →
    (∀ e : ℕ × ℤ, (s : ℤ) < e.2 → ∀ T' : ℕ, T' < Tw →
      encExpect F T R g κ T' (encStep F T R g st e) ≤ f e) →
    encExpect F T R g κ Tw st ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * f e := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s IH =>
    intro st hs Tw f hg0 B hgB hf1 hg
    classical
    rcases Tw with _ | T'
    · rw [encExpect_zero]
      have hsum0 : Summable (fun e : ℕ × ℤ => (F.fpDist s e).toReal) :=
        ENNReal.summable_toReal (by rw [(F.fpDist s).tsum_coe]; exact ENNReal.one_ne_top)
      have hle0 : ∀ e : ℕ × ℤ,
          (F.fpDist s e).toReal * encVal κ R st ≤ (F.fpDist s e).toReal * f e :=
        fun e => mul_le_mul_of_nonneg_left (hf1 e) ENNReal.toReal_nonneg
      have hsumR0 : Summable (fun e : ℕ × ℤ => (F.fpDist s e).toReal * f e) :=
        Summable.of_nonneg_of_le
          (fun e => mul_nonneg ENNReal.toReal_nonneg (hg0 e))
          (fun e => mul_le_mul_of_nonneg_left (hgB e) ENNReal.toReal_nonneg)
          (hsum0.mul_right B)
      calc encVal κ R st
          = ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * encVal κ R st := by
            rw [tsum_mul_right, fpDist_mass_toReal, one_mul]
        _ ≤ ∑' e : ℕ × ℤ, (F.fpDist s e).toReal * f e :=
            Summable.tsum_le_tsum hle0 (hsum0.mul_right _) hsumR0
    rw [encExpect_succ F T R g κ hκ T' st]
    conv_rhs => rw [fpDist]
    rw [GGMCollatz.FW.pmf_tsum_bind_toReal F.hold _ f hg0 hgB]
    have hterm : ∀ d : ℕ × ℤ,
        (F.hold d).toReal * encExpect F T R g κ T' (encStep F T R g st d)
          ≤ (F.hold d).toReal * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
              else (F.fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) :
                PMF (ℕ × ℤ)) e).toReal * f e := by
      intro d
      rcases eq_or_ne (F.hold d) 0 with h0 | h0
      · rw [h0]; simp
      have hd3 : 3 ≤ d.2 := F.hold_support_snd_ge d (by rwa [PMF.mem_support_iff])
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      rcases lt_or_ge (s : ℤ) d.2 with hover | hunder
      · rw [if_pos (Or.inr hover)]
        calc encExpect F T R g κ T' (encStep F T R g st d) ≤ f d := hg d hover T' (by omega)
          _ = ∑' e, ((PMF.pure d : PMF (ℕ × ℤ)) e).toReal * f e := by
              rw [tsum_eq_single d (fun e he => by
                rw [PMF.pure_apply, if_neg he]; simp)]
              rw [PMF.pure_apply, if_pos rfl]; simp
      · rw [if_neg (by push Not; exact ⟨by omega, hunder⟩)]
        have hnc : ¬(1 ≤ (st.pos + d).1 ∧ (st.pos + d).1 + g ≤ half
            ∧ ((st.pos + d).1 - 1, (st.pos + d).2) ∈ T.blk ∧ st.barrier < (st.pos + d).2) := by
          rintro ⟨-, -, -, hbar⟩
          have : (st.pos + d).2 = st.pos.2 + d.2 := rfl
          omega
        have hstep : encStep F T R g st d
            = ⟨st.pos + d, st.barrier, st.count,
                st.cumWhite + (if st.pos + d ∈ whiteStrip half T.W then 1 else 0),
                st.banked⟩ := by
          rw [encStep, if_neg hnc]
        have hdrop : encExpect F T R g κ T' (encStep F T R g st d)
            ≤ encExpect F T R g κ T'
                ⟨st.pos + d, st.barrier, st.count, st.cumWhite, st.banked⟩ := by
          rw [hstep]
          exact encExpect_anti F T R g κ hκ T' _ _ rfl rfl rfl (Nat.le_add_right _ _)
            (le_refl _)
        set s'' : ℕ := s - d.2.toNat with hs''
        have hrec : encExpect F T R g κ T'
              ⟨st.pos + d, st.barrier, st.count, st.cumWhite, st.banked⟩
            ≤ ∑' e', (F.fpDist s'' e').toReal * f (d + e') := by
          refine IH s'' (by omega) _ ?_ T' _ (fun e' => hg0 _) B
            (fun e' => hgB _) (fun e' => hf1 (d + e')) ?_
          · show (s'' : ℤ) = st.barrier - (st.pos + d).2
            have : (st.pos + d).2 = st.pos.2 + d.2 := rfl
            omega
          · intro e' he' T'' hT''
            rw [encStep_shift]
            refine hg (d + e') ?_ T'' (by omega)
            have h2 : (d + e').2 = d.2 + e'.2 := rfl
            omega
        rw [GGMCollatz.FW.pmf_tsum_map_toReal _ _ f hg0]
        exact le_trans (le_trans hdrop hrec) (le_of_eq (tsum_congr fun e' => by rfl))
    have hsum : Summable (fun d : ℕ × ℤ => (F.hold d).toReal) :=
      ENNReal.summable_toReal (by rw [F.hold.tsum_coe]; exact ENNReal.one_ne_top)
    have hnnL : ∀ d : ℕ × ℤ,
        0 ≤ (F.hold d).toReal * encExpect F T R g κ T' (encStep F T R g st d) :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (encExpect_nonneg F T R g κ T' _)
    have hboundL : ∀ d : ℕ × ℤ,
        (F.hold d).toReal * encExpect F T R g κ T' (encStep F T R g st d)
          ≤ (F.hold d).toReal * Real.exp (κ * R) :=
      fun d => mul_le_mul_of_nonneg_left (encExpect_le F T R g κ hκ T' _)
        ENNReal.toReal_nonneg
    have hsumL : Summable (fun d : ℕ × ℤ =>
        (F.hold d).toReal * encExpect F T R g κ T' (encStep F T R g st d)) :=
      Summable.of_nonneg_of_le hnnL hboundL (hsum.mul_right _)
    have hnnR : ∀ d : ℕ × ℤ, 0 ≤ (F.hold d).toReal
        * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (F.fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) :
              PMF (ℕ × ℤ)) e).toReal * f e :=
      fun d => mul_nonneg ENNReal.toReal_nonneg (tsum_nonneg fun e =>
        mul_nonneg ENNReal.toReal_nonneg (hg0 e))
    have hboundR : ∀ d : ℕ × ℤ, (F.hold d).toReal
        * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (F.fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) :
              PMF (ℕ × ℤ)) e).toReal * f e ≤ (F.hold d).toReal * B :=
      fun d => mul_le_mul_of_nonneg_left
        (GGMCollatz.FW.pmf_tsum_toReal_mul_le _ f hg0 hgB) ENNReal.toReal_nonneg
    have hsumR : Summable (fun d : ℕ × ℤ => (F.hold d).toReal
        * ∑' e, (((if d.2 ≤ 0 ∨ (s : ℤ) < d.2 then PMF.pure d
            else (F.fpDist (s - d.2.toNat)).map fun e => (d.1 + e.1, d.2 + e.2)) :
              PMF (ℕ × ℤ)) e).toReal * f e) :=
      Summable.of_nonneg_of_le hnnR hboundR (hsum.mul_right _)
    exact Summable.tsum_le_tsum hterm hsumL hsumR

end FW

end Family

end GGMCollatz
