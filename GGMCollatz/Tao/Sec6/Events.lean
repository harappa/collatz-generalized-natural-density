import GGMCollatz.Tao.Sec6.Tail

/-!
# Exceptional events and the decomposition by stopping time (the events `E_k`, the stopping time `k` and `M = 𝒢_{1,k+1}` of GGM §5 Step 1)

Derived from `TaoCollatz/Sec6/MixingError.lean` (first half) and `TaoCollatz/Sec6/MixingCore.lean`
(`cutEq`, `osc_cast'`, `castedTerm`, `mainDensity`, `osc_mainDensity_le`, `osc_syracZ_split_le`) of
gotrevor/tao-collatz (Apache-2.0), commit 15efca2; generalized to the GGM family (p, q, r).

The events of GGM §5 Step 1 are taken in the following form (the tail `vt` in reversed form consists of
the first `k + 1` variables of GGM):

* `stopEv T vt`: stopping time `k`: `𝒢_{1,k} ≤ T < 𝒢_{1,k+1}`.
* `windowEv s K l vt`: **window of linear deviation** `𝒢_{1,r} > s r - K` (`r ≤ k + 1`, `s < μ`). This is
  coarser than GGM's `E_k` (of type `√(r log n)`), but it suffices for the size estimate of Step 2
  (`two_abs_fint_lt`) and for the length of the head `n - k - 1 ≳ n`.
* `globalGood`: a cap `𝒢_i ≤ K_c` on each single component, and the window for all `r ≤ N`.

`mainDensity` is the sum of the conditioned densities over the pairs of stopping time `k` and `M = l`, and
`globalGood` is contained in `mainEvent` (`globalGood_mem_main`). Hence the `L¹` mass of the error is at
most `P(¬globalGood)`.
-/

open scoped BigOperators ENNReal

namespace GGMCollatz

namespace Mix

/-- The real density of the pushforward restricted to `E`. -/
noncomputable def restrictedDensity {α β : Type*} [Fintype β] [DecidableEq β]
    (P : PMF α) (X : α → β) (E : α → Prop) [DecidablePred E] : β → ℝ := fun Y =>
  ∑' a, (P a).toReal * (if X a = Y ∧ E a then 1 else 0)

theorem restrictedDensity_nonneg {α β : Type*} [Fintype β] [DecidableEq β]
    (P : PMF α) (X : α → β) (E : α → Prop) [DecidablePred E] (Y : β) :
    0 ≤ restrictedDensity P X E Y :=
  tsum_nonneg fun a => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num)

/-- The restricted pushforward loses in `L¹` exactly the mass of the complementary event. -/
theorem sum_abs_map_sub_restrictedDensity {α β : Type*} [Fintype β] [DecidableEq β]
    (P : PMF α) (X : α → β) (E : α → Prop) [DecidablePred E] :
    ∑ Y, |((P.map X) Y).toReal - restrictedDensity P X E Y|
      = ∑' a, if E a then 0 else (P a).toReal := by
  classical
  have hPsum : Summable fun a => (P a).toReal :=
    ENNReal.summable_toReal P.tsum_coe_ne_top
  have hPmass : ∑' a, (P a).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a => P.apply_ne_top a), P.tsum_coe,
      ENNReal.toReal_one]
  have hmap (Y : β) : ((P.map X) Y).toReal =
      ∑' a, (P a).toReal * (if X a = Y then 1 else 0) := by
    rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
    · refine tsum_congr fun a => ?_
      by_cases h : X a = Y
      · simp [h]
      · simp [h, Ne.symm h]
    · intro a
      by_cases h : Y = X a <;> simp [h, P.apply_ne_top a]
  have hrestSummable (Y : β) : Summable fun a =>
      (P a).toReal * (if X a = Y ∧ E a then 1 else 0) := by
    exact Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun a => by by_cases h : X a = Y ∧ E a <;> simp [h, ENNReal.toReal_nonneg]) hPsum
  have hfullSummable (Y : β) : Summable fun a =>
      (P a).toReal * (if X a = Y then 1 else 0) := by
    exact Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun a => by by_cases h : X a = Y <;> simp [h, ENNReal.toReal_nonneg]) hPsum
  have hrestricted_le (Y : β) :
      restrictedDensity P X E Y ≤ ((P.map X) Y).toReal := by
    rw [restrictedDensity, hmap]
    exact (hrestSummable Y).tsum_le_tsum
      (fun a => by
        gcongr
        by_cases hX : X a = Y <;> by_cases hE : E a <;> simp [hX, hE])
      (hfullSummable Y)
  have hcompSummable : Summable fun a => if E a then 0 else (P a).toReal := by
    exact Summable.of_nonneg_of_le
      (fun a => by by_cases h : E a <;> simp [h, ENNReal.toReal_nonneg])
      (fun a => by by_cases h : E a <;> simp [h, ENNReal.toReal_nonneg]) hPsum
  have heventSummable : Summable fun a => if E a then (P a).toReal else 0 := by
    exact Summable.of_nonneg_of_le
      (fun a => by by_cases h : E a <;> simp [h, ENNReal.toReal_nonneg])
      (fun a => by by_cases h : E a <;> simp [h, ENNReal.toReal_nonneg]) hPsum
  have hsumRestricted :
      ∑ Y, restrictedDensity P X E Y = ∑' a, if E a then (P a).toReal else 0 := by
    simp only [restrictedDensity]
    rw [← Summable.tsum_finsetSum (fun Y _ => hrestSummable Y)]
    apply tsum_congr
    intro a
    by_cases hE : E a <;> simp [hE]
  have hsplit :
      (∑' a, if E a then (P a).toReal else 0) +
          (∑' a, if E a then 0 else (P a).toReal) = 1 := by
    rw [← heventSummable.tsum_add hcompSummable]
    calc
      (∑' a, ((if E a then (P a).toReal else 0) +
          (if E a then 0 else (P a).toReal))) = ∑' a, (P a).toReal := by
            apply tsum_congr
            intro a
            by_cases h : E a <;> simp [h]
      _ = 1 := hPmass
  calc
    ∑ Y, |((P.map X) Y).toReal - restrictedDensity P X E Y|
        = ∑ Y, (((P.map X) Y).toReal - restrictedDensity P X E Y) := by
            apply Finset.sum_congr rfl
            intro Y _
            rw [abs_of_nonneg (sub_nonneg.mpr (hrestricted_le Y))]
    _ = (∑ Y, ((P.map X) Y).toReal) - ∑ Y, restrictedDensity P X E Y := by
          rw [Finset.sum_sub_distrib]
    _ = 1 - ∑' a, if E a then (P a).toReal else 0 := by
          rw [hsumRestricted]
          congr 1
          have hmass : ∑' Y, ((P.map X) Y).toReal = 1 := by
            rw [← ENNReal.tsum_toReal_eq (fun Y => (P.map X).apply_ne_top Y),
              (P.map X).tsum_coe, ENNReal.toReal_one]
          simpa only [tsum_fintype] using hmass
    _ = ∑' a, if E a then 0 else (P a).toReal := by linarith

/-- A finite sum of restricted pushforwards over disjoint events is the restriction to the union. -/
theorem sum_restrictedDensity_eq_union {α β ι : Type*} [Fintype β] [DecidableEq β]
    [DecidableEq ι] (P : PMF α) (X : α → β) (s : Finset ι)
    (E : ι → α → Prop) [∀ i, DecidablePred (E i)]
    [DecidablePred (fun a => ∃ i ∈ s, E i a)]
    (hdisj : ∀ a i, i ∈ s → ∀ i', i' ∈ s → E i a → E i' a → i = i') (Y : β) :
    ∑ i ∈ s, restrictedDensity P X (E i) Y =
      restrictedDensity P X (fun a => ∃ i ∈ s, E i a) Y := by
  classical
  have hPsum : Summable fun a => (P a).toReal :=
    ENNReal.summable_toReal P.tsum_coe_ne_top
  have hsummable (i : ι) : Summable fun a =>
      (P a).toReal * (if X a = Y ∧ E i a then 1 else 0) := by
    exact Summable.of_nonneg_of_le
      (fun a => mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num))
      (fun a => by by_cases h : X a = Y ∧ E i a <;> simp [h, ENNReal.toReal_nonneg]) hPsum
  simp only [restrictedDensity]
  rw [← Summable.tsum_finsetSum (fun i _ => hsummable i)]
  apply tsum_congr
  intro a
  rw [← Finset.mul_sum]
  congr 1
  by_cases hX : X a = Y
  · simp only [hX, true_and]
    by_cases hex : ∃ i ∈ s, E i a
    · obtain ⟨i, hi, hEi⟩ := hex
      rw [if_pos ⟨i, hi, hEi⟩, Finset.sum_eq_single i]
      · simp [hEi]
      · intro i' hi' hne
        rw [if_neg]
        exact fun hEi' => hne (hdisj a i hi i' hi' hEi hEi').symm
      · exact fun hnot => (hnot hi).elim
    · rw [if_neg hex]
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg]
      exact fun hEi => hex ⟨i, hi, hEi⟩
  · simp [hX]

end Mix

namespace Family

variable (F : Family)

/-! ### Transporting types along the cut -/

/-- The cut identity `(N-1-k) + (k+1) = N` at a stopping time `k < N`. -/
theorem cutEq {N k : ℕ} (h : k < N) : N - 1 - k + (k + 1) = N := by omega

/-- Transport the oscillation along an equality of levels. -/
theorem osc_cast' {a b m : ℕ} (h : a = b) (hma : m ≤ a) (hmb : m ≤ b)
    (f : ZMod (F.q ^ a) → ℝ) : F.osc m b hmb (h ▸ f) = F.osc m a hma f := by
  subst h; rfl

/-- The tail at cut `k` (the last `k + 1` components) of a vector at level `N`. -/
def cutTail {N : ℕ} (k : ℕ) (h : k < N) (v : Fin N → ℕ × ℕ) : Fin (k + 1) → ℕ × ℕ :=
  fun i => v (Fin.cast (cutEq h) (Fin.natAdd (N - 1 - k) i))

/-- The transported conditioned density is the restricted pushforward at level `n`. -/
theorem cast_condDensW_apply_eq_restricted (j P n l : ℕ) (e : j + P = n)
    (W : (Fin P → ℕ × ℕ) → Prop) [DecidablePred W] (Y : ZMod (F.q ^ n)) :
    (e ▸ F.condDensW j P l W) Y =
      Mix.restrictedDensity ((stepLaw F.p).iid n) (F.roff n)
        (fun v =>
          let vt : Fin P → ℕ × ℕ := fun i => v (Fin.cast e (Fin.natAdd j i))
          pre (fun i => (vt i).1) P = l ∧ W vt) Y := by
  subst n
  rfl

/-- The type of families of tail events (a predicate on tails for each cut `k` and each `M = l`). -/
abbrev TailFam : Type := (k l : ℕ) → (Fin (k + 1) → ℕ × ℕ) → Prop

open Classical in
/-- The event of the piece with cut `k` and `M = l` (on vectors at level `N`). -/
def pieceEvent (N : ℕ) (Wf : TailFam) (k l : ℕ) (v : Fin N → ℕ × ℕ) : Prop :=
  if h : k < N then
    pre (fun i => (cutTail k h v i).1) (k + 1) = l ∧ Wf k l (cutTail k h v)
  else False

open Classical in
/-- The conditioned density for cut `k` and `M = l`, transported to level `N`. -/
noncomputable def castedTerm (N : ℕ) (Wf : TailFam) (k l : ℕ) : ZMod (F.q ^ N) → ℝ :=
  if h : k < N then (cutEq h) ▸ F.condDensW (N - 1 - k) (k + 1) l (Wf k l) else 0

open Classical in
theorem castedTerm_apply_eq_pieceDensity (N : ℕ) (Wf : TailFam) (k l : ℕ) (Y : ZMod (F.q ^ N)) :
    F.castedTerm N Wf k l Y =
      Mix.restrictedDensity ((stepLaw F.p).iid N) (F.roff N) (pieceEvent N Wf k l) Y := by
  by_cases h : k < N
  · unfold castedTerm
    rw [dif_pos h, F.cast_condDensW_apply_eq_restricted (N - 1 - k) (k + 1) N l (cutEq h)
      (Wf k l) Y]
    unfold Mix.restrictedDensity
    congr 1
    funext v
    congr 2
    simp only [pieceEvent, dif_pos h]
    rfl
  · unfold castedTerm
    rw [dif_neg h]
    simp [Mix.restrictedDensity, pieceEvent, h]

open Classical in
/-- The oscillation of a piece is the oscillation of the conditioned density at the original level. -/
theorem osc_castedTerm (N m k l : ℕ) (hmn : m ≤ N) (hkn : k < N) (Wf : TailFam) :
    F.osc m N hmn (F.castedTerm N Wf k l)
      = F.osc m (N - 1 - k + (k + 1)) (by rw [cutEq hkn]; exact hmn)
          (F.condDensW (N - 1 - k) (k + 1) l (Wf k l)) := by
  unfold castedTerm
  rw [dif_pos hkn]
  exact F.osc_cast' (cutEq hkn) _ hmn _

/-- **The main density**: the sum of the pieces over the pairs `(k, l) ∈ S`. -/
noncomputable def mainDensity (N : ℕ) (Wf : TailFam) (S : Finset (ℕ × ℕ)) :
    ZMod (F.q ^ N) → ℝ := fun Y => ∑ kl ∈ S, F.castedTerm N Wf kl.1 kl.2 Y

open Classical in
/-- The oscillation of the main density is at most the sum of the oscillations of the pieces at their original levels. -/
theorem osc_mainDensity_le (N m : ℕ) (hmn : m ≤ N) (Wf : TailFam) (S : Finset (ℕ × ℕ))
    (B : ℕ × ℕ → ℝ)
    (hterm : ∀ kl ∈ S, ∀ hkn : kl.1 < N,
      F.osc m (N - 1 - kl.1 + (kl.1 + 1)) (by rw [cutEq hkn]; exact hmn)
        (F.condDensW (N - 1 - kl.1) (kl.1 + 1) kl.2 (Wf kl.1 kl.2)) ≤ B kl)
    (hB : ∀ kl ∈ S, 0 ≤ B kl) :
    F.osc m N hmn (F.mainDensity N Wf S) ≤ ∑ kl ∈ S, B kl := by
  unfold mainDensity
  refine le_trans (F.osc_sum_le m N hmn S (fun kl Y => F.castedTerm N Wf kl.1 kl.2 Y)) ?_
  refine Finset.sum_le_sum (fun kl hkl => ?_)
  by_cases hkn : kl.1 < N
  · rw [show (fun Y => F.castedTerm N Wf kl.1 kl.2 Y) = F.castedTerm N Wf kl.1 kl.2 from rfl,
      F.osc_castedTerm N m kl.1 kl.2 hmn hkn Wf]
    exact hterm kl hkl hkn
  · have hz : (fun Y => F.castedTerm N Wf kl.1 kl.2 Y) = fun _ => 0 := by
      funext Y; unfold castedTerm; rw [dif_neg hkn]; rfl
    rw [hz]
    simp only [osc, sub_self, mul_zero, abs_zero, Finset.sum_const_zero]
    exact hB kl hkl

/-- Splitting into main part and error: `Osc(𝒮_N) ≤ Osc(main) + 2 ∑ |𝒮_N - main|`. -/
theorem osc_syracZ_split_le (m N : ℕ) (hmn : m ≤ N) (main : ZMod (F.q ^ N) → ℝ) :
    F.osc m N hmn (fun Y => (F.syracZ N Y).toReal)
      ≤ F.osc m N hmn main + 2 * ∑ Y, |(F.syracZ N Y).toReal - main Y| := by
  have hsplit : (fun Y => (F.syracZ N Y).toReal)
      = (fun Y => main Y + ((F.syracZ N Y).toReal - main Y)) := by funext Y; ring
  rw [hsplit]
  refine le_trans (F.osc_add_le m N hmn main (fun Y => (F.syracZ N Y).toReal - main Y)) ?_
  exact add_le_add (le_refl _) (F.osc_le_two_mul_l1 m N hmn _)

/-! ### Prefix sums and transported tails -/

theorem pre_cast_tail_eq_sub (j P n : ℕ) (e : j + P = n) (a : Fin n → ℕ) :
    pre (fun i : Fin P => a (Fin.cast e (Fin.natAdd j i))) P = pre a n - pre a j := by
  subst n
  simp only [Fin.cast_eq_self]
  have hsplit := pre_natAdd_split a (m := P) le_rfl
  omega

theorem pre_cast_tail_prefix (j P n s : ℕ) (hs : s ≤ P) (e : j + P = n) (a : Fin n → ℕ) :
    pre (fun i : Fin P => a (Fin.cast e (Fin.natAdd j i))) s = pre a (j + s) - pre a j := by
  subst n
  simp only [Fin.cast_eq_self]
  have hsplit := pre_natAdd_split a (m := s) hs
  omega

theorem pre_cast_tail_sub_first_eq_sub (j P n : ℕ) (hp : 1 ≤ P) (e : j + P = n)
    (a : Fin n → ℕ) :
    pre (fun i : Fin P => a (Fin.cast e (Fin.natAdd j i))) P -
        pre (fun i : Fin P => a (Fin.cast e (Fin.natAdd j i))) 1 =
      pre a n - pre a (j + 1) := by
  subst n
  simp only [Fin.cast_eq_self]
  have hfull := pre_natAdd_split a (m := P) le_rfl
  have hone := pre_natAdd_split a (m := 1) hp
  omega

/-! ### The GGM events -/

/-- **The stopping event** (tail in reversed form, length `P`): `𝒢_{1,P-1} ≤ T < 𝒢_{1,P}`. -/
def stopEv (T : ℝ) {P : ℕ} (vt : Fin P → ℕ × ℕ) : Prop :=
  (pre (fun i => (vt i).1) P : ℝ) - (pre (fun i => (vt i).1) 1 : ℝ) ≤ T
    ∧ T < (pre (fun i => (vt i).1) P : ℝ)

/-- **The suffix window** (linear deviation): `a_{[1,P-r]} ≤ l - s r + K` (`1 ≤ r ≤ P`). -/
def windowEv (s K : ℝ) (l : ℕ) {P : ℕ} (vt : Fin P → ℕ × ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ P → (pre (fun i => (vt i).1) (P - r) : ℝ) ≤ l - s * r + K

/-- The GGM family of tail events (stopping and window). -/
def ggmW (T s K : ℝ) : TailFam := fun _ l vt => stopEv T vt ∧ windowEv s K l vt

/-- The stopping event determines the cut uniquely. -/
theorem pieceEvent_cut_unique (N k k' l l' : ℕ) (T s K : ℝ) (v : Fin N → ℕ × ℕ)
    (hk : pieceEvent N (ggmW T s K) k l v) (hk' : pieceEvent N (ggmW T s K) k' l' v) :
    k = k' := by
  simp only [pieceEvent] at hk hk'
  split at hk <;> rename_i hkn
  · split at hk' <;> rename_i hk'n
    · rcases hk with ⟨_, hstop, _⟩
      rcases hk' with ⟨_, hstop', _⟩
      set a : Fin N → ℕ := fun i => (v i).1 with ha
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hsum := pre_cast_tail_eq_sub (N - 1 - k) (k + 1) N (cutEq hkn) a
        have hpred := pre_cast_tail_sub_first_eq_sub (N - 1 - k') (k' + 1) N
          (by omega) (cutEq hk'n) a
        have hpref : pre a ((N - 1 - k') + 1) ≤ pre a (N - 1 - k) := pre_mono a (by omega)
        have hnat : pre (fun i => (cutTail k hkn v i).1) (k + 1)
            ≤ pre (fun i => (cutTail k' hk'n v i).1) (k' + 1)
              - pre (fun i => (cutTail k' hk'n v i).1) 1 := by
          show pre (fun i : Fin (k + 1) => a (Fin.cast (cutEq hkn) (Fin.natAdd (N - 1 - k) i)))
              (k + 1) ≤ pre (fun i : Fin (k' + 1) => a (Fin.cast (cutEq hk'n)
                (Fin.natAdd (N - 1 - k') i))) (k' + 1)
              - pre (fun i : Fin (k' + 1) => a (Fin.cast (cutEq hk'n)
                (Fin.natAdd (N - 1 - k') i))) 1
          rw [hsum, hpred]
          exact Nat.sub_le_sub_left hpref (pre a N)
        have hone : pre (fun i => (cutTail k' hk'n v i).1) 1
            ≤ pre (fun i => (cutTail k' hk'n v i).1) (k' + 1) := pre_mono _ (by omega)
        have hreal : (pre (fun i => (cutTail k hkn v i).1) (k + 1) : ℝ)
            ≤ (pre (fun i => (cutTail k' hk'n v i).1) (k' + 1) : ℝ)
              - (pre (fun i => (cutTail k' hk'n v i).1) 1 : ℝ) := by
          rw [← Nat.cast_sub hone]
          exact_mod_cast hnat
        exact (not_lt_of_ge (hreal.trans hstop'.1)) hstop.2
      · have hsum := pre_cast_tail_eq_sub (N - 1 - k') (k' + 1) N (cutEq hk'n) a
        have hpred := pre_cast_tail_sub_first_eq_sub (N - 1 - k) (k + 1) N
          (by omega) (cutEq hkn) a
        have hpref : pre a ((N - 1 - k) + 1) ≤ pre a (N - 1 - k') := pre_mono a (by omega)
        have hnat : pre (fun i => (cutTail k' hk'n v i).1) (k' + 1)
            ≤ pre (fun i => (cutTail k hkn v i).1) (k + 1)
              - pre (fun i => (cutTail k hkn v i).1) 1 := by
          show pre (fun i : Fin (k' + 1) => a (Fin.cast (cutEq hk'n) (Fin.natAdd (N - 1 - k') i)))
              (k' + 1) ≤ pre (fun i : Fin (k + 1) => a (Fin.cast (cutEq hkn)
                (Fin.natAdd (N - 1 - k) i))) (k + 1)
              - pre (fun i : Fin (k + 1) => a (Fin.cast (cutEq hkn)
                (Fin.natAdd (N - 1 - k) i))) 1
          rw [hsum, hpred]
          exact Nat.sub_le_sub_left hpref (pre a N)
        have hone : pre (fun i => (cutTail k hkn v i).1) 1
            ≤ pre (fun i => (cutTail k hkn v i).1) (k + 1) := pre_mono _ (by omega)
        have hreal : (pre (fun i => (cutTail k' hk'n v i).1) (k' + 1) : ℝ)
            ≤ (pre (fun i => (cutTail k hkn v i).1) (k + 1) : ℝ)
              - (pre (fun i => (cutTail k hkn v i).1) 1 : ℝ) := by
          rw [← Nat.cast_sub hone]
          exact_mod_cast hnat
        exact (not_lt_of_ge (hreal.trans hstop.1)) hstop'.2
    · exact hk'.elim
  · exact hk.elim

theorem pieceEvent_index_unique (N k k' l l' : ℕ) (T s K : ℝ) (v : Fin N → ℕ × ℕ)
    (hk : pieceEvent N (ggmW T s K) k l v) (hk' : pieceEvent N (ggmW T s K) k' l' v) :
    (k, l) = (k', l') := by
  have hkk := pieceEvent_cut_unique N k k' l l' T s K v hk hk'
  subst k'
  have hll : l = l' := by
    by_cases hkn : k < N
    · simp only [pieceEvent, dif_pos hkn] at hk hk'
      exact hk.1.symm.trans hk'.1
    · simp only [pieceEvent, dif_neg hkn] at hk
  subst l'
  rfl

open Classical in
/-- The main event: the piece of some pair `(k, l) ∈ S` occurs. -/
def mainEvent (N : ℕ) (T s K : ℝ) (S : Finset (ℕ × ℕ)) (v : Fin N → ℕ × ℕ) : Prop :=
  ∃ kl ∈ S, pieceEvent N (ggmW T s K) kl.1 kl.2 v

open Classical in
/-- The main density is the pushforward restricted to the main event. -/
theorem mainDensity_eq_restrictedDensity (N : ℕ) (T s K : ℝ) (S : Finset (ℕ × ℕ))
    (Y : ZMod (F.q ^ N)) :
    F.mainDensity N (ggmW T s K) S Y =
      Mix.restrictedDensity ((stepLaw F.p).iid N) (F.roff N) (mainEvent N T s K S) Y := by
  unfold mainDensity
  simp only [castedTerm_apply_eq_pieceDensity]
  have hdisj : ∀ v kl, kl ∈ S → ∀ kl', kl' ∈ S →
      pieceEvent N (ggmW T s K) kl.1 kl.2 v → pieceEvent N (ggmW T s K) kl'.1 kl'.2 v →
        kl = kl' := by
    intro v kl _ kl' _ hE hE'
    exact pieceEvent_index_unique N kl.1 kl'.1 kl.2 kl'.2 T s K v hE hE'
  rw [Mix.sum_restrictedDensity_eq_union ((stepLaw F.p).iid N) (F.roff N) S
    (fun kl => pieceEvent N (ggmW T s K) kl.1 kl.2) hdisj Y]
  unfold Mix.restrictedDensity
  refine tsum_congr (fun v => ?_)
  congr 1
  exact if_congr Iff.rfl rfl rfl

open Classical in
/-- The `L¹` mass of the error is the probability of the complement of the main event. -/
theorem sum_abs_syracZ_sub_main_eq (N : ℕ) (T s K : ℝ) (S : Finset (ℕ × ℕ)) :
    ∑ Y, |(F.syracZ N Y).toReal - F.mainDensity N (ggmW T s K) S Y| =
      ∑' v : Fin N → ℕ × ℕ, if mainEvent N T s K S v then 0
        else (((stepLaw F.p).iid N) v).toReal := by
  rw [syracZ_eq_roff]
  simp_rw [mainDensity_eq_restrictedDensity]
  exact Mix.sum_abs_map_sub_restrictedDensity ((stepLaw F.p).iid N) (F.roff N)
    (mainEvent N T s K S)

/-! ### From the good event to the main event -/

/-- **The good event**: a cap `𝒢_i ≤ K_c` on each single component, and the window `𝒢_{1,r} > s r - K_w` for all `r ≤ N`. -/
def globalGood (N : ℕ) (s Kc Kw : ℝ) (v : Fin N → ℕ × ℕ) : Prop :=
  (∀ i : Fin N, ((v i).1 : ℝ) ≤ Kc)
    ∧ (∀ r : ℕ, 1 ≤ r → r ≤ N → s * r - Kw < (sufSum (fun i => (v i).1) r : ℝ))

/-- Adding one component: `sufSum (k+1) = sufSum k + a_{N-1-k}`. -/
theorem sufSum_succ {N : ℕ} (a : Fin N → ℕ) (k : ℕ) (hk : k < N) :
    sufSum a (k + 1) = sufSum a k + a ⟨N - 1 - k, by omega⟩ := by
  have hlt : N - 1 - k < N := by omega
  have hpre : pre a (N - k) = pre a (N - 1 - k) + a ⟨N - 1 - k, hlt⟩ := by
    rw [show N - k = (N - 1 - k) + 1 from by omega, pre_succ, dif_pos hlt]
  have hle2 : pre a (N - k) ≤ pre a N := pre_mono a (by omega)
  simp only [sufSum, show N - (k + 1) = N - 1 - k from by omega]
  omega

theorem sufSum_zero {N : ℕ} (a : Fin N → ℕ) : sufSum a 0 = 0 := by simp [sufSum]

theorem sufSum_full {N : ℕ} (a : Fin N → ℕ) : sufSum a N = pre a N := by
  simp [sufSum]

/-- **The good event lies in the main event** (the construction of the stopping time in GGM §5 Step 1):
if `0 < T`, `0 ≤ K_w` and `T ≤ s N - K_w` (existence of a crossing), then for good `v` there are a stopping
time `k` and `l = 𝒢_{1,k+1}` with `k < N`, `s k < T + K_w`, `T < l ≤ T + K_c`, and the event of the piece
occurs. -/
theorem globalGood_piece (N : ℕ) (T s Kc Kw : ℝ) (v : Fin N → ℕ × ℕ)
    (hT : 0 < T) (hKw : 0 ≤ Kw) (hcross : T ≤ s * N - Kw) (hg : globalGood N s Kc Kw v) :
    ∃ k l : ℕ, k < N ∧ s * k < T + Kw ∧ T < (l : ℝ) ∧ (l : ℝ) ≤ T + Kc
      ∧ pieceEvent N (ggmW T s Kw) k l v := by
  classical
  obtain ⟨hG2, hG3⟩ := hg
  set a : Fin N → ℕ := fun i => (v i).1 with ha
  set pr : ℕ → Prop := fun r => T < (sufSum a r : ℝ) with hpr
  have hN1 : 1 ≤ N := by
    by_contra h0
    have hN0 : N = 0 := by omega
    subst hN0
    simp at hcross
    linarith
  have hpn : pr N := by
    have := hG3 N hN1 le_rfl
    simp only [hpr]; linarith
  have hex : ∃ r, pr r := ⟨N, hpn⟩
  have hp0 : ¬ pr 0 := by
    simp only [hpr, sufSum_zero, Nat.cast_zero]; exact not_lt.mpr hT.le
  set m0 := Nat.find hex with hm0
  have hm0spec : pr m0 := Nat.find_spec hex
  have hm0le : m0 ≤ N := Nat.find_min' hex hpn
  have hm0pos : 1 ≤ m0 := by
    rcases Nat.eq_zero_or_pos m0 with h | h
    · exact absurd (h ▸ hm0spec) hp0
    · exact h
  set k := m0 - 1 with hk
  have hkm0 : k + 1 = m0 := by omega
  have hkn : k < N := by omega
  have hstop_hi : T < (sufSum a (k + 1) : ℝ) := by rw [hkm0]; exact hm0spec
  have hstop_lo : (sufSum a k : ℝ) ≤ T := by
    have hnpk : ¬ pr k := Nat.find_min hex (by omega)
    exact not_lt.mp hnpk
  refine ⟨k, sufSum a (k + 1), hkn, ?_, hstop_hi, ?_, ?_⟩
  · -- `s k < T + K_w`
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simp; linarith
    · have := hG3 k hpos (by omega)
      linarith
  · -- `l ≤ T + K_c`
    rw [sufSum_succ a k hkn]
    push_cast
    have := hG2 ⟨N - 1 - k, by omega⟩
    linarith
  · -- the event of the piece
    have hjn : N - 1 - k = N - (k + 1) := by omega
    set vt := cutTail k hkn v with hvt
    have hvt_full : pre (fun i => (vt i).1) (k + 1) = pre a N - pre a (N - 1 - k) :=
      pre_cast_tail_eq_sub (N - 1 - k) (k + 1) N (cutEq hkn) a
    have hvt_pre : ∀ s', s' ≤ k + 1 →
        pre (fun i => (vt i).1) s' = pre a (N - 1 - k + s') - pre a (N - 1 - k) :=
      fun s' hs' => pre_cast_tail_prefix (N - 1 - k) (k + 1) N s' hs' (cutEq hkn) a
    have hA : pre (fun i => (vt i).1) (k + 1) = sufSum a (k + 1) := by
      rw [hvt_full, sufSum, hjn]
    unfold pieceEvent
    rw [dif_pos hkn]
    refine ⟨hA, ?_, ?_⟩
    · -- stopping
      have hpvt1 := hvt_pre 1 (by omega)
      have hnat : pre (fun i => (vt i).1) (k + 1)
          = pre (fun i => (vt i).1) 1 + sufSum a k := by
        rw [hvt_full, hpvt1, sufSum]
        have h1 : pre a (N - 1 - k) ≤ pre a (N - 1 - k + 1) := pre_mono a (by omega)
        have h2 : pre a (N - 1 - k + 1) ≤ pre a N := pre_mono a (by omega)
        have h3 : pre a (N - 1 - k + 1) = pre a (N - k) := by
          rw [show N - 1 - k + 1 = N - k from by omega]
        omega
      refine ⟨?_, ?_⟩
      · have hcast : (pre (fun i => (vt i).1) (k + 1) : ℝ) - (pre (fun i => (vt i).1) 1 : ℝ)
            = (sufSum a k : ℝ) := by
          have := congrArg (Nat.cast : ℕ → ℝ) hnat; push_cast at this ⊢; linarith
        rw [hcast]; exact hstop_lo
      · rw [hA]; exact hstop_hi
    · -- window
      intro r hr1 hrp
      have hsr : k + 1 - r ≤ k + 1 := by omega
      have hpvt : pre (fun i => (vt i).1) (k + 1 - r) = pre a (N - r) - pre a (N - 1 - k) := by
        rw [hvt_pre _ hsr]; congr 2; omega
      have hnat : sufSum a (k + 1) = pre (fun i => (vt i).1) (k + 1 - r) + sufSum a r := by
        rw [hpvt, sufSum, sufSum, hjn]
        have h1 : pre a (N - (k + 1)) ≤ pre a (N - r) := pre_mono a (by omega)
        have h2 : pre a (N - r) ≤ pre a N := pre_mono a (by omega)
        omega
      have hcast : (pre (fun i => (vt i).1) (k + 1 - r) : ℝ)
          = (sufSum a (k + 1) : ℝ) - (sufSum a r : ℝ) := by
        have := congrArg (Nat.cast : ℕ → ℝ) hnat; push_cast at this ⊢; linarith
      rw [hcast]
      have := hG3 r hr1 (by omega)
      linarith

end Family

end GGMCollatz
