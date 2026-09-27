import GGMCollatz.Tao.Sec7.TriBasic

/-!
# Tools for GGM §6 Step 2: the corner map `(j,l) ↦ (j*, l*)`, row propagation, the fibre identity, corner triangles

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Triangles.lean`, middle part
(the corner map, row propagation, `white_row_above`, characterization of corners, the fibre identity, membership in `triangle`, invariance of corners);
generalized to the GGM family (p, q, r). Modified. Triangles are `F.triangle` (`log q² : log p`).
Namespace `GGMCollatz.Family.Tri`.
-/

namespace GGMCollatz

namespace Family

namespace Tri

variable (F : Family)

/-! ### The corner map (pp.38–39 of tao-collatz) -/

open Classical in
/-- The distance in column `j` from `l` up to the first white point (formally `0` if there is none). -/
noncomputable def upRun (n : ℕ) (c : ℤ) (ε : ℝ) (j : ℕ) (l : ℤ) : ℕ :=
  if h : ∃ t : ℕ, ¬ F.black n c ε j (l + t) then Nat.find h else 0

/-- `l*(j,l)`: the top of the black column above `(j,l)`. -/
noncomputable def lstar (n : ℕ) (c : ℤ) (ε : ℝ) (j : ℕ) (l : ℤ) : ℤ :=
  l + upRun F n c ε j l - 1

open Classical in
/-- The length of the leftward black row at height `l*`. -/
noncomputable def leftRun (n : ℕ) (c : ℤ) (ε : ℝ) (j : ℕ) (l : ℤ) : ℕ :=
  Nat.find (⟨j + 1, Or.inl (by omega)⟩ :
    ∃ a : ℕ, j < a ∨ ¬ F.black n c ε (j - a) (lstar F n c ε j l))

/-- `j*(j,l)`: the left end of the black row at height `l*`. -/
noncomputable def jstar (n : ℕ) (c : ℤ) (ε : ℝ) (j : ℕ) (l : ℤ) : ℕ :=
  j - (leftRun F n c ε j l - 1)

section CornerSpec

variable {F} {n : ℕ} {c : ℤ} {ε : ℝ} {j : ℕ} {l : ℤ}

theorem black_of_le_lstar (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n)
    {l' : ℤ} (h1 : l ≤ l') (h2 : l' ≤ lstar F n c ε j l) : F.black n c ε j l' := by
  classical
  have hex := exists_white_above H j l h2j
  unfold lstar at h2
  rw [upRun, dif_pos hex] at h2
  have hi : (l' - l).toNat < Nat.find hex := by omega
  have hmin := Nat.find_min hex hi
  rw [not_not] at hmin
  have hcast : l + ((l' - l).toNat : ℤ) = l' := by omega
  rw [hcast] at hmin
  exact hmin

theorem le_lstar (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n)
    (hb : F.black n c ε j l) : l ≤ lstar F n c ε j l := by
  classical
  have hex := exists_white_above H j l h2j
  unfold lstar
  rw [upRun, dif_pos hex]
  have h0 : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso
      have hs := Nat.find_spec hex
      rw [h] at hs
      simp only [Nat.cast_zero, add_zero] at hs
      exact hs hb
    · exact h
  omega

theorem white_above_lstar (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n) :
    ¬ F.black n c ε j (lstar F n c ε j l + 1) := by
  classical
  have hex := exists_white_above H j l h2j
  unfold lstar
  rw [upRun, dif_pos hex]
  have hs := Nat.find_spec hex
  have hcast : l + (Nat.find hex : ℤ) - 1 + 1 = l + Nat.find hex := by ring
  rw [hcast]
  exact hs

theorem leftRun_pos (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n)
    (hb : F.black n c ε j l) : 0 < leftRun F n c ε j l := by
  classical
  have hbl : F.black n c ε j (lstar F n c ε j l) :=
    black_of_le_lstar H h2j (le_lstar H h2j hb) le_rfl
  rw [leftRun, Nat.find_pos]
  intro h
  rcases h with h | h
  · omega
  · simp only [Nat.sub_zero] at h
    exact h hbl

theorem black_of_jstar_le (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n)
    (hb : F.black n c ε j l) {j' : ℕ} (h1 : jstar F n c ε j l ≤ j') (h2 : j' ≤ j) :
    F.black n c ε j' (lstar F n c ε j l) := by
  classical
  have hpos := leftRun_pos H h2j hb
  unfold jstar at h1
  have ha : j - j' < leftRun F n c ε j l := by omega
  rw [leftRun] at ha
  have hmin := Nat.find_min
    (⟨j + 1, Or.inl (by omega)⟩ :
      ∃ a : ℕ, j < a ∨ ¬ F.black n c ε (j - a) (lstar F n c ε j l)) ha
  push Not at hmin
  have hj' : j - (j - j') = j' := by omega
  rw [hj'] at hmin
  exact hmin.2

theorem jstar_maximal (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n)
    (hb : F.black n c ε j l) :
    jstar F n c ε j l = 0 ∨ ¬ F.black n c ε (jstar F n c ε j l - 1) (lstar F n c ε j l) := by
  classical
  have hpos := leftRun_pos H h2j hb
  have hspec : j < leftRun F n c ε j l ∨
      ¬ F.black n c ε (j - leftRun F n c ε j l) (lstar F n c ε j l) := by
    rw [leftRun]
    exact Nat.find_spec
      (⟨j + 1, Or.inl (by omega)⟩ :
        ∃ a : ℕ, j < a ∨ ¬ F.black n c ε (j - a) (lstar F n c ε j l))
  rcases hspec with h | h
  · left; unfold jstar; omega
  · rcases Nat.lt_or_ge j (leftRun F n c ε j l) with haj | haj
    · left; unfold jstar; omega
    · right
      rw [show jstar F n c ε j l - 1 = j - leftRun F n c ε j l from by unfold jstar; omega]
      exact h

theorem jstar_le (j : ℕ) (l : ℤ) : jstar F n c ε j l ≤ j := by
  unfold jstar; omega

end CornerSpec

/-! ### Row propagation of weakly black points (the engine of Cases 2 and 3 of Claim (*)) -/

section Rows

variable {F} {n : ℕ} {c : ℤ} {ε : ℝ}

theorem wb_row_left (hεw : ε ≤ wth F) {L : ℤ} {jlo jhi : ℕ}
    (hb : ∀ j'', jlo ≤ j'' → j'' ≤ jhi → F.black n c ε j'' L)
    (hwb : wb F n c jhi (L + 1)) :
    ∀ j'', jlo ≤ j'' → j'' ≤ jhi → wb F n c j'' (L + 1) := by
  have key : ∀ i : ℕ, i ≤ jhi - jlo → wb F n c (jhi - i) (L + 1) := by
    intro i
    induction i with
    | zero => intro _; simpa using hwb
    | succ i IH =>
      intro hi
      have hIH := IH (by omega)
      have hstep : jhi - i = (jhi - (i + 1)) + 1 := by omega
      have h1 : wb F n c ((jhi - (i + 1)) + 1) (L + 1) := by
        rw [← hstep]; exact hIH
      have h2 : wb F n c (jhi - (i + 1)) ((L + 1) - 1) := by
        rw [show L + 1 - 1 = L from by ring]
        exact wb_of_black hεw (hb _ (by omega) (by omega))
      exact wb_of_succ_j_pred_l h1 h2
  intro j'' h1 h2
  have := key (jhi - j'') (by omega)
  rwa [show jhi - (jhi - j'') = j'' from by omega] at this

theorem wb_row_right (hεw : ε ≤ wth F) {L : ℤ} {jlo jhi : ℕ}
    (hb : ∀ j'', jlo ≤ j'' → j'' ≤ jhi → F.black n c ε j'' L)
    (hwb : wb F n c jlo (L + 1)) :
    ∀ j'', jlo ≤ j'' → j'' ≤ jhi → wb F n c j'' (L + 1) := by
  have key : ∀ i : ℕ, jlo + i ≤ jhi → wb F n c (jlo + i) (L + 1) := by
    intro i
    induction i with
    | zero => intro _; simpa using hwb
    | succ i IH =>
      intro hi
      have hIH := IH (by omega)
      have h2 : wb F n c ((jlo + i) + 1) ((L + 1) - 1) := by
        rw [show L + 1 - 1 = L from by ring]
        exact wb_of_black hεw (hb _ (by omega) (by omega))
      have h3 := wb_of_pred_j_pred_l hIH h2
      rwa [show jlo + (i + 1) = (jlo + i) + 1 from by omega]
  intro j'' h1 h2
  have := key (j'' - jlo) (by omega)
  rwa [show jlo + (j'' - jlo) = j'' from by omega] at this

/-- **Whiteness of the row above**: if a point `(jc, L+1)` above a black row `[jlo, jhi]` (at height `L`) is white, the whole row above is white. -/
theorem white_row_above (hεw : ε ≤ wth F) {L : ℤ} {jlo jhi jc : ℕ}
    (hb : ∀ j'', jlo ≤ j'' → j'' ≤ jhi → F.black n c ε j'' L)
    (hc1 : jlo ≤ jc) (hc2 : jc ≤ jhi) (hw : ¬ F.black n c ε jc (L + 1)) :
    ∀ j', jlo ≤ j' → j' ≤ jhi → ¬ F.black n c ε j' (L + 1) := by
  intro j' h1 h2 hb'
  have hwb' : wb F n c j' (L + 1) := wb_of_black hεw hb'
  have hwbc : wb F n c jc (L + 1) := by
    rcases le_or_gt jc j' with h | h
    · exact wb_row_left hεw (jlo := jc) (jhi := j')
        (fun j'' ha hb'' => hb j'' (by omega) (by omega)) hwb' jc le_rfl h
    · exact wb_row_right hεw (jlo := j') (jhi := jc)
        (fun j'' ha hb'' => hb j'' (by omega) (by omega)) hwb' jc (by omega) le_rfl
  have hblk : F.black n c ε jc ((L + 1) - 1) := by
    rw [show L + 1 - 1 = L from by ring]; exact hb jc hc1 hc2
  exact hw (black_of_wb_pred_l hwbc hblk)

/-- Propagating a weakly black row to the left (the form of Case 2). -/
theorem wb_row_left_of_weak_base {L : ℤ} {jlo jhi : ℕ}
    (hle : jlo ≤ jhi)
    (hbase : ∀ j'', jlo ≤ j'' → j'' < jhi → wb F n c j'' L)
    (htop : wb F n c jhi (L + 1)) :
    wb F n c jlo (L + 1) := by
  have key : ∀ i : ℕ, i ≤ jhi - jlo → wb F n c (jhi - i) (L + 1) := by
    intro i hi
    induction i with
    | zero => simpa using htop
    | succ i ih =>
      have hi' : i ≤ jhi - jlo := by omega
      have hprev := ih hi'
      have hidx : jhi - i = (jhi - (i + 1)) + 1 := by omega
      apply wb_of_succ_j_pred_l
      · rwa [← hidx]
      · rw [show L + 1 - 1 = L from by ring]
        exact hbase _ (by omega) (by omega)
  have := key (jhi - jlo) (by omega)
  rwa [show jhi - (jhi - jlo) = jlo from by omega] at this

/-- Propagating a weakly black column upward (the form of Case 3). -/
theorem wb_col_up_of_weak_right {J : ℕ} {z : ℤ} (t : ℕ)
    (hJ : 1 ≤ J) (hleft : wb F n c (J - 1) z)
    (hright : ∀ i : ℕ, i < t → wb F n c J (z + (i + 1))) :
    wb F n c (J - 1) (z + t) := by
  induction t with
  | zero => simpa using hleft
  | succ t ih =>
    have hprev := ih (fun i hi => hright i (by omega))
    have hstep := wb_of_succ_j_pred_l
      (F := F) (n := n) (c := c) (j := J - 1) (l := z + (t + 1))
      (by
        rw [show (J - 1) + 1 = J from by omega]
        exact hright t (by omega))
      (by
        convert hprev using 1; ring)
    simpa using hstep

end Rows

/-! ### Characterization of corners -/

section CornerChar

variable {F} {n : ℕ} {c : ℤ} {ε : ℝ}

theorem lstar_eq_of {j : ℕ} {l L : ℤ} (hl : l ≤ L)
    (hb : ∀ l'' : ℤ, l ≤ l'' → l'' ≤ L → F.black n c ε j l'')
    (hw : ¬ F.black n c ε j (L + 1)) : lstar F n c ε j l = L := by
  classical
  have hex : ∃ t : ℕ, ¬ F.black n c ε j (l + t) :=
    ⟨(L + 1 - l).toNat, by
      rw [show l + ((L + 1 - l).toNat : ℤ) = L + 1 from by omega]; exact hw⟩
  unfold lstar upRun
  rw [dif_pos hex]
  have hle : Nat.find hex ≤ (L + 1 - l).toNat := Nat.find_le (by
    rw [show l + ((L + 1 - l).toNat : ℤ) = L + 1 from by omega]; exact hw)
  have hge : (L + 1 - l).toNat ≤ Nat.find hex := by
    by_contra hcon
    push Not at hcon
    have hspec := Nat.find_spec hex
    exact hspec (hb _ (by omega) (by omega))
  omega

theorem jstar_eq_of {j J : ℕ} {l : ℤ} (hJ : J ≤ j)
    (hb : ∀ j'' : ℕ, J ≤ j'' → j'' ≤ j → F.black n c ε j'' (lstar F n c ε j l))
    (hw : J = 0 ∨ ¬ F.black n c ε (J - 1) (lstar F n c ε j l)) :
    jstar F n c ε j l = J := by
  classical
  have hexJ : ∃ a : ℕ, j < a ∨ ¬ F.black n c ε (j - a) (lstar F n c ε j l) :=
    ⟨j + 1, Or.inl (by omega)⟩
  have hfind : Nat.find hexJ = j - J + 1 := by
    apply le_antisymm
    · apply Nat.find_le
      rcases hw with h0 | hwhite
      · left; omega
      · right; rwa [show j - (j - J + 1) = J - 1 from by omega]
    · by_contra hcon
      push Not at hcon
      have hspec := Nat.find_spec hexJ
      rcases hspec with h | h
      · omega
      · exact h (hb _ (by omega) (by omega))
  have hlr : leftRun F n c ε j l = Nat.find hexJ := rfl
  unfold jstar
  rw [hlr, hfind]
  omega

end CornerChar

/-! ### The fibre identity `θ(j,l) = (q²)^{j-j*} p^{l*-l} θ*` -/

section Fibre

variable {F} {n : ℕ} {c : ℤ} {ε : ℝ}

/-- Along a black row, `θ(j+t, L) = (q²)^t θ(j, L)`. -/
theorem th_left_run (H : Hyp F n c ε) (j : ℕ) (L : ℤ) (t : ℕ)
    (hb : ∀ i : ℕ, i < t → F.black n c ε (j + i) L) :
    th F n c (j + t) L = ((F.q : ℝ) ^ 2) ^ t * th F n c j L := by
  induction t with
  | zero => simp
  | succ t IH =>
    have hbt : |th F n c (j + t) L| ≤ ε := hb t (by omega)
    have hsmall : (F.q : ℝ) ^ 2 * |th F n c (j + t) L| < 1 / 2 := by
      have := H.q2_eps
      have hq : (0 : ℝ) ≤ (F.q : ℝ) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hbt hq
      linarith
    have hstep := th_succ_j_exact F n c (j + t) L hsmall
    rw [show j + (t + 1) = (j + t) + 1 from by omega, hstep,
      IH (fun i h => hb i (by omega)), pow_succ]
    ring

variable {j : ℕ} {l : ℤ}

/-- **The fibre identity**. -/
theorem th_fibre_eq (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n)
    (hb : F.black n c ε j l) :
    th F n c j l = ((F.q : ℝ) ^ 2) ^ (j - jstar F n c ε j l)
      * (F.p : ℝ) ^ (lstar F n c ε j l - l).toNat
      * th F n c (jstar F n c ε j l) (lstar F n c ε j l) := by
  set j' := jstar F n c ε j l with hj'
  set L := lstar F n c ε j l with hL
  have hll : l ≤ L := le_lstar H h2j hb
  have hjj : j' ≤ j := jstar_le j l
  set b := (L - l).toNat with hbdef
  set a := j - j' with hadef
  have hup : th F n c j l = (F.p : ℝ) ^ b * th F n c j L := by
    have hcast : l + (b : ℤ) = L := by omega
    have := th_up_run H j l b (fun i h1 h2 => by
      apply black_of_le_lstar H h2j (Int.le.intro i rfl)
      rw [← hL]; omega)
    rwa [hcast] at this
  have hleft : th F n c j L = ((F.q : ℝ) ^ 2) ^ a * th F n c j' L := by
    have hja : j' + a = j := by omega
    have := th_left_run H j' L a (fun i h => by
      apply black_of_jstar_le H h2j hb (by rw [← hj']; omega) (by omega))
    rwa [hja] at this
  rw [hup, hleft]; ring

/-- `(q²)^{j-j*} p^{l*-l} |θ*| ≤ ε`. -/
theorem fibre_le_eps (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n)
    (hb : F.black n c ε j l) :
    ((F.q : ℝ) ^ 2) ^ (j - jstar F n c ε j l) * (F.p : ℝ) ^ (lstar F n c ε j l - l).toNat
      * |th F n c (jstar F n c ε j l) (lstar F n c ε j l)| ≤ ε := by
  have heq := th_fibre_eq H h2j hb
  have hble : |th F n c j l| ≤ ε := hb
  calc ((F.q : ℝ) ^ 2) ^ (j - jstar F n c ε j l) * (F.p : ℝ) ^ (lstar F n c ε j l - l).toNat
        * |th F n c (jstar F n c ε j l) (lstar F n c ε j l)|
      = |th F n c j l| := by
        rw [heq, abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((F.q : ℝ) ^ 2) ^ (j - jstar F n c ε j l)),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (F.p : ℝ) ^ (lstar F n c ε j l - l).toNat)]
    _ ≤ ε := hble

/-- The corner phase is not `0` (lower bound at the edge in the corner column). -/
theorem corner_phase_pos (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n) :
    0 < |th F n c (jstar F n c ε j l) (lstar F n c ε j l)| := by
  have hjj : jstar F n c ε j l ≤ j := jstar_le j l
  have h2j' : 2 * jstar F n c ε j l + 2 * F.edgeB + 2 ≤ n := by omega
  have := F.q_pos
  calc (0 : ℝ) < 1 / (F.q : ℝ) ^ (n - 2 * jstar F n c ε j l) := by positivity
    _ ≤ |th F n c (jstar F n c ε j l) (lstar F n c ε j l)| :=
        th_lower_bound F H.hc _ h2j'

end Fibre

/-! ### Corner triangles -/

/-- The size of the corner triangle `s* = log(ε/|θ*|)`. -/
noncomputable def cornerSize (n : ℕ) (c : ℤ) (ε : ℝ) (j : ℕ) (l : ℤ) : ℝ :=
  Real.log (ε / |th F n c (jstar F n c ε j l) (lstar F n c ε j l)|)

section CornerTri

variable {F} {n : ℕ} {c : ℤ} {ε : ℝ}

theorem log_pow_mul (a b : ℕ) :
    Real.log (((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b)
      = (a : ℝ) * Real.log ((F.q : ℝ) ^ 2) + (b : ℝ) * Real.log F.p := by
  have hq : (0 : ℝ) < (F.q : ℝ) ^ 2 := by have := one_le_q_sq F; linarith
  have hp : (0 : ℝ) < F.p := by have := one_le_p F; linarith
  rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]

/-- `(q²)^a p^b |θ*| ≤ ε` is equivalent to membership in the triangle (`ε > 0`, `θ* ≠ 0`). -/
theorem mem_triangle_iff_scale {J r : ℕ} {L z : ℤ} {θs : ℝ} (hε : 0 < ε) (hθ : 0 < |θs|)
    (hJ : J ≤ r) (hz : z ≤ L) :
    (r, z) ∈ F.triangle J L (Real.log (ε / |θs|))
      ↔ ((F.q : ℝ) ^ 2) ^ (r - J) * (F.p : ℝ) ^ (L - z).toNat * |θs| ≤ ε := by
  set a := r - J with ha
  set b := (L - z).toNat with hb
  have haR : (r : ℝ) - (J : ℝ) = (a : ℝ) := by rw [ha, Nat.cast_sub hJ]
  have hbR : (L : ℝ) - (z : ℝ) = (b : ℝ) := by
    have hto : ((L - z).toNat : ℤ) = L - z := by omega
    have := congrArg (fun x : ℤ => (x : ℝ)) hto
    push_cast at this
    simpa [hb] using this.symm
  have hpos : (0 : ℝ) < ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b := by
    have hq : (0 : ℝ) < (F.q : ℝ) ^ 2 := by have := one_le_q_sq F; linarith
    have hp : (0 : ℝ) < F.p := by have := one_le_p F; linarith
    positivity
  have hdivpos : (0 : ℝ) < ε / |θs| := div_pos hε hθ
  constructor
  · rintro ⟨_, _, hlog⟩
    simp only at hlog
    rw [haR, hbR, ← log_pow_mul] at hlog
    have := (Real.log_le_log_iff hpos hdivpos).mp hlog
    rwa [le_div_iff₀ hθ] at this
  · intro h
    refine ⟨hJ, hz, ?_⟩
    simp only
    rw [haR, hbR, ← log_pow_mul]
    exact Real.log_le_log hpos ((le_div_iff₀ hθ).mpr h)

variable {j : ℕ} {l : ℤ}

/-- **Membership in the corner triangle**: points of the black strip lie in the corner triangle. -/
theorem black_mem_corner_triangle (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n)
    (hb : F.black n c ε j l) :
    (j, l) ∈ F.triangle (jstar F n c ε j l) (lstar F n c ε j l) (cornerSize F n c ε j l) := by
  unfold cornerSize
  rw [mem_triangle_iff_scale H.pos (corner_phase_pos H h2j) (jstar_le j l) (le_lstar H h2j hb)]
  exact fibre_le_eps H h2j hb

/-- **Corner triangles are black**. -/
theorem black_of_mem_corner_triangle (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n)
    {x : ℕ × ℤ}
    (hx : x ∈ F.triangle (jstar F n c ε j l) (lstar F n c ε j l) (cornerSize F n c ε j l)) :
    F.black n c ε x.1 x.2 := by
  have hj1 : jstar F n c ε j l ≤ x.1 := hx.1
  have hl1 : x.2 ≤ lstar F n c ε j l := hx.2.1
  unfold cornerSize at hx
  have hx' : (x.1, x.2) ∈ F.triangle (jstar F n c ε j l) (lstar F n c ε j l)
      (Real.log (ε / |th F n c (jstar F n c ε j l) (lstar F n c ε j l)|)) := hx
  rw [mem_triangle_iff_scale H.pos (corner_phase_pos H h2j) hj1 hl1] at hx'
  have hp1 : x.1 = jstar F n c ε j l + (x.1 - jstar F n c ε j l) := by omega
  have hp2 : x.2 = lstar F n c ε j l - ((lstar F n c ε j l - x.2).toNat : ℕ) := by omega
  show |th F n c x.1 x.2| ≤ ε
  rw [hp1, hp2]
  calc |th F n c (jstar F n c ε j l + (x.1 - jstar F n c ε j l))
        (lstar F n c ε j l - ((lstar F n c ε j l - x.2).toNat : ℕ))|
      ≤ ((F.q : ℝ) ^ 2) ^ (x.1 - jstar F n c ε j l)
          * (F.p : ℝ) ^ (lstar F n c ε j l - x.2).toNat
          * |th F n c (jstar F n c ε j l) (lstar F n c ε j l)| :=
        th_iterate_abs_le F n c _ _ _ _
    _ ≤ ε := hx'

/-- **Invariance of corners** (`corner_eq` of tao-collatz, via Claim (*)): points of the corner triangle have the same corner as the original point. -/
theorem corner_eq (H : Hyp F n c ε) (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n)
    (hb : F.black n c ε j l) {x : ℕ × ℤ}
    (hx : x ∈ F.triangle (jstar F n c ε j l) (lstar F n c ε j l) (cornerSize F n c ε j l)) :
    lstar F n c ε x.1 x.2 = lstar F n c ε j l ∧ jstar F n c ε x.1 x.2 = jstar F n c ε j l := by
  obtain ⟨hj1, hl1, hsize⟩ := hx
  have hlogq : (0 : ℝ) ≤ Real.log ((F.q : ℝ) ^ 2) := Real.log_nonneg (one_le_q_sq F)
  have hlogp : (0 : ℝ) ≤ Real.log F.p := Real.log_nonneg (one_le_p F)
  have hJj : jstar F n c ε j l ≤ j := jstar_le j l
  have hcol : ∀ l'' : ℤ, x.2 ≤ l'' → l'' ≤ lstar F n c ε j l → F.black n c ε x.1 l'' := by
    intro l'' h1 h2
    refine black_of_mem_corner_triangle H h2j (x := (x.1, l'')) ⟨hj1, h2, ?_⟩
    show ((x.1 : ℝ) - (jstar F n c ε j l : ℝ)) * Real.log ((F.q : ℝ) ^ 2)
        + ((lstar F n c ε j l : ℝ) - (l'' : ℝ)) * Real.log F.p ≤ cornerSize F n c ε j l
    have hmul : (0 : ℝ) ≤ ((l'' : ℝ) - (x.2 : ℝ)) * Real.log F.p :=
      mul_nonneg (sub_nonneg.mpr (by exact_mod_cast h1)) hlogp
    linarith [hsize]
  have hrow : ∀ j'' : ℕ, jstar F n c ε j l ≤ j'' → j'' ≤ max j x.1 →
      F.black n c ε j'' (lstar F n c ε j l) := by
    intro j'' h1 h2
    rcases le_or_gt j'' j with hle | hgt
    · exact black_of_jstar_le H h2j hb h1 hle
    · have hle' : j'' ≤ x.1 := by omega
      refine black_of_mem_corner_triangle H h2j (x := (j'', lstar F n c ε j l))
        ⟨h1, le_rfl, ?_⟩
      show ((j'' : ℝ) - (jstar F n c ε j l : ℝ)) * Real.log ((F.q : ℝ) ^ 2)
          + ((lstar F n c ε j l : ℝ) - (lstar F n c ε j l : ℝ)) * Real.log F.p
          ≤ cornerSize F n c ε j l
      have hmul9 : (0 : ℝ) ≤ ((x.1 : ℝ) - (j'' : ℝ)) * Real.log ((F.q : ℝ) ^ 2) :=
        mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hle')) hlogq
      have hmul2 : (0 : ℝ) ≤ ((lstar F n c ε j l : ℝ) - (x.2 : ℝ)) * Real.log F.p :=
        mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hl1)) hlogp
      linarith [hsize]
  have hwabove : ∀ j' : ℕ, jstar F n c ε j l ≤ j' → j' ≤ max j x.1 →
      ¬ F.black n c ε j' (lstar F n c ε j l + 1) :=
    white_row_above H.le_w hrow hJj (le_max_left _ _) (white_above_lstar H h2j)
  have hls : lstar F n c ε x.1 x.2 = lstar F n c ε j l :=
    lstar_eq_of hl1 hcol (hwabove x.1 hj1 (le_max_right _ _))
  refine ⟨hls, ?_⟩
  apply jstar_eq_of hj1
  · intro j'' h1 h2
    rw [hls]
    exact hrow j'' h1 (le_trans h2 (le_max_right _ _))
  · rw [hls]
    exact jstar_maximal H h2j hb

end CornerTri

end Tri

end Family

end GGMCollatz
