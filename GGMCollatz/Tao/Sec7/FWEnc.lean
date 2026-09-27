import GGMCollatz.Tao.Sec7.FpPlus

/-!
# GGM §7: the encounter convolution with triangles (the D6-form definitions of Lemma 7.9 of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/ManyTriangles.lean`
(`EncState`, `encStep`, `encInit`, `encVal`, `encExpect` and their basic properties) and
`TaoCollatz/Sec7/Case3.lean` (`encFold_*`, `pathSum_head`, `pathSum_fst_le`);
generalized to the GGM family (p, q, r). Modified.

Instead of `TriangleFamily n ξ` of tao-collatz we use a triangle family `T : F.TriFam half σ`.
The encounter condition: the phase point `(q₁ - 1, q₂)` lies in `T.blk` (the union of the triangles), the depth satisfies `q₁ + g ≤ half`,
and the height exceeds `barrier`, the top of the previous triangle. The barrier is the top of the triangle containing that point (`covTri`, chosen).
White points are `whiteStrip half T.W` (for `q₁ ≥ 1`, equivalent to the phase point not lying in `T.blk`).

* `EncState`, `encStep`, `encInit`, `encVal`, `encExpect`.
* Basic properties: `encExpect_succ` (peeling off the head), `encExpect_le`, `encFold_pos`, `encFold_count_le`,
  `encFold_banked_le`, `encFold_cumWhite`, `pathSum_head`, `pathSum_fst_le`, `pathSum_depth_le`.
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace FW

/-- The state of the encounter convolution (`EncState` of tao-collatz). -/
structure EncState : Type where
  /-- current position (renewal coordinates) -/
  pos : ℕ × ℤ
  /-- barrier: the top of the most recently encountered triangle -/
  barrier : ℤ
  /-- number of encounters `r` -/
  count : ℕ
  /-- number of white points passed -/
  cumWhite : ℕ
  /-- number of white points frozen at the `min(count, R)`-th encounter -/
  banked : ℕ

/-- The initial state: no encounters, barrier `l'`. -/
def encInit (j' : ℕ) (l' : ℤ) : EncState := ⟨(j', l'), l', 0, 0, 0⟩

/-- The integrand `exp(-banked + κ min(r, R))` of (7.57). -/
noncomputable def encVal (κ : ℝ) (R : ℕ) (st : EncState) : ℝ :=
  Real.exp (-(st.banked : ℝ) + κ * min st.count R)

theorem encVal_pos (κ : ℝ) (R : ℕ) (st : EncState) : 0 < encVal κ R st := Real.exp_pos _

theorem encVal_le (κ : ℝ) (hκ : 0 ≤ κ) (R : ℕ) (st : EncState) :
    encVal κ R st ≤ Real.exp (κ * R) := by
  apply Real.exp_le_exp.mpr
  have h1 : (0 : ℝ) ≤ (st.banked : ℝ) := Nat.cast_nonneg _
  have h2 : ((min st.count R : ℕ) : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr (min_le_right _ _)
  linarith [mul_le_mul_of_nonneg_left h2 hκ, h1]

variable (F : Family)

open Classical in
/-- The family triangle containing the point `x` (chosen; formally `(0,0,0)` if there is none). -/
noncomputable def covTri {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (x : ℕ × ℤ) : ℕ × ℤ × ℝ :=
  if h : ∃ t ∈ T.T, x ∈ F.triangle t.1 t.2.1 t.2.2 then Classical.choose h else (0, 0, 0)

theorem covTri_spec {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) {x : ℕ × ℤ} (hx : x ∈ T.blk) :
    covTri F T x ∈ T.T ∧ x ∈ F.triangle (covTri F T x).1 (covTri F T x).2.1 (covTri F T x).2.2 := by
  have h : ∃ t ∈ T.T, x ∈ F.triangle t.1 t.2.1 t.2.2 := by
    simpa [TriFam.blk] using hx
  unfold covTri
  rw [dif_pos h]
  exact Classical.choose_spec h

open Classical in
/-- **One step of the encounter convolution** (`encStep` of tao-collatz, with depth gate `g`). -/
noncomputable def encStep {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (st : EncState) (d : ℕ × ℤ) : EncState :=
  if 1 ≤ (st.pos + d).1 ∧ (st.pos + d).1 + g ≤ half
      ∧ ((st.pos + d).1 - 1, (st.pos + d).2) ∈ T.blk ∧ st.barrier < (st.pos + d).2 then
    { pos := st.pos + d
      barrier := (covTri F T ((st.pos + d).1 - 1, (st.pos + d).2)).2.1
      count := st.count + 1
      cumWhite := st.cumWhite + (if st.pos + d ∈ whiteStrip half T.W then 1 else 0)
      banked := if st.count < R then
          st.cumWhite + (if st.pos + d ∈ whiteStrip half T.W then 1 else 0)
        else st.banked }
  else
    { pos := st.pos + d, barrier := st.barrier, count := st.count,
      cumWhite := st.cumWhite + (if st.pos + d ∈ whiteStrip half T.W then 1 else 0),
      banked := st.banked }

/-- The left-hand side of (7.57) (horizon `Tw`, from state `st`). -/
noncomputable def encExpect {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) (κ : ℝ)
    (Tw : ℕ) (st : EncState) : ℝ :=
  (F.hold.iid Tw).expect fun v => encVal κ R ((List.ofFn v).foldl (encStep F T R g) st)

variable {F}

theorem encStep_pos {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (st : EncState) (d : ℕ × ℤ) : (encStep F T R g st d).pos = st.pos + d := by
  unfold encStep
  split <;> rfl

theorem encFold_pos {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) :
    ∀ (L : List (ℕ × ℤ)) (st : EncState),
      (L.foldl (encStep F T R g) st).pos = st.pos + L.sum := by
  intro L
  induction L with
  | nil => intro st; simp
  | cons d L IH =>
    intro st
    rw [List.foldl_cons, IH, encStep_pos, List.sum_cons, add_assoc]

theorem encStep_count_le {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (st : EncState) (d : ℕ × ℤ) : st.count ≤ (encStep F T R g st d).count := by
  unfold encStep
  split <;> dsimp only <;> omega

theorem encFold_count_le {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) :
    ∀ (L : List (ℕ × ℤ)) (st : EncState),
      st.count ≤ (L.foldl (encStep F T R g) st).count := by
  intro L
  induction L with
  | nil => intro st; simp
  | cons d L IH =>
    intro st
    exact le_trans (encStep_count_le T R g st d) (IH _)

theorem encStep_banked_le {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (st : EncState) (d : ℕ × ℤ) (h : st.banked ≤ st.cumWhite) :
    (encStep F T R g st d).banked ≤ (encStep F T R g st d).cumWhite := by
  unfold encStep
  split <;> dsimp only <;> split_ifs <;> omega

theorem encFold_banked_le {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) :
    ∀ (L : List (ℕ × ℤ)) (st : EncState), st.banked ≤ st.cumWhite →
      (L.foldl (encStep F T R g) st).banked ≤ (L.foldl (encStep F T R g) st).cumWhite := by
  intro L
  induction L with
  | nil => intro st h; simpa using h
  | cons d L IH =>
    intro st h
    exact IH _ (encStep_banked_le T R g st d h)

open Classical in
theorem encStep_cumWhite {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (st : EncState) (d : ℕ × ℤ) :
    (encStep F T R g st d).cumWhite
      = st.cumWhite + (if st.pos + d ∈ whiteStrip half T.W then 1 else 0) := by
  unfold encStep
  split <;> rfl

/-- Peeling off the head (a form not using `Fin.cons`). -/
theorem pathSum_head {Tw : ℕ} (v : Fin (Tw + 1) → ℕ × ℤ) (p : ℕ) :
    pathSum v (p + 1) = v 0 + pathSum (fun i : Fin Tw => v i.succ) p := by
  rw [pathSum, pathSum, List.ofFn_succ]
  simp

/-- The first coordinate of `pathSum` is monotone. -/
theorem pathSum_fst_le {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) {p q : ℕ} (hpq : p ≤ q) :
    (pathSum v p).1 ≤ (pathSum v q).1 := by
  have hsplit : (List.ofFn v).take q
      = (List.ofFn v).take p ++ ((List.ofFn v).take q).drop p := by
    conv_lhs => rw [← List.take_append_drop p ((List.ofFn v).take q)]
    rw [List.take_take, Nat.min_eq_left hpq]
  have hq : pathSum v q = pathSum v p + (((List.ofFn v).take q).drop p).sum := by
    conv_lhs => rw [pathSum, hsplit, List.sum_append]
    rw [pathSum]
  rw [hq, Prod.fst_add]
  exact Nat.le_add_right _ _

/-- If the endpoint is deep, all intermediate points are deep. -/
theorem pathSum_depth_le {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) (q₀ : ℕ × ℤ) (g half : ℕ)
    (hend : q₀.1 + (pathSum v Tw).1 + g ≤ half) :
    ∀ p, p ≤ Tw → (q₀ + pathSum v p).1 + g ≤ half := by
  intro p hp
  have hmono : (pathSum v p).1 ≤ (pathSum v Tw).1 := pathSum_fst_le v hp
  have hfst : (q₀ + pathSum v p).1 = q₀.1 + (pathSum v p).1 := rfl
  omega

open Classical in
/-- The number of white points of the convolution is the number of white positions after each step of the walk (`encFold_cumWhite` of tao-collatz). -/
theorem encFold_cumWhite {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) :
    ∀ (Tw : ℕ) (v : Fin Tw → ℕ × ℤ) (st : EncState),
      ((List.ofFn v).foldl (encStep F T R g) st).cumWhite
        = st.cumWhite + (Finset.range Tw).sum
            (fun p => if st.pos + pathSum v (p + 1) ∈ whiteStrip half T.W then 1 else 0) := by
  intro Tw
  induction Tw with
  | zero => intro v st; simp
  | succ Tw IH =>
    intro v st
    rw [List.ofFn_succ, List.foldl_cons,
      IH (fun i : Fin Tw => v i.succ) (encStep F T R g st (v 0)),
      encStep_cumWhite, encStep_pos, Finset.sum_range_succ']
    have h0 : pathSum v 1 = v 0 := by
      simpa using pathSum_head v 0
    have hstep : ∀ p : ℕ,
        pathSum v (p + 1 + 1) = v 0 + pathSum (fun i : Fin Tw => v i.succ) (p + 1) :=
      fun p => pathSum_head v (p + 1)
    rw [h0]
    have hsum : ∀ p ∈ Finset.range Tw,
        (if st.pos + v 0 + pathSum (fun i : Fin Tw => v i.succ) (p + 1) ∈ whiteStrip half T.W
          then (1 : ℕ) else 0)
        = (if st.pos + pathSum v (p + 1 + 1) ∈ whiteStrip half T.W then 1 else 0) := by
      intro p _
      rw [hstep p, add_assoc]
    rw [Finset.sum_congr rfl hsum]
    omega

variable (F)

/-- Horizon `0`: the expectation is the integrand itself. -/
theorem encExpect_zero {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) (κ : ℝ)
    (st : EncState) : encExpect F T R g κ 0 st = encVal κ R st := by
  rw [encExpect, PMF.expect_iid_zero]
  simp

/-- **Peeling off the head** (`encExpect_succ` of tao-collatz). -/
theorem encExpect_succ {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (Tw : ℕ) (st : EncState) :
    encExpect F T R g κ (Tw + 1) st
      = ∑' d : ℕ × ℤ, (F.hold d).toReal * encExpect F T R g κ Tw (encStep F T R g st d) := by
  set c : ℝ := Real.exp (κ * R) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hkey : ∀ (m : ℕ) (τ : EncState),
      encExpect F T R g κ m τ * c⁻¹
        = (F.hold.iid m).expect fun v =>
            encVal κ R ((List.ofFn v).foldl (encStep F T R g) τ) * c⁻¹ := by
    intro m τ
    rw [encExpect, PMF.expect, PMF.expect, ← tsum_mul_right]
    exact tsum_congr fun v => by ring
  have h0 : ∀ (m : ℕ) (τ : EncState) (v : Fin m → ℕ × ℤ),
      0 ≤ encVal κ R ((List.ofFn v).foldl (encStep F T R g) τ) * c⁻¹ :=
    fun m τ v => mul_nonneg (encVal_pos κ R _).le (by positivity)
  have h1 : ∀ (m : ℕ) (τ : EncState) (v : Fin m → ℕ × ℤ),
      encVal κ R ((List.ofFn v).foldl (encStep F T R g) τ) * c⁻¹ ≤ 1 := by
    intro m τ v
    rw [← mul_inv_cancel₀ hc0.ne']
    exact mul_le_mul_of_nonneg_right (encVal_le κ hκ R _) (by positivity)
  have hmain : encExpect F T R g κ (Tw + 1) st * c⁻¹
      = ∑' d : ℕ × ℤ, (F.hold d).toReal
          * (encExpect F T R g κ Tw (encStep F T R g st d) * c⁻¹) := by
    rw [hkey (Tw + 1) st,
      PMF.expect_iid_succ F.hold Tw _ (h0 (Tw + 1) st) (h1 (Tw + 1) st)]
    refine tsum_congr fun d => ?_
    rw [hkey Tw (encStep F T R g st d)]
    congr 1
    refine congrArg _ (funext fun w => ?_)
    have hlist : List.ofFn (Fin.cons d w : Fin (Tw + 1) → ℕ × ℤ)
        = d :: List.ofFn w := by
      rw [List.ofFn_succ]
      congr 1
    rw [hlist, List.foldl_cons]
  have hfin := congrArg (· * c) hmain
  simp only [mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one] at hfin
  rw [hfin, ← tsum_mul_right]
  exact tsum_congr fun d => by
    rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one]

/-- The trivial upper bound `encExpect ≤ exp(κR)`. -/
theorem encExpect_le {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (Tw : ℕ) (st : EncState) :
    encExpect F T R g κ Tw st ≤ Real.exp (κ * R) := by
  have hsum : Summable (fun v : Fin Tw → ℕ × ℤ => ((F.hold.iid Tw) v).toReal) :=
    ENNReal.summable_toReal (by rw [(F.hold.iid Tw).tsum_coe]; exact ENNReal.one_ne_top)
  have hle : ∀ v : Fin Tw → ℕ × ℤ,
      ((F.hold.iid Tw) v).toReal * encVal κ R ((List.ofFn v).foldl (encStep F T R g) st)
        ≤ ((F.hold.iid Tw) v).toReal * Real.exp (κ * R) :=
    fun v => mul_le_mul_of_nonneg_left (encVal_le κ hκ R _) ENNReal.toReal_nonneg
  have hsumR : Summable (fun v : Fin Tw → ℕ × ℤ =>
      ((F.hold.iid Tw) v).toReal * Real.exp (κ * R)) := hsum.mul_right _
  have hsumL : Summable (fun v : Fin Tw → ℕ × ℤ =>
      ((F.hold.iid Tw) v).toReal * encVal κ R ((List.ofFn v).foldl (encStep F T R g) st)) :=
    Summable.of_nonneg_of_le
      (fun v => mul_nonneg ENNReal.toReal_nonneg (encVal_pos κ R _).le) hle hsumR
  calc encExpect F T R g κ Tw st
      ≤ ∑' v : Fin Tw → ℕ × ℤ, ((F.hold.iid Tw) v).toReal * Real.exp (κ * R) :=
        Summable.tsum_le_tsum hle hsumL hsumR
    _ = Real.exp (κ * R) := by
        rw [tsum_mul_right, ← ENNReal.tsum_toReal_eq (fun v => PMF.apply_ne_top _ _),
          (F.hold.iid Tw).tsum_coe, ENNReal.toReal_one, one_mul]

theorem encExpect_nonneg {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ) (κ : ℝ)
    (Tw : ℕ) (st : EncState) : 0 ≤ encExpect F T R g κ Tw st :=
  tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (encVal_pos κ R _).le

end FW

end Family

end GGMCollatz
