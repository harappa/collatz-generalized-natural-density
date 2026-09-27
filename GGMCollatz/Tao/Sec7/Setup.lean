import GGMCollatz.Inter
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The setting of GGM §6: the phase `θ`, black and white points, triangle families (counterpart of the setting of §7.1 of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Setup.lean` (and
the definitional parts of `Sec7/Triangles.lean` and `Sec7/BlackEdge.lean`); generalized to the GGM family (p, q, r). Modified.
GGM (arXiv:2111.06170) §6 Steps 1 and 2, formula (def:theta).

* `sfrac`: the signed fractional part (values in `[-1/2, 1/2)`).
* `up n`: the unit `p ∈ (ZMod (q^n))ˣ` (condition (a)).
* `θq n c j l`: the phase `θ(j,l) = {c q^{2j} p^{1-l} / q^n}` (`j` starts at 0; GGM's `j` is `j_lean + 1`, so
  the exponent `2j - 2` becomes `2 j_lean`). In GGM, `c = ξ r(j₀)(p-1)` (`phaseC`).
* `θq_succ_j`, `θq_pred_l`: the recurrences `θ(j+1,l) = q²θ(j,l) + integer`, `θ(j,l-1) = pθ(j,l) + integer`.
* `black`, `white`: whether `|θ| ≤ ε` (GGM's `𝔅`).
* `goodDigit`, `phaseC`: a digit `j₀` with `q ∤ ξ r(j₀)` (by condition (d), `gcd_one`) and the phase multiplier.
* `edgeB`: the edge width `B` (the `B` of GGM §6 Step 2, for composite `q`).
* `triangle`: triangles with slope `log q² : log p` (GGM (def:triangles), (7.11) of tao-collatz).
* `TriFam half σ`: triangle families: mutually at distance at least `σ`, and at distance at least `σ` from the edge `{j = half}`
  (conditions (i), (ii) of GGM Theorem 1.9). `blk` is the union of the triangles, and `W` is the white set in renewal coordinates (starting at 1).
-/

namespace GGMCollatz

/-- The signed fractional part `x - round x` (values in `[-1/2, 1/2)`). -/
def sfrac (x : ℚ) : ℚ := x - round x

/-- `sfrac` is invariant under adding integers. -/
theorem sfrac_add_int (x : ℚ) (m : ℤ) : sfrac (x + m) = sfrac x := by
  unfold sfrac; rw [round_add_intCast]; push_cast; ring

/-- `|sfrac x| ≤ |x|`. -/
theorem abs_sfrac_le (x : ℚ) : |sfrac x| ≤ |x| := by
  rcases le_or_gt (1 / 2) |x| with h | h
  · exact le_trans (abs_sub_round x) h
  · have h' : |x| < 1 / 2 := h
    rw [abs_lt] at h'
    have hr : round x = 0 := by
      rw [round_eq]
      refine Int.floor_eq_zero_iff.mpr ⟨by linarith [h'.1], by linarith [h'.2]⟩
    unfold sfrac; rw [hr]; simp

/-- `|sfrac x| ≤ 1/2`. -/
theorem abs_sfrac_le_half (x : ℚ) : |sfrac x| ≤ 1 / 2 := abs_sub_round x

/-- `sfrac` takes values in `[-1/2, 1/2)`. -/
theorem sfrac_mem (x : ℚ) : -(1 / 2) ≤ sfrac x ∧ sfrac x < 1 / 2 := by
  unfold sfrac
  rw [round_eq]
  constructor
  · linarith [Int.floor_le (x + 1 / 2)]
  · linarith [Int.lt_floor_add_one (x + 1 / 2)]

/-- On `[-1/2, 1/2)`, `sfrac x = x`. -/
theorem sfrac_eq_self {x : ℚ} (h1 : -(1 / 2) ≤ x) (h2 : x < 1 / 2) : sfrac x = x := by
  unfold sfrac
  rw [round_eq]
  have : ⌊x + 1 / 2⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
  rw [this]; simp

/-- `sfrac` is idempotent. -/
theorem sfrac_idem (x : ℚ) : sfrac (sfrac x) = sfrac x :=
  sfrac_eq_self (sfrac_mem x).1 (sfrac_mem x).2

/-- If `y = c x + m` (`m ∈ ℤ`) then `sfrac y = c · sfrac x + integer`. -/
theorem sfrac_scale_of (c : ℤ) (x y : ℚ) (m : ℤ) (h : y = c * x + m) :
    ∃ k : ℤ, sfrac y = c * sfrac x + k := by
  refine ⟨c * round x - round ((c : ℚ) * x), ?_⟩
  unfold sfrac
  rw [h, round_add_intCast]
  push_cast
  ring

namespace Family

variable (F : Family)

/-! ### The unit `p` and the phase -/

/-- The unit `p ∈ (ZMod (q^n))ˣ`. -/
noncomputable def up (n : ℕ) : (ZMod (F.q ^ n))ˣ :=
  ZMod.unitOfCoprime F.p (Nat.Coprime.pow_right n F.coprime)

theorem up_val (n : ℕ) : ((F.up n : (ZMod (F.q ^ n))ˣ) : ZMod (F.q ^ n)) = F.p := by
  rw [up, ZMod.coe_unitOfCoprime]

/-- The phase point `W(j,l) = c q^{2j} p^{1-l} ∈ ZMod (q^n)`. -/
noncomputable def phasePt (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) : ZMod (F.q ^ n) :=
  (c : ZMod (F.q ^ n)) * (F.q : ZMod (F.q ^ n)) ^ (2 * j)
    * (((F.up n) ^ (1 - l) : (ZMod (F.q ^ n))ˣ) : ZMod (F.q ^ n))

/-- **The phase** `θ(j,l) = {c q^{2j} p^{1-l} / q^n}` (GGM (def:theta), `c = ξ r(j₀)(p-1)`). -/
noncomputable def θq (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) : ℚ :=
  sfrac (((F.phasePt n c j l).val : ℚ) / (F.q : ℚ) ^ n)

/-- If `W' = c' W` (in `ZMod (q^n)`), the phase arguments differ by the factor `c'` and an integer. -/
theorem argRel (n : ℕ) (c : ℤ) (W W' : ZMod (F.q ^ n))
    (hWW' : W' = (c : ZMod (F.q ^ n)) * W) :
    ∃ m : ℤ, ((W'.val : ℚ) / (F.q : ℚ) ^ n) = c * ((W.val : ℚ) / (F.q : ℚ) ^ n) + m := by
  have := F.neZero_q_pow n
  have hdvd : ((F.q : ℤ) ^ n) ∣ (c * (W.val : ℤ) - (W'.val : ℤ)) := by
    have hz : (((c * (W.val : ℤ) - (W'.val : ℤ)) : ℤ) : ZMod (F.q ^ n)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hWW']
      ring
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (F.q ^ n)).mp hz
    exact_mod_cast hd
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨-t, ?_⟩
  have h3 : (F.q : ℚ) ^ n ≠ 0 := by
    have := F.q_pos
    positivity
  have hval : (W'.val : ℚ) = c * (W.val : ℚ) - (F.q : ℚ) ^ n * t := by
    have hz2 : (W'.val : ℤ) = c * (W.val : ℤ) - (F.q : ℤ) ^ n * t := by linarith [ht]
    exact_mod_cast hz2
  rw [hval]; field_simp; push_cast; ring

/-- Recurrence: `θ(j+1,l) = q² θ(j,l) + integer` ((7.13) of tao-collatz). -/
theorem θq_succ_j (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) :
    ∃ k : ℤ, F.θq n c (j + 1) l = ((F.q : ℤ) ^ 2 : ℤ) * F.θq n c j l + k := by
  obtain ⟨m, hm⟩ := F.argRel n ((F.q : ℤ) ^ 2) (F.phasePt n c j l) (F.phasePt n c (j + 1) l)
    (by
      unfold phasePt
      rw [show 2 * (j + 1) = 2 * j + 2 from by ring, pow_add]
      push_cast; ring)
  obtain ⟨k, hk⟩ := sfrac_scale_of ((F.q : ℤ) ^ 2) _ _ m hm
  exact ⟨k, by simpa only [θq] using hk⟩

/-- Recurrence: `θ(j,l-1) = p θ(j,l) + integer` ((7.14) of tao-collatz). -/
theorem θq_pred_l (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) :
    ∃ k : ℤ, F.θq n c j (l - 1) = (F.p : ℤ) * F.θq n c j l + k := by
  obtain ⟨m, hm⟩ := F.argRel n (F.p : ℤ) (F.phasePt n c j l) (F.phasePt n c j (l - 1))
    (by
      unfold phasePt
      rw [show (1 : ℤ) - (l - 1) = (1 - l) + 1 from by ring, zpow_add_one, Units.val_mul,
        F.up_val]
      push_cast; ring)
  obtain ⟨k, hk⟩ := sfrac_scale_of (F.p : ℤ) _ _ m hm
  exact ⟨k, by simpa only [θq, Int.cast_natCast] using hk⟩

/-- `|θ| ≤ 1/2`. -/
theorem θq_abs_le_half (n : ℕ) (c : ℤ) (j : ℕ) (l : ℤ) : |F.θq n c j l| ≤ 1 / 2 :=
  abs_sfrac_le_half _

/-- Black points (GGM's `𝔅`, (7.9) of tao-collatz): `|θ(j,l)| ≤ ε`. -/
def black (n : ℕ) (c : ℤ) (ε : ℝ) (j : ℕ) (l : ℤ) : Prop := |((F.θq n c j l : ℚ) : ℝ)| ≤ ε

/-- White points: points that are not black. -/
def white (n : ℕ) (c : ℤ) (ε : ℝ) (j : ℕ) (l : ℤ) : Prop := ¬ F.black n c ε j l

/-! ### The good digit `j₀` and the phase multiplier -/

/-- From condition (d): if `q ∤ x`, there is a digit `0 < d < p` with `q ∤ x r(d)` (GGM §6 Step 1). -/
theorem exists_goodDigit {x : ℤ} (hx : ¬ (F.q : ℤ) ∣ x) :
    ∃ d : ℕ, 0 < d ∧ d < F.p ∧ ¬ (F.q : ℤ) ∣ x * F.r d := by
  by_contra hcon
  push Not at hcon
  -- `g = gcd(q, x)`, `q' = q / g`. For every digit `q' ∣ r(d)`, and `q' ∣ q`, so (d) gives `q' = 1`.
  set g : ℕ := Int.gcd (F.q : ℤ) x with hg
  have hq0 : (F.q : ℤ) ≠ 0 := by exact_mod_cast F.q_pos.ne'
  have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_left _ hq0
  have hgq : (g : ℤ) ∣ (F.q : ℤ) := Int.gcd_dvd_left _ _
  have hgx : (g : ℤ) ∣ x := Int.gcd_dvd_right _ _
  obtain ⟨q', hq'⟩ := hgq
  obtain ⟨x', hx'⟩ := hgx
  have hcop : IsCoprime q' x' := by
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
    have := Int.isCoprime_iff_gcd_eq_one.mpr
      (Int.gcd_ediv_gcd_ediv_gcd (i := (F.q : ℤ)) (j := x) (by rw [← hg]; exact hgpos))
    rw [← hg] at this
    have e1 : (F.q : ℤ) / g = q' := by rw [hq']; exact Int.mul_ediv_cancel_left _ hg0
    have e2 : x / g = x' := by rw [hx']; exact Int.mul_ediv_cancel_left _ hg0
    rwa [e1, e2] at this
  have hq'nn : 0 ≤ q' := by
    have hqpos : (0 : ℤ) < F.q := by exact_mod_cast F.q_pos
    rw [hq'] at hqpos
    have hgp : (0 : ℤ) < g := by exact_mod_cast hgpos
    exact le_of_lt (pos_of_mul_pos_right hqpos hgp.le)
  have hdig : ∀ d : ℕ, 0 < d → d < F.p → (q'.toNat : ℤ) ∣ F.r d := by
    intro d h0 hd
    have h := hcon d h0 hd
    rw [hq', hx'] at h
    have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hgpos.ne'
    have h2 : q' ∣ x' * F.r d := by
      have : (g : ℤ) * q' ∣ (g : ℤ) * (x' * F.r d) := by
        rw [show (g : ℤ) * (x' * F.r d) = g * x' * F.r d by ring]; exact h
      exact (mul_dvd_mul_iff_left hg0).mp this
    rw [Int.toNat_of_nonneg hq'nn]
    exact hcop.dvd_of_dvd_mul_left h2
  have hq'q : q'.toNat ∣ F.q := by
    have : (q'.toNat : ℤ) ∣ (F.q : ℤ) := by
      rw [Int.toNat_of_nonneg hq'nn, hq']; exact dvd_mul_left _ _
    exact_mod_cast this
  have h1 := F.gcd_one q'.toNat hq'q hdig
  have hq'1 : q' = 1 := by
    have : (q'.toNat : ℤ) = 1 := by exact_mod_cast h1
    rwa [Int.toNat_of_nonneg hq'nn] at this
  apply hx
  rw [hq', hq'1, mul_one]
  exact Int.gcd_dvd_right _ _

open Classical in
/-- The good digit `j₀`: a digit with `q ∤ x r(j₀)` (formally `1` if there is none). -/
noncomputable def goodDigit (x : ℤ) : ℕ :=
  if h : ∃ d : ℕ, 0 < d ∧ d < F.p ∧ ¬ (F.q : ℤ) ∣ x * F.r d then Classical.choose h else 1

theorem goodDigit_pos_lt (x : ℤ) : 0 < F.goodDigit x ∧ F.goodDigit x < F.p := by
  unfold goodDigit
  split_ifs with h
  · exact ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2.1⟩
  · exact ⟨by norm_num, F.one_lt_p⟩

theorem goodDigit_spec {x : ℤ} (hx : ¬ (F.q : ℤ) ∣ x) :
    ¬ (F.q : ℤ) ∣ x * F.r (F.goodDigit x) := by
  have h := F.exists_goodDigit hx
  unfold goodDigit
  rw [dif_pos h]
  exact (Classical.choose_spec h).2.2

/-- The phase multiplier `c = ξ r(j₀)(p-1)` (GGM (def:theta)). -/
noncomputable def phaseC (ξ : ℕ) : ℤ := (ξ : ℤ) * F.r (F.goodDigit ξ) * ((F.p : ℤ) - 1)

/-- The edge width `B` (GGM §6 Step 2; if `q ∤ ξ r(j₀)` then `q^{2B+2} ∤ ξ r(j₀)(p-1)`). -/
def edgeB : ℕ := F.p

/-- The separation coefficient: triangles are at distance at least `sepc · log(1/ε)` from each other. -/
noncomputable def sepc : ℝ := 1 / (10 * Real.log ((F.p : ℝ) * (F.q : ℝ) ^ 2))

/-- The separation width `σ(ε) = sepc · log(1/ε)`. -/
noncomputable def sep (ε : ℝ) : ℝ := F.sepc * Real.log (1 / ε)

/-! ### Triangles and triangle families -/

/-- The triangle with apex `(j₀, l₀)` and size `s` (GGM (def:triangles), (7.11) of tao-collatz):
`j ≥ j₀`, `l ≤ l₀`, `(j - j₀) log q² + (l₀ - l) log p ≤ s`. -/
def triangle (j₀ : ℕ) (l₀ : ℤ) (s : ℝ) : Set (ℕ × ℤ) :=
  {x | j₀ ≤ x.1 ∧ x.2 ≤ l₀ ∧
    ((x.1 : ℝ) - j₀) * Real.log ((F.q : ℝ) ^ 2) + ((l₀ : ℝ) - x.2) * Real.log F.p ≤ s}

/-- **Triangle family** (conditions (i), (ii) of GGM Theorem 1.9, `TriangleFamily` of tao-collatz):
sizes are nonnegative, points of distinct triangles are at Euclidean distance at least `σ`, and every point satisfies `j + 1 ≤ half - σ`. -/
structure TriFam (half : ℕ) (σ : ℝ) where
  /-- The triangle parameters (apex `(j₀, l₀)`, size `s`). -/
  T : Set (ℕ × ℤ × ℝ)
  size_nonneg : ∀ t ∈ T, 0 ≤ t.2.2
  separated : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
    ∀ x ∈ F.triangle t.1 t.2.1 t.2.2, ∀ x' ∈ F.triangle t'.1 t'.2.1 t'.2.2,
      σ ^ 2 ≤ ((x.1 : ℝ) - x'.1) ^ 2 + ((x.2 : ℝ) - x'.2) ^ 2
  confined : ∀ t ∈ T, ∀ x ∈ F.triangle t.1 t.2.1 t.2.2, (x.1 : ℝ) + 1 ≤ (half : ℝ) - σ

variable {F}

/-- The union of the family's triangles (phase coordinates, `j` starting at 0). -/
def TriFam.blk {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) : Set (ℕ × ℤ) :=
  ⋃ t ∈ T.T, F.triangle t.1 t.2.1 t.2.2

/-- The white set in renewal coordinates (`j` starting at 1): `(j, l)` is white when `(j - 1, l)` lies in no triangle
(the positional reinterpretation of `whiteSet` of tao-collatz). -/
def TriFam.W {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) : Set (ℕ × ℤ) :=
  {x | 1 ≤ x.1 ∧ (x.1 - 1, x.2) ∉ T.blk}

end Family

end GGMCollatz
