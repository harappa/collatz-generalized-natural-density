import GGMCollatz.Tao.Sec7.FW710Sum

/-!
# Geometry for Lemma 7.10: proximity of apices, and separation of the apices of the large triangles that can be met

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/ManyTriangles.lean`
(`encounter_apex_proximity`, `qualifying_apex_separated`) and from GGM (arXiv:2111.06170) §7 Step 4;
generalized to the GGM family (p, q, r). Modified. The explicit constants and phase facts of tao-collatz are not used; only the separation of the triangle family is.
Notation: `Lq = log q²`, `Lp = log p`. A triangle `t₀ ∋ (j, l)`, budget `s = l_Δ - l`.

* `not_mem_both`: distinct triangles of the family have no common point (`σ > 0`).
* `top_mem`: if `X₁ Lq ≤ s Lp`, the points `(k, l_Δ)` of the top row with `j ≤ k ≤ j + X₁` lie in `t₀`.
* `proximity`: if a good endpoint (`s < X₂ < s + H`, `X₁ Lq ≤ s Lp`, `X₁ ≥ W₀ ≥ H`) lies in a triangle `t'`, then
  the apex column of `t'` is within `W₀` of the endpoint column, and the top height of `t'` is within `O(W₀)` of `l_Δ + s_{t'}/Lp`.
* `row_mem`, `apex_sep`: on the row at height `l_Δ + ⌊s'/(2Lp)⌋`, two triangles of size `≥ s'` contain intervals of length `≍ s'`,
  so their apex columns are more than `⌊s'/(4Lq)⌋` apart.
-/

namespace GGMCollatz

namespace Family

namespace FW

namespace T710

variable (F : Family)

theorem log_p_le_log_q_sq : Real.log (F.p : ℝ) ≤ Real.log ((F.q : ℝ) ^ 2) := by
  have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  have hpq : (F.p : ℝ) ≤ F.q := by exact_mod_cast F.p_lt_q.le
  apply Real.log_le_log (by linarith)
  nlinarith

/-- Distinct triangles of the family have no common point. -/
theorem not_mem_both {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (hσ : 0 < σ)
    {t t' : ℕ × ℤ × ℝ} (ht : t ∈ T.T) (ht' : t' ∈ T.T) (hne : t ≠ t') {y : ℕ × ℤ}
    (hy : y ∈ F.triangle t.1 t.2.1 t.2.2) (hy' : y ∈ F.triangle t'.1 t'.2.1 t'.2.2) : False := by
  have h := T.separated t ht t' ht' hne y hy y hy'
  rw [sub_self, sub_self] at h
  have : 0 < σ ^ 2 := by positivity
  norm_num at h
  linarith

/-- The points of the top row lie in `t₀`. -/
theorem top_mem {t₀ : ℕ × ℤ × ℝ} {j : ℕ} {l : ℤ}
    (hmem : (j, l) ∈ F.triangle t₀.1 t₀.2.1 t₀.2.2) {s : ℕ} (hs : (s : ℤ) = t₀.2.1 - l)
    {X1 : ℕ} (hX1 : (X1 : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ (s : ℝ) * Real.log F.p)
    {k : ℕ} (hk1 : j ≤ k) (hk2 : k ≤ j + X1) :
    ((k, t₀.2.1) : ℕ × ℤ) ∈ F.triangle t₀.1 t₀.2.1 t₀.2.2 := by
  obtain ⟨h1, h2, h3⟩ := hmem
  simp only at h1 h2 h3
  have hLq := Family.WE.log_q_sq_pos F
  refine ⟨le_trans h1 hk1, le_refl _, ?_⟩
  simp only
  have hsR : ((t₀.2.1 : ℝ) - l) = s := by
    have : ((s : ℤ) : ℝ) = ((t₀.2.1 - l : ℤ) : ℝ) := by rw [hs]
    push_cast at this; linarith
  have hkR : (k : ℝ) ≤ j + X1 := by exact_mod_cast hk2
  rw [hsR] at h3
  nlinarith

/-- **Proximity of apices** (GGM §7 Step 4, `encounter_apex_proximity` of tao-collatz). -/
theorem proximity {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (hσ : 0 < σ)
    {t₀ : ℕ × ℤ × ℝ} (ht₀ : t₀ ∈ T.T) {j : ℕ} {l : ℤ}
    (hmem : (j, l) ∈ F.triangle t₀.1 t₀.2.1 t₀.2.2) {s : ℕ} (hs : (s : ℤ) = t₀.2.1 - l)
    {H : ℝ} {W₀ : ℕ} (hHW : H ≤ W₀) {X : ℕ × ℤ} (hX2lo : (s : ℤ) < X.2)
    (hX2hi : (X.2 : ℝ) < s + H)
    (hX1col : (X.1 : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ (s : ℝ) * Real.log F.p) (hX1W : W₀ ≤ X.1)
    {t' : ℕ × ℤ × ℝ} (ht' : t' ∈ T.T)
    (hx : ((j + X.1, l + X.2) : ℕ × ℤ) ∈ F.triangle t'.1 t'.2.1 t'.2.2) :
    t'.1 ≤ j + X.1 ∧ j + X.1 < t'.1 + W₀ ∧
      t'.2.2 - W₀ * Real.log ((F.q : ℝ) ^ 2) ≤ ((t'.2.1 : ℝ) - t₀.2.1) * Real.log F.p ∧
      ((t'.2.1 : ℝ) - t₀.2.1) < H + t'.2.2 / Real.log F.p := by
  set Lq := Real.log ((F.q : ℝ) ^ 2) with hLqdef
  set Lp := Real.log (F.p : ℝ) with hLpdef
  have hLq : 0 < Lq := Family.WE.log_q_sq_pos F
  have hLp : 0 < Lp := Family.WE.log_p_pos F
  have hLpq : Lp ≤ Lq := log_p_le_log_q_sq F
  obtain ⟨hx1, hx2, hx3⟩ := hx
  simp only at hx1 hx2 hx3
  have hsR : ((t₀.2.1 : ℝ) - l) = s := by
    have : ((s : ℤ) : ℝ) = ((t₀.2.1 - l : ℤ) : ℝ) := by rw [hs]
    push_cast at this; linarith
  -- `t' ≠ t₀`
  have hne : t₀ ≠ t' := by
    intro heq
    rw [← heq] at hx2
    omega
  have htop : t₀.2.1 ≤ t'.2.1 := by omega
  have htopR : (t₀.2.1 : ℝ) ≤ t'.2.1 := by exact_mod_cast htop
  have hx2R : ((l + X.2 : ℤ) : ℝ) ≤ t'.2.1 := by exact_mod_cast hx2
  push_cast at hx3 hx2R
  -- (2) proximity of columns
  have h2 : j + X.1 < t'.1 + W₀ := by
    by_contra hc
    push Not at hc
    set k := j + X.1 - W₀ with hk
    have hmem0 := top_mem F hmem hs hX1col (k := k) (by omega) (by omega)
    have hmem' : ((k, t₀.2.1) : ℕ × ℤ) ∈ F.triangle t'.1 t'.2.1 t'.2.2 := by
      refine ⟨by omega, htop, ?_⟩
      simp only
      have hkR : (k : ℝ) = (j : ℝ) + X.1 - W₀ := by
        rw [hk, Nat.cast_sub (by omega)]; push_cast; ring
      rw [hkR]
      have hX2R : (X.2 : ℝ) - s ≤ W₀ := by linarith
      nlinarith
    exact not_mem_both F T hσ ht₀ ht' hne hmem0 hmem'
  refine ⟨hx1, h2, ?_, ?_⟩
  · -- (3) lower bound on the top height
    by_contra hc
    push Not at hc
    have hmem0 := top_mem F hmem hs hX1col (k := j + X.1) (by omega) le_rfl
    have hmem' : ((j + X.1, t₀.2.1) : ℕ × ℤ) ∈ F.triangle t'.1 t'.2.1 t'.2.2 := by
      refine ⟨hx1, htop, ?_⟩
      simp only
      have hd : ((j + X.1 : ℕ) : ℝ) - t'.1 ≤ W₀ := by
        have : j + X.1 - t'.1 ≤ W₀ := by omega
        have h' : ((j + X.1 - t'.1 : ℕ) : ℝ) ≤ W₀ := by exact_mod_cast this
        rw [Nat.cast_sub hx1] at h'
        exact h'
      nlinarith
    exact not_mem_both F T hσ ht₀ ht' hne hmem0 hmem'
  · -- (4) upper bound on the top height
    have hjt : (0 : ℝ) ≤ ((j + X.1 : ℕ) : ℝ) - t'.1 := by
      have : (t'.1 : ℝ) ≤ ((j + X.1 : ℕ) : ℝ) := by exact_mod_cast hx1
      linarith
    have hx3' : ((t'.2.1 : ℝ) - (l + X.2)) * Lp ≤ t'.2.2 := by
      push_cast at hjt
      nlinarith
    have hdiv : (t'.2.1 : ℝ) - (l + X.2) ≤ t'.2.2 / Lp := by
      rw [le_div_iff₀ hLp]; exact hx3'
    linarith

/-- **Row interval**: on the row at height `l_Δ + ⌊s'/(2Lp)⌋`, if `a Lq ≤ s'/4` then `(t'.1 + a, ·)` lies in `t'`. -/
theorem row_mem {t₀ t' : ℕ × ℤ × ℝ} {H : ℝ} {W₀ s' : ℕ} (hsize : (s' : ℝ) ≤ t'.2.2)
    (h3 : t'.2.2 - W₀ * Real.log ((F.q : ℝ) ^ 2) ≤ ((t'.2.1 : ℝ) - t₀.2.1) * Real.log F.p)
    (h4 : ((t'.2.1 : ℝ) - t₀.2.1) < H + t'.2.2 / Real.log F.p)
    (hR1 : 2 * (W₀ : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ s')
    (hR2 : 4 * (H + 1) * Real.log F.p ≤ s')
    (a : ℕ) (ha : (a : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ s' / 4) :
    ((t'.1 + a, t₀.2.1 + (⌊(s' : ℝ) / (2 * Real.log F.p)⌋₊ : ℤ)) : ℕ × ℤ)
      ∈ F.triangle t'.1 t'.2.1 t'.2.2 := by
  set Lq := Real.log ((F.q : ℝ) ^ 2) with hLqdef
  set Lp := Real.log (F.p : ℝ) with hLpdef
  have hLq : 0 < Lq := Family.WE.log_q_sq_pos F
  have hLp : 0 < Lp := Family.WE.log_p_pos F
  set r : ℕ := ⌊(s' : ℝ) / (2 * Lp)⌋₊ with hr
  have hr1 : (r : ℝ) ≤ s' / (2 * Lp) := Nat.floor_le (by positivity)
  have hr2 : (s' : ℝ) / (2 * Lp) < r + 1 := Nat.lt_floor_add_one _
  have hrLp : (r : ℝ) * Lp ≤ s' / 2 := by
    have := mul_le_mul_of_nonneg_right hr1 hLp.le
    rw [div_mul_eq_mul_div, mul_div_assoc] at this
    have e : Lp / (2 * Lp) = 1 / 2 := by field_simp
    rw [e] at this; linarith
  have hrLp2 : (s' : ℝ) / 2 - Lp < (r : ℝ) * Lp := by
    have := mul_lt_mul_of_pos_right hr2 hLp
    have e : (s' : ℝ) / (2 * Lp) * Lp = s' / 2 := by field_simp
    rw [e] at this; linarith
  have hdiff : (r : ℝ) * Lp ≤ ((t'.2.1 : ℝ) - t₀.2.1) * Lp := by linarith
  have hdiffR : (r : ℝ) ≤ (t'.2.1 : ℝ) - t₀.2.1 := le_of_mul_le_mul_right hdiff hLp
  refine ⟨Nat.le_add_right _ _, ?_, ?_⟩
  · simp only
    have : ((t₀.2.1 + (r : ℤ) : ℤ) : ℝ) ≤ t'.2.1 := by push_cast; linarith
    exact_mod_cast this
  · simp only
    push_cast
    have h4' : ((t'.2.1 : ℝ) - t₀.2.1) * Lp < H * Lp + t'.2.2 := by
      have := mul_lt_mul_of_pos_right h4 hLp
      rw [add_mul, div_mul_cancel₀ _ hLp.ne'] at this
      exact this
    nlinarith

/-- **Separation of apices**: the apex columns of two distinct triangles of size `≥ s'` that can be met are more than `⌊s'/(4Lq)⌋` apart. -/
theorem apex_sep {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (hσ : 0 < σ)
    {t₀ t' t'' : ℕ × ℤ × ℝ} (ht' : t' ∈ T.T) (ht'' : t'' ∈ T.T) (hne : t' ≠ t'')
    {H : ℝ} {W₀ s' : ℕ} (hsize' : (s' : ℝ) ≤ t'.2.2) (hsize'' : (s' : ℝ) ≤ t''.2.2)
    (h3' : t'.2.2 - W₀ * Real.log ((F.q : ℝ) ^ 2) ≤ ((t'.2.1 : ℝ) - t₀.2.1) * Real.log F.p)
    (h4' : ((t'.2.1 : ℝ) - t₀.2.1) < H + t'.2.2 / Real.log F.p)
    (h3'' : t''.2.2 - W₀ * Real.log ((F.q : ℝ) ^ 2) ≤ ((t''.2.1 : ℝ) - t₀.2.1) * Real.log F.p)
    (h4'' : ((t''.2.1 : ℝ) - t₀.2.1) < H + t''.2.2 / Real.log F.p)
    (hR1 : 2 * (W₀ : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ s')
    (hR2 : 4 * (H + 1) * Real.log F.p ≤ s') (hle : t'.1 ≤ t''.1) :
    t'.1 + ⌊(s' : ℝ) / (4 * Real.log ((F.q : ℝ) ^ 2))⌋₊ < t''.1 := by
  have hLq : 0 < Real.log ((F.q : ℝ) ^ 2) := Family.WE.log_q_sq_pos F
  by_contra hc
  push Not at hc
  set a := t''.1 - t'.1 with ha
  have haR : (a : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ s' / 4 := by
    have h1 : a ≤ ⌊(s' : ℝ) / (4 * Real.log ((F.q : ℝ) ^ 2))⌋₊ := by omega
    have h2 : (a : ℝ) ≤ (s' : ℝ) / (4 * Real.log ((F.q : ℝ) ^ 2)) :=
      le_trans (by exact_mod_cast h1) (Nat.floor_le (by positivity))
    have := mul_le_mul_of_nonneg_right h2 hLq.le
    have e : (s' : ℝ) / (4 * Real.log ((F.q : ℝ) ^ 2)) * Real.log ((F.q : ℝ) ^ 2) = s' / 4 := by
      field_simp
    linarith
  have hy' := row_mem F (t₀ := t₀) hsize' h3' h4' hR1 hR2 a haR
  have hy'' := row_mem F (t₀ := t₀) hsize'' h3'' h4'' hR1 hR2 0 (by simp; positivity)
  have heq : t'.1 + a = t''.1 + 0 := by omega
  rw [heq] at hy'
  exact not_mem_both F T hσ ht' ht'' hne hy' hy''

end T710

end FW

end Family

end GGMCollatz
