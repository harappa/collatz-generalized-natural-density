import GGMCollatz.NatDen.UProf.Conc
import GGMCollatz.NatDen.UProf.URD
import GGMCollatz.NatDen.UProf.Master
import GGMCollatz.NatDen.UProf.Final
import GGMCollatz.NatDen.UProf.DKern
import GGMCollatz.NatDen.UProf.EPrime

/-!
# The profile on the uniform side

`uprof_of_parts`: from the weighted form of (KRON) ((IRR) acts only through it), (LCLT), Proposition 6.12 (c) of the paper (and GGM
Props. 3.1 and 4.1), the law of the first-passage location for the uniform window is close to `(μ/d) ψ`.

Decomposition (statements in `NatDen/UProf/Statements.lean`, definitions in `NatDen/UProf/Defs.lean`):
`P_unif(Pass ∈ E) ≈ (1/Z) Σ_n urow(n)` ((UC)) `≈ (1/Z) Σ_n umain(n)` ((URD)) `≈ kernSum/Z` ((UM))
`≈ (μ/d) ψ(E)` ((UF), using the kernel bound (DK) and the structure (EP1) of `E'`). (UM) also uses the
flatness (EP2) of `E'` ((URD) uses no hypotheses). `uprof_of_four` is the triangle inequality for these four
steps (no `sorry`).
-/

namespace GGMCollatz

namespace ND

variable (F : Family)

/-- Chain the four approximations (triangle inequality). -/
theorem uprof_of_four (hUC : uconc_statement F) (hURD : urd_statement F)
    (hUM : umaster_statement F) (hUF : ufinal_statement F) : uprof_statement F := by
  obtain ⟨a₁, ha₁, h₁⟩ := hUC
  obtain ⟨a₂, ha₂, h₂⟩ := hURD
  obtain ⟨a₃, ha₃, h₃⟩ := hUM
  obtain ⟨a₄, ha₄, h₄⟩ := hUF
  refine ⟨min (min a₁ a₂) (min a₃ a₄), lt_min (lt_min ha₁ ha₂) (lt_min ha₃ ha₄), ?_⟩
  intro α hα hαa
  have hα₁ : α ≤ a₁ := le_trans hαa (le_trans (min_le_left _ _) (min_le_left _ _))
  have hα₂ : α ≤ a₂ := le_trans hαa (le_trans (min_le_left _ _) (min_le_right _ _))
  have hα₃ : α ≤ a₃ := le_trans hαa (le_trans (min_le_right _ _) (min_le_left _ _))
  have hα₄ : α ≤ a₄ := le_trans hαa (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨c₁, K₁, hc₁, hK₁, e₁⟩ := h₁ α hα hα₁
  obtain ⟨c₂, K₂, hc₂, hK₂, e₂⟩ := h₂ α hα hα₂
  obtain ⟨c₃, K₃, hc₃, hK₃, e₃⟩ := h₃ α hα hα₃
  obtain ⟨c₄, K₄, hc₄, hK₄, e₄⟩ := h₄ α hα hα₄
  set c : ℝ := min (min c₁ c₂) (min c₃ c₄) with hcdef
  have hc : 0 < c := lt_min (lt_min hc₁ hc₂) (lt_min hc₃ hc₄)
  refine ⟨c, K₁ + K₂ + K₃ + K₄, hc, by positivity, ?_⟩
  filter_upwards [e₁, e₂, e₃, e₄, Family.eventually_log_ge 1] with x hx₁ hx₂ hx₃ hx₄ hL
  intro E
  obtain ⟨hZ, hx₁⟩ := hx₁
  obtain ⟨-, hx₄⟩ := hx₄
  set Z := wCard F α x with hZdef
  set L := Real.log x with hLdef
  have hmono : ∀ c' : ℝ, c ≤ c' → L ^ (-c') ≤ L ^ (-c) := fun c' h =>
    Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg h)
  have m₁ := hmono c₁ (le_trans (min_le_left _ _) (min_le_left _ _))
  have m₂ := hmono c₂ (le_trans (min_le_left _ _) (min_le_right _ _))
  have m₃ := hmono c₃ (le_trans (min_le_right _ _) (min_le_left _ _))
  have m₄ := hmono c₄ (le_trans (min_le_right _ _) (min_le_right _ _))
  set P := Family.expect (unifWin F (x ^ α) ((x ^ α) ^ α))
    (Set.indicator {N | F.passLoc ⌊x⌋₊ N ∈ E} 1) with hPdef
  set R := ∑ n ∈ rows F α x, (urow F α x E n : ℝ) with hRdef
  set U := ∑ n ∈ rows F α x, umain F α x E n with hUdef
  set S := kernSum F α x E with hSdef
  have d₂ : |R / Z - U / Z| ≤ K₂ * L ^ (-c₂) := by
    rw [← sub_div, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    have := hx₂ E; linarith
  have d₃ : |U / Z - S / Z| ≤ K₃ * L ^ (-c₃) := by
    rw [← sub_div, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    have := hx₃ E; linarith
  have t₁ := hx₁ E
  have t₄ := hx₄ E
  calc |P - F.mu / F.drift * F.psi α x E|
      ≤ |P - R / Z| + |R / Z - U / Z| + |U / Z - S / Z| + |S / Z - F.mu / F.drift * F.psi α x E| := by
        have a1 := abs_sub_le P (R / Z) (U / Z)
        have a2 := abs_sub_le P (U / Z) (S / Z)
        have a3 := abs_sub_le P (S / Z) (F.mu / F.drift * F.psi α x E)
        linarith
    _ ≤ K₁ * L ^ (-c₁) + K₂ * L ^ (-c₂) + K₃ * L ^ (-c₃) + K₄ * L ^ (-c₄) := by
        gcongr
    _ ≤ K₁ * L ^ (-c) + K₂ * L ^ (-c) + K₃ * L ^ (-c) + K₄ * L ^ (-c) := by
        gcongr
    _ = (K₁ + K₂ + K₃ + K₄) * L ^ (-c) := by ring

/-- **The profile on the uniform side** (Proposition 7.24 of the paper; the uniform side of (D.3)). The hypotheses are only
(KRON-W) (with its `μ ≥ 2`), (LCLT) and Proposition 6.12 (c) of the paper: (IRR) acts only through (KRON-W), (URD) uses no hypotheses,
and (UM) does not use (LCLT) (the unused arguments were removed after a referee pointed them out). -/
theorem uprof_of_parts {μ : ℝ} (hμ : 2 ≤ μ)
    (hkw : kronW_statement (lam F) μ) (hL : lclt_statement F.p) (hC : summixC_statement F) :
    uprof_statement F := by
  have h1 := eprimeC F
  have h2 := eprimeFlat F
  have hDK := dkern F hμ hkw hL
  exact uprof_of_four F (uconc F) (urd F) (umaster F hC h1 h2) (ufinal F hDK h1)

end ND

end GGMCollatz
