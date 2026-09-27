import GGMCollatz.Tao.Sec7.Case2
import GGMCollatz.Tao.Sec7.Case3

/-!
# GGM §7: bounds at black edges (Cases 2 and 3), Proposition 7.8 and (7.37) (counterpart of §7.4 of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, files `TaoCollatz/Sec7/BlackEdge.lean`,
`Sec7/BlackEdgeQ.lean`, `Sec7/Case3.lean` (`Q_black_edge_at`, `prop_7_8`, `Q_polynomial_decay`);
generalized to the GGM family (p, q, r). Modified. GGM §7 from Step 1 on (the proof of Theorem 1.9).

The white set is `T.W`, built from a triangle family `T : F.TriFam half (F.sep ε)` (points outside the triangles are white).
The decay rate is `κ = ε³` (the "replace `ε` by `ε³`" of GGM §6).

* `budget_le_of_mem_triangle`: (7.52) of tao-collatz. The height budget `s = l_Δ - l` of an edge point at depth `m` satisfies
  `s log p ≤ (m+2) log q²`.
* Uses `Q_black_edge_case2` (`s ≤ m / log² m`, `Case2.lean`) and `Q_black_edge_case3`
  (`s > m / log² m`, `Case3.lean`).
* `Q_black_edge`: assembly of the case distinction. `prop_7_8`: Proposition 7.8. `Q_polynomial_decay`: (7.37).
-/

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- `log q² > 0`. -/
theorem log_q_sq_pos : 0 < Real.log ((F.q : ℝ) ^ 2) := by
  apply Real.log_pos
  have : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
  nlinarith

/-- `log p > 0`. -/
theorem log_p_pos : 0 < Real.log (F.p : ℝ) := by
  apply Real.log_pos
  have : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
  linarith

/-- **Height budget** ((7.52) of tao-collatz): for a point of a triangle at depth `≤ m + 1` from the edge, the budget `s = l_Δ - l` satisfies
`s log p ≤ (m+2) log q²`. -/
theorem budget_le_of_mem_triangle {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (hσ : 0 ≤ σ)
    {t : ℕ × ℤ × ℝ} (ht : t ∈ T.T) {j : ℕ} {l : ℤ}
    (hmem : (j, l) ∈ F.triangle t.1 t.2.1 t.2.2) {m : ℕ} (hjm : half ≤ j + 1 + m) :
    ((t.2.1 - l).toNat : ℝ) * Real.log F.p ≤ ((m : ℝ) + 2) * Real.log ((F.q : ℝ) ^ 2) := by
  obtain ⟨hj0, hl0, hlin⟩ := hmem
  have hsz0 : 0 ≤ t.2.2 := T.size_nonneg t ht
  have hlq := F.log_q_sq_pos
  have hlp := F.log_p_pos
  set K : ℕ := ⌊t.2.2 / Real.log ((F.q : ℝ) ^ 2)⌋₊ with hK
  have hKle : (K : ℝ) * Real.log ((F.q : ℝ) ^ 2) ≤ t.2.2 := by
    have hfl : (K : ℝ) ≤ t.2.2 / Real.log ((F.q : ℝ) ^ 2) := Nat.floor_le (by positivity)
    calc (K : ℝ) * Real.log ((F.q : ℝ) ^ 2)
        ≤ t.2.2 / Real.log ((F.q : ℝ) ^ 2) * Real.log ((F.q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hfl hlq.le
      _ = t.2.2 := div_mul_cancel₀ _ hlq.ne'
  have hqmem : ((t.1 + K, t.2.1) : ℕ × ℤ) ∈ F.triangle t.1 t.2.1 t.2.2 := by
    refine ⟨Nat.le_add_right _ _, le_refl _, ?_⟩
    push_cast
    have h : ((t.1 : ℝ) + K - t.1) * Real.log ((F.q : ℝ) ^ 2)
        = (K : ℝ) * Real.log ((F.q : ℝ) ^ 2) := by ring
    rw [h]
    simpa using hKle
  have hconf := T.confined t ht _ hqmem
  have h3 : (t.1 : ℝ) + K + 1 ≤ (half : ℝ) := by
    push_cast at hconf
    linarith
  have h5 : (half : ℝ) ≤ (j : ℝ) + 1 + m := by exact_mod_cast hjm
  have hK1 : t.2.2 < ((K : ℝ) + 1) * Real.log ((F.q : ℝ) ^ 2) := by
    have hlt : t.2.2 / Real.log ((F.q : ℝ) ^ 2) < (K : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (t.2.2 / Real.log ((F.q : ℝ) ^ 2))
      rw [← hK] at this
      exact this
    calc t.2.2 = t.2.2 / Real.log ((F.q : ℝ) ^ 2) * Real.log ((F.q : ℝ) ^ 2) :=
          (div_mul_cancel₀ _ hlq.ne').symm
      _ < ((K : ℝ) + 1) * Real.log ((F.q : ℝ) ^ 2) := mul_lt_mul_of_pos_right hlt hlq
  have htn : (((t.2.1 - l).toNat : ℕ) : ℝ) = (t.2.1 : ℝ) - l := by
    have h := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ t.2.1 - l)
    have : (((t.2.1 - l).toNat : ℕ) : ℤ) = t.2.1 - l := h
    exact_mod_cast this
  have h6 : (K : ℝ) + 1 - j + t.1 ≤ (m : ℝ) + 2 := by linarith
  calc ((t.2.1 - l).toNat : ℝ) * Real.log F.p
      = ((t.2.1 : ℝ) - l) * Real.log F.p := by rw [htn]
    _ ≤ t.2.2 - ((j : ℝ) - t.1) * Real.log ((F.q : ℝ) ^ 2) := by linarith [hlin]
    _ ≤ ((K : ℝ) + 1) * Real.log ((F.q : ℝ) ^ 2)
          - ((j : ℝ) - t.1) * Real.log ((F.q : ℝ) ^ 2) := by linarith
    _ = ((K : ℝ) + 1 - j + t.1) * Real.log ((F.q : ℝ) ^ 2) := by ring
    _ ≤ ((m : ℝ) + 2) * Real.log ((F.q : ℝ) ^ 2) := mul_le_mul_of_nonneg_right h6 hlq.le

/-- If `ε ≤ 1`, the separation width is nonnegative. -/
theorem sep_nonneg {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ F.sep ε := by
  unfold sep sepc
  have hlpq : 0 < Real.log ((F.p : ℝ) * (F.q : ℝ) ^ 2) := by
    apply Real.log_pos
    have hp : (2 : ℝ) ≤ F.p := by exact_mod_cast F.two_le_p
    have hq : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
    nlinarith
  have hl : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  positivity

/-- **Bound at black edges** (`Q_black_edge` of tao-collatz, the black case of (7.41)): case distinction between Case 2 and Case 3. -/
theorem Q_black_edge :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ, 0 < A →
      ∃ Cthr : ℕ, ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (m : ℕ), Cthr ≤ m → m ≤ half →
        ∀ l : ℤ, 1 ≤ half - m → (half - m, l) ∉ T.W →
        F.Q half T.W (ε ^ 3) (half - m) l
          ≤ (m : ℝ) ^ (-A) * F.Qm half T.W (ε ^ 3) A (m - 1) := by
  obtain ⟨ε₂, hε₂, h2⟩ := F.Q_black_edge_case2
  obtain ⟨ε₃, hε₃, h3⟩ := F.Q_black_edge_case3
  refine ⟨min (min ε₂ ε₃) 1, lt_min (lt_min hε₂ hε₃) one_pos, ?_⟩
  intro ε hε hεle A hA
  have hε2 : ε ≤ ε₂ := le_trans hεle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε3 : ε ≤ ε₃ := le_trans hεle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε1 : ε ≤ 1 := le_trans hεle (min_le_right _ _)
  obtain ⟨C2, hC2⟩ := h2 ε hε hε2 A hA
  obtain ⟨C3, hC3⟩ := h3 ε hε hε3 A hA
  refine ⟨max C2 C3, ?_⟩
  intro half T m hm hmn l h1 hnw
  -- the phase point `(half - m - 1, l)` lies in a triangle
  have hblk : (half - m - 1, l) ∈ T.blk := by
    by_contra hc
    apply hnw
    refine ⟨h1, ?_⟩
    simpa using hc
  simp only [TriFam.blk, Set.mem_iUnion, exists_prop] at hblk
  obtain ⟨t, ht, hmem⟩ := hblk
  have hl : l ≤ t.2.1 := hmem.2.1
  set s : ℕ := (t.2.1 - l).toNat with hs
  have hsZ : (s : ℤ) = t.2.1 - l := by omega
  have hbudget : (s : ℝ) * Real.log F.p ≤ ((m : ℝ) + 2) * Real.log ((F.q : ℝ) ^ 2) :=
    F.budget_le_of_mem_triangle T (F.sep_nonneg hε hε1) ht hmem (by omega)
  rcases le_or_gt (s : ℝ) ((m : ℝ) / Real.log m ^ 2) with hcase | hcase
  · exact hC2 half T m (le_trans (le_max_left _ _) hm) hmn l h1 t ht hmem s hsZ hcase
  · exact hC3 half T m (le_trans (le_max_right _ _) hm) hmn l h1 t ht hmem s hsZ hcase hbudget

/-- **Proposition 7.8** (monotonicity): `Q_m ≤ Q_{m-1}` (`Cthr ≤ m ≤ half`, with a threshold independent of `half` and `T`). -/
theorem prop_7_8 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ, 0 < A →
      ∃ Cthr : ℕ, ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (m : ℕ), Cthr ≤ m → m ≤ half →
        F.Qm half T.W (ε ^ 3) A m ≤ F.Qm half T.W (ε ^ 3) A (m - 1) := by
  obtain ⟨ε₀, hε₀, hB⟩ := F.Q_black_edge
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle A hA
  obtain ⟨C2, hC2⟩ := hB ε hε hεle A hA
  obtain ⟨C1, -, hC1⟩ := F.Q_white_case1 (κ := ε ^ 3) (by positivity) A hA
  refine ⟨max (max C1 C2) 1, ?_⟩
  intro half T m hm hmn
  exact F.prop_7_8_of half T.W (by positivity) A hA C1 C2
    (fun m hm hmn l hw => hC1 half T.W m hm hmn l hw)
    (fun m hm hmn l h1 hnw => hC2 half T m hm hmn l h1 hnw) m hm hmn

/-- **(7.37)**: `Q(j,l) ≤ C max(half - j, 1)^{-A}` (`j ≥ 1`, with `C` independent of `half`, `T`, `l`). -/
theorem Q_polynomial_decay :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 < C ∧ ∀ (half : ℕ) (T : F.TriFam half (F.sep ε)) (j : ℕ) (l : ℤ), 1 ≤ j →
        F.Q half T.W (ε ^ 3) j l ≤ C * ((max (half - j) 1 : ℕ) : ℝ) ^ (-A) := by
  obtain ⟨ε₀, hε₀, h78⟩ := F.prop_7_8
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεle A hA
  obtain ⟨C0, hC0⟩ := h78 ε hε hεle A hA
  refine ⟨((max C0 1 : ℕ) : ℝ) ^ A, Real.rpow_pos_of_pos ?_ A, ?_⟩
  · have h1 : (1 : ℕ) ≤ max C0 1 := le_max_right _ _
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  · intro half T j l hj
    exact F.Q_polynomial_decay_of half T.W (by positivity) A hA C0
      (fun m hm hmn => hC0 half T m hm hmn) j l hj

end Family

end GGMCollatz
