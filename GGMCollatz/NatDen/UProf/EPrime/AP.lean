import Mathlib

/-!
# The number of elements of a residue class in a segment of an arithmetic progression (the per-class bound of Lemma 7.13 (iii) of the paper)

A finite set `S` that is "convex" within one residue class mod `P` (every number of the same class lying between two elements of `S`
belongs to `S`) is a segment `{a, a + P, …, a + (n-1)P}` of an arithmetic progression with difference `P`. If `P` and `Q` are coprime,
its residues mod `Q` run through all classes with period `Q`, so the number of terms in the class of `X` is `⌊n/Q⌋` or `⌊n/Q⌋ + 1`:
`|#{c ∈ S | c ≡ X (Q)} - #S/Q| ≤ 1`.
-/

namespace GGMCollatz

namespace ND

namespace EPrimeAux

/-- **The number of elements of a residue class in a segment of an arithmetic progression**. -/
theorem ap_count {P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) (hcop : Nat.Coprime P Q) (S : Finset ℕ)
    (hcong : ∀ a ∈ S, ∀ b ∈ S, a ≡ b [MOD P])
    (hconv : ∀ a ∈ S, ∀ b ∈ S, ∀ c : ℕ, a ≤ c → c ≤ b → c ≡ a [MOD P] → c ∈ S)
    (X : ZMod Q) :
    |((S.filter (fun c : ℕ => (c : ZMod Q) = X)).card : ℝ) - (S.card : ℝ) / Q| ≤ 1 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hne
  · subst hS; simp
  set a := S.min' hne with ha
  set b := S.max' hne with hb
  have haS : a ∈ S := S.min'_mem hne
  have hbS : b ∈ S := S.max'_mem hne
  set n := (b - a) / P + 1 with hn
  -- `S` is the segment `{a + iP | i < n}` of an arithmetic progression
  have hS_eq : S = (Finset.range n).image (fun i => a + i * P) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · intro hc
      have hac : a ≤ c := S.min'_le c hc
      have hcb : c ≤ b := S.le_max' c hc
      have hmod : a ≡ c [MOD P] := (hcong c hc a haS).symm
      obtain ⟨i, hi⟩ := (Nat.modEq_iff_dvd' hac).mp hmod
      refine ⟨i, ?_, ?_⟩
      · have h1 : i * P ≤ b - a := by rw [mul_comm, ← hi]; omega
        have h2 : i ≤ (b - a) / P := (Nat.le_div_iff_mul_le hP).mpr h1
        omega
      · rw [mul_comm] at hi
        omega
    · rintro ⟨i, hi, rfl⟩
      apply hconv a haS b hbS
      · omega
      · have h1 : i ≤ (b - a) / P := by omega
        have h2 : i * P ≤ (b - a) / P * P := Nat.mul_le_mul_right P h1
        have h3 : (b - a) / P * P ≤ b - a := Nat.div_mul_le_self _ _
        have h4 : a ≤ b := S.min'_le b hbS
        omega
      · show (a + i * P) % P = a % P
        exact Nat.add_mul_mod_self_right a i P
  have hinj : Function.Injective (fun i : ℕ => a + i * P) := by
    intro i j h
    simp only [add_right_inj] at h
    exact Nat.eq_of_mul_eq_mul_right hP h
  rw [hS_eq, Finset.filter_image, Finset.card_image_of_injective _ hinj,
    Finset.card_image_of_injective _ hinj, Finset.card_range]
  -- the condition `a + iP ≡ X (Q)` is `i ≡ v (Q)`
  have : NeZero Q := ⟨hQ.ne'⟩
  have hunit : IsUnit (P : ZMod Q) := (ZMod.isUnit_iff_coprime P Q).mpr hcop
  set u : ZMod Q := (P : ZMod Q)⁻¹ * (X - a) with hu
  have hfilt : (Finset.range n).filter (fun i => ((a + i * P : ℕ) : ZMod Q) = X)
      = (Finset.range n).filter (fun i => i ≡ u.val [MOD Q]) := by
    apply Finset.filter_congr
    intro i _
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    push_cast
    constructor
    · intro h
      rw [hu, ← h]
      calc (i : ZMod Q) = ((P : ZMod Q)⁻¹ * (P : ZMod Q)) * i := by
            rw [ZMod.inv_mul_of_unit _ hunit, one_mul]
        _ = (P : ZMod Q)⁻¹ * (a + i * P - a) := by ring
    · intro h
      rw [h, hu]
      calc (a : ZMod Q) + (P : ZMod Q)⁻¹ * (X - a) * P
          = a + ((P : ZMod Q) * (P : ZMod Q)⁻¹) * (X - a) := by ring
        _ = X := by rw [ZMod.mul_inv_of_unit _ hunit, one_mul]; ring
  rw [hfilt, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card n hQ]
  -- real-valued bound: `|⌊n/Q⌋ + [·] - n/Q| ≤ 1`
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hnQ : (n : ℝ) / Q = ((n / Q : ℕ) : ℝ) + ((n % Q : ℕ) : ℝ) / Q := by
    have h := Nat.div_add_mod n Q
    have h' : (n : ℝ) = (Q : ℝ) * ((n / Q : ℕ) : ℝ) + ((n % Q : ℕ) : ℝ) := by exact_mod_cast h.symm
    rw [h']
    field_simp
  have h1 : 0 ≤ ((n % Q : ℕ) : ℝ) / Q := by positivity
  have h2 : ((n % Q : ℕ) : ℝ) / Q < 1 := by
    rw [div_lt_one hQR]; exact_mod_cast Nat.mod_lt n hQ
  rw [hnQ, abs_le]
  split_ifs <;> push_cast <;> constructor <;> linarith

end EPrimeAux

end ND

end GGMCollatz
