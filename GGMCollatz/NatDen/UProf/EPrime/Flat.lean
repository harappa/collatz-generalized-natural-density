import GGMCollatz.NatDen.UProf.EPrime.Count
import GGMCollatz.NatDen.UProf.EPrime.AP

/-!
# Flatness on residue classes (Lemma 7.13 (iii) of the paper)

Splitting `E' ∩ (A, B]` by keys, each class is convex (`convex`) within a residue class mod `p^{|b|+1}`, hence a segment of an
arithmetic progression; since `p^{|b|+1}` and `q^k` are coprime ((a)), `ap_count` gives a difference of at most 1 per class.
The total is at most `Π_x`.
(The accompanying paper's (iii) allows at most 2 per class, but counting along a segment of an arithmetic progression gives at most 1.)
-/

namespace GGMCollatz

namespace ND

namespace EPrimeAux

open Family

variable (F : Family)

/-- Flatness on the part `(A, B]` of one class (apply `ap_count`). -/
theorem flat_class (α x : ℝ) (k : ℕ) (X : ZMod (F.q ^ k)) (A B : ℝ)
    (κ : (Fin (F.mZero α x) → ℕ) × (Fin (F.mZero α x + 1) → ℕ)) :
    |(((((F.Eprime α x Set.univ).filter (fun M : ℕ => A < (M : ℝ) ∧ (M : ℝ) ≤ B)).filter
          (fun M => key F (F.mZero α x) M = κ)).filter
            (fun M : ℕ => (M : ZMod (F.q ^ k)) = X)).card : ℝ)
      - ((((F.Eprime α x Set.univ).filter (fun M : ℕ => A < (M : ℝ) ∧ (M : ℝ) ≤ B)).filter
          (fun M => key F (F.mZero α x) M = κ)).card : ℝ) / ((F.q ^ k : ℕ) : ℝ)| ≤ 1 := by
  set T := ((F.Eprime α x Set.univ).filter (fun M : ℕ => A < (M : ℝ) ∧ (M : ℝ) ≤ B)).filter
    (fun M => key F (F.mZero α x) M = κ) with hT
  have hmemT : ∀ M ∈ T, M ∈ F.Eprime α x Set.univ ∧ (A < (M : ℝ) ∧ (M : ℝ) ≤ B) ∧
      key F (F.mZero α x) M = κ := by
    intro M hM
    simp only [hT, Finset.mem_filter] at hM
    exact ⟨hM.1.1, hM.1.2, hM.2⟩
  have hP : 0 < F.p ^ (pre κ.1 (F.mZero α x) + 1) := pow_pos F.p_pos _
  have hQ : 0 < F.q ^ k := pow_pos F.q_pos _
  have hcop : Nat.Coprime (F.p ^ (pre κ.1 (F.mZero α x) + 1)) (F.q ^ k) :=
    Nat.Coprime.pow _ _ F.coprime
  apply ap_count hP hQ hcop T
  · intro a ha b hb
    obtain ⟨haE, -, hka⟩ := hmemT a ha
    obtain ⟨hbE, -, hkb⟩ := hmemT b hb
    have hpa := ((mem_Eprime_univ F).mp haE).1
    have hpb := ((mem_Eprime_univ F).mp hbE).1
    have h := modEq_of_key_eq F hpa hpb (hka.trans hkb.symm)
    rw [hka] at h
    exact h
  · intro a ha b hb c hac hcb hmod
    obtain ⟨haE, ⟨hAa, -⟩, hka⟩ := hmemT a ha
    obtain ⟨hbE, ⟨-, hbB⟩, hkb⟩ := hmemT b hb
    have hmod' : c ≡ a [MOD F.p ^ (pre (key F (F.mZero α x) a).1 (F.mZero α x) + 1)] := by
      rw [hka]; exact hmod
    obtain ⟨hcE, hkc⟩ := convex F haE hbE (hka.trans hkb.symm) hac hcb hmod'
    simp only [hT, Finset.mem_filter]
    have hac' : (a : ℝ) ≤ c := by exact_mod_cast hac
    have hcb' : (c : ℝ) ≤ b := by exact_mod_cast hcb
    exact ⟨⟨hcE, by linarith, by linarith⟩, hkc.trans hka⟩

/-- **Deterministic form of (EP2)**: the difference is at most the number of keys. -/
theorem flat_le_card_keys (α x : ℝ) (k : ℕ) (X : ZMod (F.q ^ k)) (A B : ℝ) :
    |(((F.Eprime α x Set.univ).filter (fun M : ℕ =>
          A < (M : ℝ) ∧ (M : ℝ) ≤ B ∧ ((M : ℕ) : ZMod (F.q ^ k)) = X)).card : ℝ)
      - (F.q : ℝ) ^ (-(k : ℤ)) *
        (((F.Eprime α x Set.univ).filter (fun M : ℕ => A < (M : ℝ) ∧ (M : ℝ) ≤ B)).card : ℝ)|
      ≤ ((keys F α x).card : ℝ) := by
  set T := (F.Eprime α x Set.univ).filter (fun M : ℕ => A < (M : ℝ) ∧ (M : ℝ) ≤ B) with hT
  set T3 := (F.Eprime α x Set.univ).filter (fun M : ℕ =>
    A < (M : ℝ) ∧ (M : ℝ) ≤ B ∧ ((M : ℕ) : ZMod (F.q ^ k)) = X) with hT3
  have hmaps : Set.MapsTo (key F (F.mZero α x)) (T : Set ℕ) (keys F α x : Set _) := by
    intro M hM
    have hM' : M ∈ T := Finset.mem_coe.mp hM
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_filter.mp hM').1)
  have hmaps3 : Set.MapsTo (key F (F.mZero α x)) (T3 : Set ℕ) (keys F α x : Set _) := by
    intro M hM
    have hM' : M ∈ T3 := Finset.mem_coe.mp hM
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_filter.mp hM').1)
  have e3 : T3.card = ∑ κ ∈ keys F α x,
      ((T.filter (fun M => key F (F.mZero α x) M = κ)).filter
        (fun M : ℕ => (M : ZMod (F.q ^ k)) = X)).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps3]
    apply Finset.sum_congr rfl
    intro κ _
    congr 1
    ext M
    simp only [hT, hT3, Finset.mem_filter]
    tauto
  have e1 : T.card = ∑ κ ∈ keys F α x, (T.filter (fun M => key F (F.mZero α x) M = κ)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hqk : (F.q : ℝ) ^ (-(k : ℤ)) = (((F.q ^ k : ℕ) : ℝ))⁻¹ := by
    rw [zpow_neg, zpow_natCast]; push_cast; rfl
  rw [e3, e1, hqk]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ κ ∈ keys F α x, (((((T.filter (fun M => key F (F.mZero α x) M = κ)).filter
          (fun M : ℕ => (M : ZMod (F.q ^ k)) = X)).card : ℕ) : ℝ)
        - ((F.q : ℝ) ^ k)⁻¹ * (((T.filter (fun M => key F (F.mZero α x) M = κ)).card : ℕ) : ℝ))|
      ≤ ∑ κ ∈ keys F α x, |(((((T.filter (fun M => key F (F.mZero α x) M = κ)).filter
          (fun M : ℕ => (M : ZMod (F.q ^ k)) = X)).card : ℕ) : ℝ)
        - ((F.q : ℝ) ^ k)⁻¹ * (((T.filter (fun M => key F (F.mZero α x) M = κ)).card : ℕ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _κ ∈ keys F α x, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro κ _
        have h := flat_class F α x k X A B κ
        rw [← hT] at h
        push_cast at h
        rw [div_eq_inv_mul] at h
        exact h
    _ = ((keys F α x).card : ℝ) := by simp

end EPrimeAux

end ND

end GGMCollatz
