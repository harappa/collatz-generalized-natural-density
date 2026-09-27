import GGMCollatz.General.Rate

/-!
# Removing (d), reduction 5: case distinction and the chain (Proposition 3.7 of the paper)

* `q_ne_p`: `q = p` is incompatible with (a).
* `Cmin_le_bigR_of_q_lt`: if `q < p`, then `C_min(N) ≤ R` for every `N` (GGM §2.2; if `p ∤ N` and `N > R`, then
  `C²(N) = C(N)/p ≤ (qN + R)/p < N`; if `p ∣ N`, then `C(N) = N/p < N`; strong induction).
  A slightly stronger form than `C_min(N) ≤ pA` in the accompanying paper (`A = R`).
* `mainA_of_q_lt`, `mainB_of_q_lt`: for `q < p` the exceptional set is empty for `N₀ ≥ R`, and small `N₀` are
  absorbed into the constant.
* `GcdOne`, `toFamily`: build a `Family` from a `FamilyGen` satisfying (d) and `p < q`. `C` and `C_min` agree by
  definition.
* `exists_commonDiv`: if (d) fails, there is a common divisor `d ≥ 2`.
* **`chain_induction`**: a property `P` of families with `p < q` holds for all such families if it holds for the
  families satisfying (d) and can be pulled back along `reduce` (induction on `R`; `R* < R`, `R ≥ 1`).
  Lemma 3.5 (iv) of the paper.
-/

namespace GGMCollatz

namespace Gen

open Finset

variable (G : FamilyGen)

/-- `q = p` is incompatible with (a). -/
lemma q_ne_p : G.q ≠ G.p := by
  intro h
  have hc := G.coprime
  rw [h, Nat.coprime_self] at hc
  have := G.two_le_p
  omega

/-- If `p ∤ N`, then `C(N) ≤ qN + R` (in ℤ). -/
lemma C_cast_le {N : ℕ} (h : N % G.p ≠ 0) : (G.C N : ℤ) ≤ G.q * N + bigR G := by
  rw [C_cast G h]
  have h1 : G.r (N % G.p) ≤ ((G.r (N % G.p)).natAbs : ℤ) := Int.le_natAbs
  have h2 : ((G.r (N % G.p)).natAbs : ℤ) ≤ bigR G := by
    exact_mod_cast natAbs_le_bigR G (mod_pos G h) (mod_lt_p G N)
  linarith

/-- **The case `q < p`** (GGM §2.2): `C_min(N) ≤ R` for every `N`. -/
lemma Cmin_le_bigR_of_q_lt (hqp : G.q < G.p) (N : ℕ) : G.Cmin N ≤ bigR G := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hNR : N ≤ bigR G
    · exact le_trans (Cmin_le_self G N) hNR
    · push Not at hNR
      by_cases hN : N % G.p = 0
      · have hlt : G.C N < N := by
          rw [C_of_mod_eq_zero G hN]; exact Nat.div_lt_self (by omega) (one_lt_p G)
        calc G.Cmin N ≤ G.Cmin (G.C^[1] N) := Cmin_le_Cmin_iterate G N 1
          _ ≤ bigR G := ih _ hlt
      · have hCC : G.C (G.C N) = G.C N / G.p := C_of_mod_eq_zero G (mod_C G hN)
        have hle := C_cast_le G hN
        have hlt : G.C N / G.p < N := by
          rw [Nat.div_lt_iff_lt_mul (p_pos G)]
          have hq : (G.q : ℤ) + 1 ≤ G.p := by exact_mod_cast hqp
          have hNR' : (bigR G : ℤ) < N := by exact_mod_cast hNR
          have hN0 : (0 : ℤ) ≤ N := by positivity
          have : (G.C N : ℤ) < N * G.p := by nlinarith
          exact_mod_cast this
        calc G.Cmin N ≤ G.Cmin (G.C^[2] N) := Cmin_le_Cmin_iterate G N 2
          _ = G.Cmin (G.C N / G.p) := by
              rw [show G.C^[2] N = G.C (G.C N) from rfl, hCC]
          _ ≤ bigR G := ih _ hlt

/-- **(A) for `q < p`**. -/
theorem mainA_of_q_lt (hqp : G.q < G.p) : G.mainA_gen_statement := by
  apply mainA_of_large G (bigR G) (K := 1) (c := 1) one_pos one_pos
  intro N₀ _ hN x hx
  have hempty : (Finset.Icc 1 ⌊x⌋₊).filter (fun N => N₀ < G.Cmin N) = ∅ := by
    apply Finset.filter_false_of_mem
    intro N _ hlt
    have := Cmin_le_bigR_of_q_lt G hqp N
    omega
  rw [hempty, Finset.sum_empty]
  exact mul_nonneg (mul_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (by linarith [one_le_log hx])

/-- **(B) for `q < p`**. -/
theorem mainB_of_q_lt (hqp : G.q < G.p) : G.mainB_gen_statement := by
  apply mainB_of_large G (bigR G) (K := 1) (c := 1) one_pos one_pos
  intro N₀ _ hN X hX
  have hempty : (Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < G.Cmin N) = ∅ := by
    apply Finset.filter_false_of_mem
    intro N _ hlt
    have := Cmin_le_bigR_of_q_lt G hqp N
    omega
  rw [hempty, Finset.card_empty, Nat.cast_zero]
  exact mul_nonneg (mul_nonneg zero_le_one (by linarith)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-! ### The map to families satisfying (d) -/

/-- (d): `gcd(q, r(1), …, r(p-1)) = 1` (the same form as `Family.gcd_one`). -/
def GcdOne : Prop :=
  ∀ d : ℕ, d ∣ G.q → (∀ j : ℕ, 0 < j → j < G.p → (d : ℤ) ∣ G.r j) → d = 1

/-- Build a `Family` from a `FamilyGen` satisfying (d) and `p < q` (the data are the same). -/
def toFamily (hpq : G.p < G.q) (h1 : GcdOne G) : Family where
  p := G.p
  q := G.q
  r := G.r
  two_le_p := G.two_le_p
  p_lt_q := hpq
  coprime := G.coprime
  subcritical := G.subcritical
  divisible := G.divisible
  positive := G.positive
  gcd_one := h1

/-- `Family.C` and `FamilyGen.C` are the same formula. -/
lemma toFamily_C (hpq : G.p < G.q) (h1 : GcdOne G) : (toFamily G hpq h1).C = G.C := rfl

/-- Hence `C_min` also agrees. -/
lemma toFamily_Cmin (hpq : G.p < G.q) (h1 : GcdOne G) : (toFamily G hpq h1).Cmin = G.Cmin := by
  funext N
  simp only [Family.Cmin, FamilyGen.Cmin, toFamily_C]

lemma mainA_of_toFamily (hpq : G.p < G.q) (h1 : GcdOne G)
    (h : (toFamily G hpq h1).mainA_statement) : G.mainA_gen_statement := by
  unfold Family.mainA_statement at h
  rw [toFamily_Cmin] at h
  exact h

lemma mainB_of_toFamily (hpq : G.p < G.q) (h1 : GcdOne G)
    (h : (toFamily G hpq h1).mainB_statement) : G.mainB_gen_statement := by
  unfold Family.mainB_statement at h
  rw [toFamily_Cmin] at h
  exact h

variable {G}

/-- If (d) fails, there is a common divisor `d ≥ 2`. -/
lemma exists_commonDiv (h : ¬ GcdOne G) : ∃ d, CommonDiv G d := by
  unfold GcdOne at h
  push Not at h
  obtain ⟨d, hdq, hdr, hd1⟩ := h
  have hd0 : d ≠ 0 := by
    rintro rfl
    have := Nat.eq_zero_of_zero_dvd hdq
    have := G.two_le_q
    omega
  exact ⟨d, ⟨by omega, hdq, hdr⟩⟩

/-- **Induction along the chain** (Lemma 3.5 (iv) of the paper): if a property `P` of families with `p < q` holds for the
families satisfying (d) and can be pulled back along `reduce`, then it holds for every family with `p < q`. -/
theorem chain_induction (P : FamilyGen → Prop)
    (hbase : ∀ G : FamilyGen, G.p < G.q → GcdOne G → P G)
    (hstep : ∀ (G : FamilyGen) (d : ℕ) (hd : CommonDiv G d), P (reduce G d hd) → P G) :
    ∀ G : FamilyGen, G.p < G.q → P G := by
  suffices H : ∀ n : ℕ, ∀ G : FamilyGen, bigR G ≤ n → G.p < G.q → P G from
    fun G hpq => H _ G le_rfl hpq
  intro n
  induction n with
  | zero =>
    intro G hR _
    have := one_le_bigR G
    omega
  | succ n ih =>
    intro G hR hpq
    by_cases h1 : GcdOne G
    · exact hbase G hpq h1
    · obtain ⟨d, hd⟩ := exists_commonDiv h1
      apply hstep G d hd
      apply ih
      · have := bigR_reduce_lt hd
        omega
      · exact hpq

end Gen

end GGMCollatz
