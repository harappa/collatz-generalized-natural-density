import GGMCollatz.StatementB

/-!
# Removing (d), reduction 1: basic properties of the general family, and conjugation (Lemmas 3.2 and 3.5 of the paper)

For `FamilyGen` (the family given only by GGM's Definition 1.2 and (a)(b)(c)):

* `C_cast`: if `p ∤ N`, then `C(N) = qN + r(N mod p)` (in ℤ); `one_le_C`: in that case `C(N) ≥ 1`.
* `mod_C`: if `p ∤ N`, then `p ∣ C(N)` (from (c)). `C_le`: `C(N) ≤ (q + R)N` (`R = max_{0<j<p} |r(j)|`).
* `Cmin_le_iterate`, `Cmin_le_Cmin_iterate`, `Cmin_pow_mul_le`: monotonicity of the orbit minimum.
* `reduce`: the family `r*(i) = r(d i mod p)/d` obtained by dividing by a common divisor `d ≥ 2` (`d ∣ q`,
  `d ∣ r(j)`) (Lemma 3.5 (i) of the paper). `C_mul`: `C(dN) = d C*(N)`; `Cmin_le_mul_Cmin`: if `p ∤ N`, then
  `C_min(N) ≤ d C*_min(C(N)/d)` (Lemma 3.5 (iii) of the paper).
  `bigR_reduce_lt`: `R* < R` (the finiteness in Lemma 3.5 (iv) of the paper).

The accompanying paper divides by `h = gcd(q, r(1), …, r(p-1))`; here we divide by an arbitrary common divisor
`d ≠ 1` (the argument is the same, and `gcd` need not be computed).
-/

namespace GGMCollatz

namespace Gen

variable (G : FamilyGen)

lemma one_lt_p : 1 < G.p := G.two_le_p

lemma p_pos : 0 < G.p := by have := G.two_le_p; omega

lemma q_pos : 0 < G.q := by have := G.two_le_q; omega

/-- `R = max_{0 < j < p} |r(j)|`. -/
def bigR : ℕ := (Finset.Ioo 0 G.p).sup fun j => (G.r j).natAbs

lemma natAbs_le_bigR {j : ℕ} (hj0 : 0 < j) (hjp : j < G.p) : (G.r j).natAbs ≤ bigR G :=
  Finset.le_sup (f := fun j => (G.r j).natAbs) (Finset.mem_Ioo.mpr ⟨hj0, hjp⟩)

lemma mod_pos {N : ℕ} (h : N % G.p ≠ 0) : 0 < N % G.p := Nat.pos_of_ne_zero h

lemma mod_lt_p (N : ℕ) : N % G.p < G.p := Nat.mod_lt _ (p_pos G)

/-- `r(j) ≠ 0` (from (a)(c)). -/
lemma r_ne_zero {j : ℕ} (hj0 : 0 < j) (hjp : j < G.p) : G.r j ≠ 0 := by
  intro h0
  have hdiv := G.divisible j hj0 hjp
  rw [h0, add_zero] at hdiv
  -- `p ∣ j` from `p ∣ q j` and `gcd(p, q) = 1`
  have h1 : G.p ∣ G.q * j := by exact_mod_cast hdiv
  have h2 : G.p ∣ j := G.coprime.dvd_of_dvd_mul_left h1
  have := Nat.le_of_dvd hj0 h2
  omega

lemma one_le_bigR : 1 ≤ bigR G := by
  have h := natAbs_le_bigR G (j := 1) (by norm_num) (one_lt_p G)
  have h1 : (G.r 1).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]; exact r_ne_zero G (by norm_num) (one_lt_p G)
  omega

lemma C_of_mod_eq_zero {N : ℕ} (h : N % G.p = 0) : G.C N = N / G.p := by
  simp [FamilyGen.C, h]

/-- Positivity of the value of a multiplication step: if `p ∤ N`, then `qN + r(N mod p) ≥ 1`. -/
lemma one_le_step {N : ℕ} (h : N % G.p ≠ 0) :
    1 ≤ (G.q : ℤ) * N + G.r (N % G.p) := by
  have h1 := G.positive _ (mod_pos G h) (mod_lt_p G N)
  have h2 : ((N % G.p : ℕ) : ℤ) ≤ N := by exact_mod_cast Nat.mod_le N G.p
  have hq : (0 : ℤ) ≤ G.q := by positivity
  nlinarith

lemma C_cast {N : ℕ} (h : N % G.p ≠ 0) : (G.C N : ℤ) = G.q * N + G.r (N % G.p) := by
  simp only [FamilyGen.C, if_neg h]
  exact Int.toNat_of_nonneg (by linarith [one_le_step G h])

lemma one_le_C {N : ℕ} (h : N % G.p ≠ 0) : 1 ≤ G.C N := by
  have := C_cast G h
  have := one_le_step G h
  omega

/-- If `p ∤ N`, then `p ∣ C(N)` ((c)). -/
lemma mod_C {N : ℕ} (h : N % G.p ≠ 0) : G.C N % G.p = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  have hdiv := G.divisible _ (mod_pos G h) (mod_lt_p G N)
  have hmod : ((N % G.p : ℕ) : ℤ) + (G.p : ℤ) * ((N / G.p : ℕ) : ℤ) = N := by
    exact_mod_cast Nat.mod_add_div N G.p
  have e : (G.C N : ℤ) = ((G.q : ℤ) * ((N % G.p : ℕ) : ℤ) + G.r (N % G.p)) +
      G.p * (G.q * ((N / G.p : ℕ) : ℤ)) := by
    rw [C_cast G h]
    linear_combination (G.q : ℤ) * hmod.symm
  have : (G.p : ℤ) ∣ (G.C N : ℤ) := by
    rw [e]; exact dvd_add hdiv (dvd_mul_right _ _)
  exact_mod_cast this

/-- If `p ∤ N` and `N ≥ 1`, then `C(N) ≤ (q + R) N`. -/
lemma C_le {N : ℕ} (h : N % G.p ≠ 0) (hN : 1 ≤ N) : G.C N ≤ (G.q + bigR G) * N := by
  have e := C_cast G h
  have h1 : G.r (N % G.p) ≤ ((G.r (N % G.p)).natAbs : ℤ) := Int.le_natAbs
  have h2 : ((G.r (N % G.p)).natAbs : ℤ) ≤ bigR G := by
    exact_mod_cast natAbs_le_bigR G (mod_pos G h) (mod_lt_p G N)
  have h3 : (bigR G : ℤ) ≤ bigR G * N := by
    have : (1 : ℤ) ≤ N := by exact_mod_cast hN
    nlinarith [(by positivity : (0 : ℤ) ≤ bigR G)]
  have : (G.C N : ℤ) ≤ ((G.q + bigR G) * N : ℕ) := by push_cast; linarith
  exact_mod_cast this

/-- Injectivity of the multiplication step: if `N₁ ≡ N₂ (mod p)`, `p ∤ N₁` and `C(N₁) = C(N₂)`, then
`N₁ = N₂`. -/
lemma C_inj_of_mod_eq {N₁ N₂ : ℕ} (h1 : N₁ % G.p ≠ 0) (hmod : N₁ % G.p = N₂ % G.p)
    (hC : G.C N₁ = G.C N₂) : N₁ = N₂ := by
  have h2 : N₂ % G.p ≠ 0 := hmod ▸ h1
  have e1 := C_cast G h1
  have e2 := C_cast G h2
  rw [hC, e2, hmod] at e1
  have hq : (G.q : ℤ) ≠ 0 := by have := q_pos G; positivity
  have : (N₂ : ℤ) = N₁ := by
    have := e1
    have h' : (G.q : ℤ) * N₂ = G.q * N₁ := by linarith
    exact mul_left_cancel₀ hq h'
  exact_mod_cast this.symm

lemma C_p_mul (N : ℕ) : G.C (G.p * N) = N := by
  rw [C_of_mod_eq_zero G (Nat.mul_mod_right _ _), Nat.mul_div_cancel_left _ (p_pos G)]

lemma iterate_C_pow_mul (k N : ℕ) : G.C^[k] (G.p ^ k * N) = N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, pow_succ', mul_assoc, C_p_mul, ih]

/-! ### The orbit minimum -/

lemma Cmin_le_iterate (N k : ℕ) : G.Cmin N ≤ G.C^[k] N := Nat.sInf_le ⟨k, rfl⟩

lemma Cmin_le_self (N : ℕ) : G.Cmin N ≤ N := Cmin_le_iterate G N 0

lemma exists_Cmin_eq (N : ℕ) : ∃ k, G.C^[k] N = G.Cmin N :=
  Nat.sInf_mem (Set.range_nonempty fun k => G.C^[k] N)

lemma Cmin_le_Cmin_iterate (N k : ℕ) : G.Cmin N ≤ G.Cmin (G.C^[k] N) := by
  obtain ⟨j, hj⟩ := exists_Cmin_eq G (G.C^[k] N)
  rw [← hj, ← Function.iterate_add_apply]
  exact Cmin_le_iterate G N _

/-- `C_min(p^k N) ≤ C_min(N)` (the second half of Lemma 3.2 (iv) of the paper). -/
lemma Cmin_pow_mul_le (k N : ℕ) : G.Cmin (G.p ^ k * N) ≤ G.Cmin N := by
  have := Cmin_le_Cmin_iterate G (G.p ^ k * N) k
  rwa [iterate_C_pow_mul] at this

/-! ### Conjugation by a common divisor (Lemma 3.5 (i)(ii) of the paper) -/

/-- `d` is a common divisor `≠ 1` of `q` and `r(1), …, r(p-1)`. -/
structure CommonDiv (d : ℕ) : Prop where
  two_le : 2 ≤ d
  dvd_q : d ∣ G.q
  dvd_r : ∀ j : ℕ, 0 < j → j < G.p → (d : ℤ) ∣ G.r j

variable {G}

lemma CommonDiv.pos {d : ℕ} (hd : CommonDiv G d) : 0 < d := by have := hd.two_le; omega

lemma CommonDiv.coprime {d : ℕ} (hd : CommonDiv G d) : Nat.Coprime G.p d :=
  Nat.Coprime.coprime_dvd_right hd.dvd_q G.coprime

lemma CommonDiv.mul_mod_ne_zero {d : ℕ} (hd : CommonDiv G d) {i : ℕ} (hi : i % G.p ≠ 0) :
    d * i % G.p ≠ 0 := by
  intro h0
  have h1 : G.p ∣ d * i := Nat.dvd_of_mod_eq_zero h0
  exact hi (Nat.mod_eq_zero_of_dvd (hd.coprime.dvd_of_dvd_mul_left h1))

lemma CommonDiv.mul_div_r {d : ℕ} (hd : CommonDiv G d) {i : ℕ} (hi : i % G.p ≠ 0) :
    (d : ℤ) * (G.r (d * i % G.p) / d) = G.r (d * i % G.p) :=
  Int.mul_ediv_cancel' (hd.dvd_r _ (mod_pos G (hd.mul_mod_ne_zero hi)) (mod_lt_p G _))

/-- The family `r*(i) = r(d i mod p)/d` obtained by dividing by the common divisor `d` (Lemma 3.5 (i) of the paper). -/
def reduce (G : FamilyGen) (d : ℕ) (hd : CommonDiv G d) : FamilyGen where
  p := G.p
  q := G.q
  r := fun i => G.r (d * i % G.p) / d
  two_le_p := G.two_le_p
  two_le_q := G.two_le_q
  coprime := G.coprime
  subcritical := G.subcritical
  divisible := by
    intro i hi hip
    have hi' : i % G.p ≠ 0 := by rw [Nat.mod_eq_of_lt hip]; omega
    have hj0 := hd.mul_mod_ne_zero hi'
    have hdr := hd.mul_div_r hi'
    have hdiv := G.divisible _ (mod_pos G hj0) (mod_lt_p G _)
    have hmod : ((d * i % G.p : ℕ) : ℤ) + (G.p : ℤ) * ((d * i / G.p : ℕ) : ℤ) = (d : ℤ) * i := by
      exact_mod_cast Nat.mod_add_div (d * i) G.p
    have key : (G.p : ℤ) ∣ (d : ℤ) * ((G.q : ℤ) * i + G.r (d * i % G.p) / d) := by
      have e : (d : ℤ) * ((G.q : ℤ) * i + G.r (d * i % G.p) / d) =
          ((G.q : ℤ) * ((d * i % G.p : ℕ) : ℤ) + G.r (d * i % G.p)) +
            G.p * (G.q * ((d * i / G.p : ℕ) : ℤ)) := by
        rw [mul_add, hdr]
        linear_combination (G.q : ℤ) * hmod.symm
      rw [e]
      exact dvd_add hdiv (dvd_mul_right _ _)
    exact (Nat.isCoprime_iff_coprime.mpr hd.coprime).dvd_of_dvd_mul_left key
  positive := by
    intro i hi hip
    have hi' : i % G.p ≠ 0 := by rw [Nat.mod_eq_of_lt hip]; omega
    have hj0 := hd.mul_mod_ne_zero hi'
    have hdr := hd.mul_div_r hi'
    have hpos := G.positive _ (mod_pos G hj0) (mod_lt_p G _)
    have hle : ((d * i % G.p : ℕ) : ℤ) ≤ (d : ℤ) * i := by exact_mod_cast Nat.mod_le (d * i) G.p
    have e : (d : ℤ) * ((G.q : ℤ) * i + G.r (d * i % G.p) / d) =
        (G.q : ℤ) * ((d : ℤ) * i) + G.r (d * i % G.p) := by
      rw [mul_add, hdr]; ring
    have hq : (0 : ℤ) ≤ G.q := by positivity
    have h1 : 1 ≤ (d : ℤ) * ((G.q : ℤ) * i + G.r (d * i % G.p) / d) := by
      rw [e]; nlinarith
    have hd0 : (0 : ℤ) < d := by exact_mod_cast hd.pos
    by_contra hneg
    push Not at hneg
    have : (G.q : ℤ) * i + G.r (d * i % G.p) / d ≤ 0 := by omega
    nlinarith

variable {d : ℕ} (hd : CommonDiv G d)

@[simp] lemma reduce_p : (reduce G d hd).p = G.p := rfl

@[simp] lemma reduce_q : (reduce G d hd).q = G.q := rfl

lemma reduce_r (i : ℕ) : (reduce G d hd).r i = G.r (d * i % G.p) / d := rfl

/-- **Conjugation**: `C(dN) = d C*(N)` (Lemma 3.5 (ii) of the paper). -/
lemma C_mul (N : ℕ) : G.C (d * N) = d * (reduce G d hd).C N := by
  by_cases hN : N % G.p = 0
  · have h1 : d * N % G.p = 0 := by rw [Nat.mul_mod, hN, mul_zero, Nat.zero_mod]
    have h2 : (reduce G d hd).C N = N / G.p := C_of_mod_eq_zero (reduce G d hd) hN
    rw [C_of_mod_eq_zero G h1, h2]
    exact Nat.mul_div_assoc d (Nat.dvd_of_mod_eq_zero hN)
  · have h1 : d * N % G.p ≠ 0 := hd.mul_mod_ne_zero hN
    have hN' : N % (reduce G d hd).p ≠ 0 := hN
    have e1 := C_cast G h1
    have e2 := C_cast (reduce G d hd) hN'
    have hdr := hd.mul_div_r hN
    rw [reduce_r, reduce_q, reduce_p, Nat.mul_mod_mod] at e2
    have : (G.C (d * N) : ℤ) = ((d * (reduce G d hd).C N : ℕ) : ℤ) := by
      push_cast
      rw [e1, e2, mul_add, hdr]
      push_cast; ring
    exact_mod_cast this

lemma iterate_C_mul (k N : ℕ) : G.C^[k] (d * N) = d * (reduce G d hd).C^[k] N := by
  induction k generalizing N with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, C_mul hd, ih]

include hd in
/-- If `p ∤ N`, then `d ∣ C(N)`. -/
lemma dvd_C {N : ℕ} (hN : N % G.p ≠ 0) : d ∣ G.C N := by
  have : (d : ℤ) ∣ (G.C N : ℤ) := by
    rw [C_cast G hN]
    exact dvd_add (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hd.dvd_q) _)
      (hd.dvd_r _ (mod_pos G hN) (mod_lt_p G N))
  exact_mod_cast this

/-- **Lemma 3.5 (iii) of the paper**: if `p ∤ N`, then `C_min(N) ≤ d C*_min(C(N)/d)`. -/
lemma Cmin_le_mul_Cmin {N : ℕ} (hN : N % G.p ≠ 0) :
    G.Cmin N ≤ d * (reduce G d hd).Cmin (G.C N / d) := by
  obtain ⟨k, hk⟩ := exists_Cmin_eq (reduce G d hd) (G.C N / d)
  have e : G.C N = d * (G.C N / d) := (Nat.mul_div_cancel' (dvd_C hd hN)).symm
  calc G.Cmin N ≤ G.C^[k + 1] N := Cmin_le_iterate G N _
    _ = G.C^[k] (G.C N) := Function.iterate_succ_apply _ _ _
    _ = G.C^[k] (d * (G.C N / d)) := by rw [← e]
    _ = d * (reduce G d hd).C^[k] (G.C N / d) := iterate_C_mul hd _ _
    _ = d * (reduce G d hd).Cmin (G.C N / d) := by rw [hk]

/-- **The finiteness in Lemma 3.5 (iv) of the paper**: `R* ≤ R/d < R`. -/
lemma bigR_reduce_le : bigR (reduce G d hd) ≤ bigR G / d := by
  apply Finset.sup_le
  intro i hi
  rw [Finset.mem_Ioo] at hi
  have hip : i < G.p := hi.2
  have hi' : i % G.p ≠ 0 := by rw [Nat.mod_eq_of_lt hip]; omega
  have hj0 := hd.mul_mod_ne_zero hi'
  have hdr := hd.mul_div_r hi'
  have h1 := natAbs_le_bigR G (mod_pos G hj0) (mod_lt_p G (d * i))
  rw [Nat.le_div_iff_mul_le hd.pos]
  show (G.r (d * i % G.p) / d).natAbs * d ≤ bigR G
  have : (G.r (d * i % G.p) / d).natAbs * d = (G.r (d * i % G.p)).natAbs := by
    conv_rhs => rw [← hdr]
    rw [Int.natAbs_mul, Int.natAbs_natCast, mul_comm]
  rw [this]; exact h1

lemma bigR_reduce_lt : bigR (reduce G d hd) < bigR G :=
  lt_of_le_of_lt (bigR_reduce_le hd) (Nat.div_lt_self (one_le_bigR G) hd.two_le)

end Gen

end GGMCollatz
