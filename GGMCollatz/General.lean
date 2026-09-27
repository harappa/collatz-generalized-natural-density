import GGMCollatz.Main
import GGMCollatz.General.Chain

/-!
# Theorem 1.4 and Proposition 3.7 of the paper: the whole family without (d) and `q > p`

For the family `FamilyGen` given only by GGM's Definition 1.2 and (a)(b)(c) (frozen in
`GGMCollatz/StatementB.lean`):

* **`FamilyGen.mainA_gen`**: (A) (a power rate for the logarithmic density). No hypotheses. Uses `Family.mainA`
  (`Main.lean`).
* **`FamilyGen.mainB_gen_of`**: (B) (a power rate for the natural density). Takes (B) for the families satisfying
  (d) as a hypothesis `hB` ((B) itself is proved elsewhere). The hypothesis `MatveevHyp` depends only on `p` and
  `q`, so it does not change along the chain.

Outline of the proof: the case `q < p` is `Gen.mainA_of_q_lt`, `Gen.mainB_of_q_lt` (GGM §2.2); `q = p` is
incompatible with (a) (`Gen.q_ne_p`); `q > p` goes by `Gen.chain_induction` (the finite chain of Lemma 3.5 (iv) of the paper).
A family satisfying (d) is mapped to a `Family` by `Gen.toFamily`, and one link of the chain is
`Gen.transferA`, `Gen.transferB` (Lemma 3.6 of the paper; the exponent does not change).
-/

namespace GGMCollatz

namespace FamilyGen

/-- **(A) Theorem 1.4 of the paper (no hypotheses)**: for every family satisfying only (a)(b)(c), there are `K, c' > 0`
such that for all `N₀ ≥ 1` and `x ≥ 3`, `∑_{N ≤ x, C_min(N) > N₀} 1/N ≤ K N₀^{-c'} log x`. -/
theorem mainA_gen (G : FamilyGen) : G.mainA_gen_statement := by
  rcases lt_trichotomy G.q G.p with hlt | heq | hgt
  · exact Gen.mainA_of_q_lt G hlt
  · exact absurd heq (Gen.q_ne_p G)
  · exact Gen.chain_induction (fun G => G.mainA_gen_statement)
      (fun G hpq h1 => Gen.mainA_of_toFamily G hpq h1 (Family.mainA _))
      (fun _ _ hd h => Gen.transferA hd h) G hgt

/-- **(B) Proposition 3.7 (ii) of the paper (assuming (B) for the families satisfying (d))**: for a family satisfying only
(a)(b)(c), under the hypothesis of Matveev's estimate, `#{N ≤ X | C_min(N) > N₀} ≤ K X N₀^{-c}`. -/
theorem mainB_gen_of
    (hB : ∀ F : GGMCollatz.Family, GGMCollatz.MatveevHyp F.p F.q → F.mainB_statement)
    (G : GGMCollatz.FamilyGen) (hM : GGMCollatz.MatveevHyp G.p G.q) : G.mainB_gen_statement := by
  rcases lt_trichotomy G.q G.p with hlt | heq | hgt
  · exact Gen.mainB_of_q_lt G hlt
  · exact absurd heq (Gen.q_ne_p G)
  · exact Gen.chain_induction (fun G => MatveevHyp G.p G.q → G.mainB_gen_statement)
      (fun G hpq h1 hM' => Gen.mainB_of_toFamily G hpq h1 (hB _ hM'))
      (fun _ _ hd h hM' => Gen.transferB hd (h hM')) G hgt hM

end FamilyGen

end GGMCollatz
