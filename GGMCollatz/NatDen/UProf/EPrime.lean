import GGMCollatz.NatDen.UProf.Statements
import GGMCollatz.NatDen.UProf.EPrime.Asymp
import GGMCollatz.NatDen.UProf.EPrime.Flat

/-!
# (EP1)(EP2) The structure of `E'` (Lemma 7.13 of the paper)

The `M ∈ ℕ_p` sharing a prefix `(b, R') = (a^{(m₀)}(M), R^{(m₀+1)}(M))` form one residue class mod `p^{|b|+1}` (GGM Lemma 3.3,
`valDig_eq_iff_residue` in `Tao/Basic/Valuation.lean`), and on it `S^j(M)` is an increasing function of `M`, so the condition of `E'`
cuts out an interval. The number `Π_x` of nonempty prefixes is at most `2^K (p-1)^{m₀+1} · 3 log_p x` (`K = μ m₀ + L^{0.7}/log p + 1`),
and `≤ x^{1/2}/2` if `α` is close to 1.
(EP1): on each class `Σ 1/M ≤ 1/max(L_b, Mlo) + Q_b^{-1} log(U_b/L_b)` (`Q_b = p^{|b|+1} q^k`, `U_b/L_b ≤ 4 p^{b_{m₀}}`),
and `Σ_{b, R'} p^{-|b|-1}(b_{m₀} log p + log 4) = ((p-1)/p) E[G log p + log 4]`.
(EP2): on each class the difference is at most 2.

The Lean form (`NatDen/UProf/EPrime/`):
* `Class.lean`: the key `key m M = (a^{(m)}(M), dig^{(m+1)}(M))`, keys and residue classes (Lemmas 3.2, 3.3), monotonicity and
  convexity within a class (`convex`, the form of "the intersection of a class with an interval"), size bounds. The bundle of conditions `Good`.
* `Box.lean`: bound the sum over the box of keys by the product of coordinatewise sums (`box_sum`; the count of `Π_x` and the main term of `C_k`).
  In Lean we count in the form `Π_x ≤ W (p-1)^2 Bmax` (`W = 2q^{m₀-1}Mhi/x ≥ p^{b_{[1,m₀-1]}}`, `Bmax ≤ 3 log x/log p`).
* `AP.lean`: the number of elements of a residue class in a convex class (`ap_count`; the difference per class is at most 1).
* `Count.lean`: `Π_x ≤ x^{1/2}`, the harmonic sum per class, `C_k ≤ 1 + 2(p-1)^2(log 4 + log p)`.
* `Flat.lean`: the difference in (EP2) is `≤ Π_x`.
* `Asymp.lean`: if `α ≤ α₀ = 1 + d/(3 log q)`, then `Good` holds for large `x`.
-/

namespace GGMCollatz

namespace ND

variable (F : Family)

/-- **(EP1)**. -/
theorem eprimeC : eprimeC_statement F := by
  refine ⟨EPrimeAux.alpha0 F, EPrimeAux.one_lt_alpha0 F, fun α hα hα₀ => ?_⟩
  refine ⟨EPrimeAux.Kc F, EPrimeAux.Kc_pos F, ?_⟩
  filter_upwards [EPrimeAux.eventually_good F hα hα₀] with x hG
  intro k hk X
  exact EPrimeAux.cE_le_of_good F hG hk X

/-- **(EP2)**. -/
theorem eprimeFlat : eprimeFlat_statement F := by
  refine ⟨EPrimeAux.alpha0 F, EPrimeAux.one_lt_alpha0 F, fun α hα hα₀ => ?_⟩
  filter_upwards [EPrimeAux.eventually_good F hα hα₀] with x hG
  intro k _ X A B
  exact (EPrimeAux.flat_le_card_keys F α x k X A B).trans (EPrimeAux.card_keys_le F hG)

end ND

end GGMCollatz
