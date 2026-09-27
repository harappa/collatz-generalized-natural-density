import GGMCollatz.NatDen.Statements
import GGMCollatz.Tao.Sec5.Stabilization

/-!
# Decomposition of the profile on the uniform side: definitions

Window: `y = x^α`, `Y = (x^α)^α`, `W = ℕ_p ∩ [y, Y]` (`F.logWindow`), `Z = #W` (`wCard`).
`m₀ = F.mZero α x`, `n₀ = F.nZero x`, `E' = F.Eprime α x E` (the definitions of the logarithmic side `Tao/Sec5/Defs.lean`, with `β = α`).
Rows `n ∈ [2m₀, n₀]`, `k = n - m₀` (the `n'` of the accompanying paper).

* `urow F α x E n`: the number of `N` in the window such that the first `k` valuations form a good tuple (`goodVec`) and `S^k(N) ∈ E'(E)`.
* `jpG F k X s G`: `P(Σa = s, F_k(v) ≡ X (q^k), G(a))` (`v = (a, digit)` i.i.d. with the one-step law, `F_k` the forward
  offset `offsetFwd`). A valid tuple has mass `p^{-Σa}`, so `p^s jpG` is a count of tuples (identity (K) of the accompanying paper).
* `inWin F y Y k s M`: `y < p^s M / q^k ≤ Y` (the paper's `s ∈ Σ(n, M)`, `p^s/q^k = p^{s - kλ}`).
* `umain F α x E n`: the main term of row `n`, `Σ_{M∈E'(E)} Σ_s p^s P(Σa = s, F_k ≡ M, a ∈ A^{(k)}) 1[s ∈ Σ(n,M)]`
  (the window indicator replaced by `s ∈ Σ(n,M)`).
* `kern F α x M`: the kernel `D(M) = Σ_{n ∈ [2m₀, n₀]} Σ_{s ∈ Σ(n,M)} p^s q^{-k} P(s_k = s)` (the `D_y(M)` of the accompanying paper).
* `m1 x = ⌊log^{0.4} x⌋`: the coarse scale of the product formula (the paper's `m₁`).
-/

open scoped ENNReal

namespace GGMCollatz

namespace ND

variable (F : Family)

/-- Number of points of the window `Z = #(ℕ_p ∩ [x^α, (x^α)^α])`. -/
noncomputable def wCard (α x : ℝ) : ℝ := ((F.logWindow (x ^ α) ((x ^ α) ^ α)).card : ℝ)

/-- The range of rows `[2m₀, n₀]`. -/
noncomputable def rows (α x : ℝ) : Finset ℕ := Finset.Icc (2 * F.mZero α x) (F.nZero x)

open Classical in
/-- The count of row `n` of the uniform window: `#{N ∈ W | a^{(k)}(N) ∈ A^{(k)}, S^k(N) ∈ E'(E)}`, `k = n - m₀`. -/
noncomputable def urow (α x : ℝ) (E : Set ℕ) (n : ℕ) : ℕ :=
  ((F.logWindow (x ^ α) ((x ^ α) ^ α)).filter (fun N =>
    F.goodVec x (F.valVec N (n - F.mZero α x)) ∧
      F.S^[n - F.mZero α x] N ∈ F.Eprime α x E)).card

open Classical in
/-- `P(Σa = s, F_k(v) ≡ X (mod q^k), G(a))` (`v i = (a_i, digit_i)` i.i.d. with law `stepLaw`). -/
noncomputable def jpG (k : ℕ) (X : ZMod (F.q ^ k)) (s : ℕ) (G : (Fin k → ℕ) → Prop) : ℝ :=
  ∑' v : Fin k → ℕ × ℕ, ((PMF.iid (stepLaw F.p) k) v).toReal *
    (if (∑ i, (v i).1 = s ∧ F.offsetFwd v = X ∧ G (fun i => (v i).1)) then 1 else 0)

/-- `s ∈ Σ(n, M)`: `y < p^s M / q^k ≤ Y`. -/
def inWin (y Y : ℝ) (k s : ℕ) (M : ℝ) : Prop :=
  y < (F.p : ℝ) ^ s * M / (F.q : ℝ) ^ k ∧ (F.p : ℝ) ^ s * M / (F.q : ℝ) ^ k ≤ Y

open Classical in
/-- The main term of row `n`: `Σ_{M ∈ E'(E)} Σ_s p^s P(Σa = s, F_k ≡ M, a ∈ A^{(k)}) 1[s ∈ Σ(n,M)]`. -/
noncomputable def umain (α x : ℝ) (E : Set ℕ) (n : ℕ) : ℝ :=
  ∑ M ∈ F.Eprime α x E, ∑' s : ℕ,
    if inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M then
      (F.p : ℝ) ^ s *
        jpG F (n - F.mZero α x) (M : ZMod (F.q ^ (n - F.mZero α x))) s (fun a => F.goodVec x a)
    else 0

open Classical in
/-- The kernel `D(M) = Σ_{n ∈ [2m₀, n₀]} Σ_{s ∈ Σ(n,M)} p^s q^{-k} P(s_k = s)`. -/
noncomputable def kern (α x M : ℝ) : ℝ :=
  ∑ n ∈ rows F α x, ∑' s : ℕ,
    if inWin F (x ^ α) ((x ^ α) ^ α) (n - F.mZero α x) s M then
      (F.p : ℝ) ^ s / (F.q : ℝ) ^ (n - F.mZero α x) * nb F.p (n - F.mZero α x) s
    else 0

/-- The coarse scale of the product formula `m₁ = ⌊log^{0.4} x⌋`. -/
noncomputable def m1 (x : ℝ) : ℕ := ⌊Real.log x ^ (0.4 : ℝ)⌋₊

/-- The kernel-weighted sum of the profile at scale `m₁`, `Σ_{M ∈ E'(E)} q^{m₁} ω_{m₁}(M) D(M)` (the numerator of the right-hand side of the master formula). -/
noncomputable def kernSum (α x : ℝ) (E : Set ℕ) : ℝ :=
  ∑ M ∈ F.Eprime α x E,
    (F.q : ℝ) ^ m1 x * ((F.syracZ (m1 x)) (M : ZMod (F.q ^ m1 x))).toReal * kern F α x M

end ND

end GGMCollatz
