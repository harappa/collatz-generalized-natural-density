# A power saving in natural density for generalized Collatz maps

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22986677.svg)](https://doi.org/10.5281/zenodo.22986677)

This repository contains the Lean 4 formalization accompanying the preprint *A power saving in natural density for
generalized Collatz maps* by Hiroyuki Nashida (Zenodo, 2026, doi:10.5281/zenodo.22986677). It is the complete Lean
project `GGMCollatz` (182 files, about 50,000 lines), which formalizes the results of the paper for the generalized
Collatz maps of Gonçalves, Greenfeld and Madrid (the logarithmic-density theorem, the natural-density theorem with a
power saving in $N_0$ uniform in $X$, and its corollaries), including the four propositions of Gonçalves, Greenfeld
and Madrid on which the proof rests; the natural-density theorems take a transcription of Matveev's lower bound for
linear forms in two logarithms as an explicit hypothesis.

## Paper

- Author: Hiroyuki Nashida
- Title: *A power saving in natural density for generalized Collatz maps*
- Preprint: Zenodo, 2026
- DOI: [10.5281/zenodo.22986677](https://doi.org/10.5281/zenodo.22986677)
- Lean code: this repository

Revision r5 (September 27, 2026). This repository accompanies revision r5 of the paper; the revision number is
incremented with every revision of the paper and of this repository.

## Abstract

Let $p,q\ge 2$ be coprime integers with $q<p^{p/(p-1)}$, and let $r(1),\dots,r(p-1)$ be integers with
$qj+r(j)\equiv 0 \pmod p$ and $qj+r(j)\ge 1$. The generalized Collatz map of Gonçalves, Greenfeld and Madrid is
$C(N)=N/p$ if $p\mid N$ and $C(N)=qN+r(j)$ if $N\equiv j\pmod p$; the Collatz map is the case $p=2$, $q=3$,
$r(1)=1$. Extending Tao's theorem, Gonçalves, Greenfeld and Madrid proved that for every $f$ with $f(N)\to\infty$,
the orbit of almost every $N$ in the sense of logarithmic density attains a value below $f(N)$, and remarked that
the natural-density version seemed out of reach. We prove the natural-density version with a power saving in $N_0$,
uniform in $X$: there are $K,c>0$ such that for all integers $N_0\ge 1$ and reals $X\ge 1$,

$$\left|\lbrace 1\le N\le X : C^{k}(N)>N_0 \text{ for all } k\ge 0\rbrace\right| \le K X N_0^{-c}.$$

We also prove the logarithmic-density form $\sum_{N\le x,\ C^k(N)>N_0\ \forall k}1/N\le K N_0^{-c'}\log x$ for
$x\ge3$. The proof combines a fixed-barrier estimate, the first-passage stabilization of
Gonçalves-Greenfeld-Madrid carried through a one-step recursion, and a comparison of first passage from uniform and
from logarithmic windows; the only additional Diophantine input is an effective irrationality measure of
$\log q/\log p$, which follows from Matveev's lower bound for linear forms in two logarithms. The argument,
including the propositions of Gonçalves-Greenfeld-Madrid on which it rests, is formalized in Lean 4 and checked by
the kernel. The formal natural-density theorem is conditional: it takes a transcription of Matveev's corollary for
the two logarithms $\log p,\log q$ as its only hypothesis (Matveev's theorem itself is not formalized); the
logarithmic-density theorem has no hypothesis; no axioms beyond the three used throughout Mathlib are used. The
constants $K,c,c'$ are not effective, and the exponents are very small (for $p=3$, $q=4$ our proof gives
$c\le 1.2\times10^{-14}$). The Lean code is available in this repository.

## Main results in Lean

The main declarations are in the namespace `GGMCollatz` (`GGM` stands for Gonçalves, Greenfeld and Madrid).

### The maps and the families

For integers `p, q ≥ 2` and `r : ℕ → ℤ` (only the values `r 1, …, r (p-1)` matter), the map of
Gonçalves, Greenfeld and Madrid is

```lean
def C (N : ℕ) : ℕ :=
  if N % G.p = 0 then N / G.p else ((G.q : ℤ) * N + G.r (N % G.p)).toNat
noncomputable def Cmin (N : ℕ) : ℕ := sInf (Set.range fun k => G.C^[k] N)
```

`C` is the map $C_{p,q,r}$ of the paper, and `Cmin N` is the minimum of the orbit of `N` (the iterates `C^[k] N`
for all `k ≥ 0`, including `N` itself).

`FamilyGen` (in `GGMCollatz/StatementB.lean`) collects the conditions of their Theorem 1.3:
(a) `Nat.Coprime p q`, (b) `q < p ^ (p / (p - 1))` (real power), (c) `p ∣ q j + r j` and
`1 ≤ q j + r j` for `0 < j < p`. `Family` (in `GGMCollatz/Basic.lean`) adds (d) `gcd(q, r 1, …, r (p-1)) = 1`
and `p < q`.

### The two main theorems

```lean
theorem GGMCollatz.FamilyGen.mainA_gen (G : FamilyGen) : G.mainA_gen_statement
-- ∃ K c' > 0, ∀ N₀ ≥ 1, ∀ x ≥ 3,
--   ∑_{N ∈ [1, ⌊x⌋], N₀ < Cmin N} 1/N ≤ K * N₀^(-c') * log x

theorem GGMCollatz.FamilyGen.mainB_gen (G : FamilyGen) (hM : MatveevHyp G.p G.q) :
    G.mainB_gen_statement
-- ∃ K c > 0, ∀ N₀ ≥ 1, ∀ X ≥ 1 (real),
--   #{N ∈ [1, ⌊X⌋] | N₀ < Cmin N} ≤ K * X * N₀^(-c)
```

`FamilyGen.mainA_gen` is Theorem A of the paper (Theorem 1.4, logarithmic density with a power saving) and has no
hypothesis. `FamilyGen.mainB_gen` is the main theorem of the paper (Theorem 1.1, natural density with a power saving
in `N₀`, uniform in `X`); its only hypothesis is `MatveevHyp G.p G.q` (below).

### The corollaries

The corollaries of the main theorem (Corollary 8.6 of the paper) are in `GGMCollatz/Corollary.lean`. `corollaries`
gives, with the same `K, c` as the main theorem, (i) the upper natural density, (iii) the barrier `X^θ` and (iv)
the barrier `N^θ`; `density_one` is (ii), natural density one for any `f → ∞`:

```lean
theorem GGMCollatz.FamilyGen.corollaries (G : FamilyGen) (hM : MatveevHyp G.p G.q) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      (∀ N₀ : ℕ, 1 ≤ N₀ → ∀ X : ℝ, 1 ≤ X →
        (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => N₀ < G.Cmin N)).card : ℝ)
          ≤ K * X * (N₀ : ℝ) ^ (-c)) ∧
      (∀ N₀ : ℕ, 1 ≤ N₀ →
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => N₀ < G.Cmin N)).card : ℝ) / X) ∧
        Filter.limsup
          (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => N₀ < G.Cmin N)).card : ℝ) / X)
          Filter.atTop ≤ K * (N₀ : ℝ) ^ (-c)) ∧
      (∀ θ : ℝ, 0 < θ → ∀ X : ℝ, 1 ≤ X →
        (((Finset.Icc 1 ⌊X⌋₊).filter (fun N => X ^ θ < (G.Cmin N : ℝ))).card : ℝ)
          ≤ 2 ^ c * K * X ^ (1 - θ * c)) ∧
      (∀ θ : ℝ, 0 < θ → θ * c < 1 → ∀ X : ℝ, 1 ≤ X →
        (((Finset.Icc 1 ⌊X⌋₊).filter (fun N : ℕ => (N : ℝ) ^ θ < (G.Cmin N : ℝ))).card : ℝ)
          ≤ 2 ^ (c * (1 + θ)) * K * X ^ (1 - θ * c) / (1 - 2 ^ (θ * c - 1)))

theorem GGMCollatz.FamilyGen.density_one (G : FamilyGen) (hM : MatveevHyp G.p G.q) (f : ℕ → ℝ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun X : ℕ => (((Finset.Icc 1 X).filter (fun N => (G.Cmin N : ℝ) < f N)).card : ℝ) / X)
      Filter.atTop (nhds 1)
```

In `corollaries` the first conjunct is the main theorem, so the constants of the other parts are those of the main
theorem; part (i) is stated as a bounded sequence whose `limsup` is at most `K * N₀^(-c)`. `density_one` says that
the set of `N ≥ 1` with `Cmin N < f N` has natural density one whenever `f N → ∞`. Both take `MatveevHyp` as a
hypothesis.

### The theorems for `Family` and the propositions of Gonçalves–Greenfeld–Madrid

`Family.mainA` and `Family.mainB` are the same statements for `Family` (Theorem 5.7(ii) and Theorem 8.4 of the
paper, for the maps with (a)–(d) and `p < q`); `General.lean` transfers them to `FamilyGen` (Section 3 of the
paper). `Family.mainB` takes `MatveevHyp F.p F.q` as a hypothesis; `Family.mainA` has none. The propositions of
Gonçalves–Greenfeld–Madrid that the proof uses are proved here, not assumed: `Family.prop33` (their
Proposition 3.1; the name reflects an earlier miscount of the numbering and is kept because it belongs to the frozen
statement files), `Family.prop35` (Proposition 3.5), `Family.prop41_of_prop51` (Proposition 5.1 implies
Proposition 4.1) and `Family.prop51` (Proposition 5.1).

### The hypothesis `MatveevHyp`

```lean
def MatveevHyp (p q : ℕ) : Prop :=
  ∀ b₁ b₂ : ℤ, (b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q ≠ 0 →
    Real.exp (-(10 ^ 9 : ℝ) * Real.log p * Real.log q *
        (1 + Real.log ((max |b₁| |b₂| : ℤ) : ℝ)))
      ≤ |(b₁ : ℝ) * Real.log p + (b₂ : ℝ) * Real.log q|
```

This is E. M. Matveev, Izv. Math. 64 (2000), Corollary 2.3, for two logarithms of rational integers, with the
constant `C₁(2) ≈ 7.4732e8` weakened to `10^9`. `MatveevBridge.lean` states the corollary, specialized to this case
(n = 2 over ℚ, α₁ = p, α₂ = q), in its two forms with B of (1.3) and B* of (1.4) (`Matveev.Cor23B13`,
`Matveev.Cor23Bstar`), and proves `Matveev.hyp_of_B13`: the corollary implies `MatveevHyp p q` for all `p, q ≥ 2`.
For `p = 1` the hypothesis is false (`Matveev.not_hyp_1_2`); the structures require `p, q ≥ 2`. The hypothesis is
used only for the irrationality measure of `log q / log p` (`NatDen/Irr.lean`); `mainA`, `mainA_gen` and the four
propositions above do not use it.

## What is and is not verified

**Checked by the Lean kernel.** All theorems above are proved in Lean 4 with Mathlib and checked by the kernel when
the project is built. In addition, `lake env leanchecker --fresh GGMCollatz.Corollary` re-checked, in a fresh
environment, every declaration in the dependency closure of `GGMCollatz.Corollary`, including Mathlib; this closure
contains `FamilyGen.corollaries`, `FamilyGen.density_one`, `FamilyGen.mainB_gen`, `FamilyGen.mainA_gen`,
`Family.mainB`, `Family.mainA` and the four propositions of Gonçalves–Greenfeld–Madrid (see
[Verification records](#verification-records)). There is no `sorry`, no project axiom and no `native_decide`: the
specification tests use `decide` and `decide +kernel`.

**Hypotheses.** `FamilyGen.mainA_gen`, `Family.mainA` and the four propositions of Gonçalves–Greenfeld–Madrid have
no hypothesis beyond the conditions on the map (the fields of `FamilyGen` or `Family`). `Family.mainB`,
`FamilyGen.mainB_gen`, `FamilyGen.corollaries` and `FamilyGen.density_one` take `MatveevHyp` as an explicit
hypothesis. `Matveev.hyp_of_B13` takes the transcription `Matveev.Cor23B13` of Matveev's corollary (for all
`p, q ≥ 2`) as its hypothesis. Matveev's theorem itself is not formalized, so the formal natural-density theorems
are implications whose premise is supplied by Matveev's published proof.

**Axioms.** `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` (the three axioms used throughout
Mathlib) for `Family.mainA`, `Family.mainB`, `FamilyGen.mainA_gen`, `FamilyGen.mainB_gen`,
`FamilyGen.corollaries` and `FamilyGen.density_one`, and also for `Family.prop33`, `Family.prop35`,
`Family.prop51` and `Matveev.hyp_of_B13` (see `verify/axioms.log`). `#print axioms` lists axioms, not hypotheses:
an explicit hypothesis such as `MatveevHyp` is part of the statement, does not appear in this list, and is not an
axiom.

**What rests on the written proof or on reading.**

- The transcription of Matveev's Corollary 2.3 in `MatveevBridge.lean` (`Matveev.Cor23B13`, `Matveev.Cor23Bstar`):
  that these propositions say what the published corollary says in this special case is a matter of reading
  (Appendix A of the paper gives the specialization with a table of the correspondence of symbols), and the
  corollary itself rests on Matveev's published proof. The bound `C₁(2) ≤ 10^9` on its constant is proved in Lean
  (`Matveev.C1_le`).
- The correspondence between the Lean definitions (the structures `Family` and `FamilyGen`, the maps `C` and
  `Cmin`, the counted sets) and the statements of the paper and of Gonçalves–Greenfeld–Madrid is a matter of reading
  the statement files (`Basic.lean`, `Statement.lean`, `StatementB.lean`, `Inter.lean`, `Corollary.lean`); Section 9
  of the paper discusses it, and the specification tests (`Spec.lean`, `General/Spec.lean`) evaluate the
  definitions on small values.
- Explicit constants: the Lean statements assert only the existence of constants `K, c, c' > 0`. The estimates of
  their size in the paper (for example $c\le 1.2\times10^{-14}$ for $(p,q)=(3,4)$) are derived in the paper and are
  not part of the formal statements.

**Review status.** This work has not yet been reviewed by independent human experts.

## Repository layout

| Path | Content |
|---|---|
| `GGMCollatz/Basic.lean`, `Statement.lean`, `StatementB.lean`, `Inter.lean` | Definitions and the frozen statements (the family, the maps `C`, `S`, orbit minima, windows, first passage; the statements of the main theorems and of the intermediate propositions of Gonçalves–Greenfeld–Madrid). |
| `GGMCollatz/Tao/` | The machinery of Tao's proof generalized to these maps: valuations and the Syracuse random variable (`Syracuse/`, Proposition 3.1), first passage (`Sec5/`, Proposition 3.5), fine-scale mixing (`Sec6/`, Proposition 4.1), decay of the characteristic function by the renewal argument (`Sec7/`, Proposition 5.1), probability tools (`Prob/`, `Fourier/`). |
| `GGMCollatz/Seed.lean`, `Seed/` | The fixed-barrier estimate (the seed). |
| `GGMCollatz/Assembly.lean`, `Assembly/`, `Main.lean` | One-step recursion and Theorem A (`Family.mainA`). |
| `GGMCollatz/NatDen/` | Natural density: local limit theorem, conditioned decay and mixing, Kronecker equidistribution, irrationality measure from `MatveevHyp`, uniform first passage, top conversion, Theorem 8.4 of the paper (`Family.mainB`). |
| `GGMCollatz/General.lean`, `General/`, `MainB.lean` | Removal of condition (d) and of `p < q` (`FamilyGen.mainA_gen`, `FamilyGen.mainB_gen`). |
| `GGMCollatz/Corollary.lean` | Corollary 8.6 of the paper: upper density, natural density one for any `f → ∞` (`FamilyGen.density_one`), the barriers `X^θ` and `N^θ` (`FamilyGen.corollaries`); hypothesis `MatveevHyp`. |
| `GGMCollatz/MatveevBridge.lean` | Matveev's corollary specialized to two logarithms (transcription) and the implication to `MatveevHyp`. |
| `GGMCollatz/Spec.lean`, `General/Spec.lean` | Specification tests on small values. |
| `verify/` | Axiom report (`Axioms.lean`, `axioms.log`), clean-clone build record (`build.log`) and kernel re-check log (`leanchecker.log`). |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake project, pinned dependency (Mathlib) and Lean toolchain. |
| `LICENSE`, `NOTICE` | Apache License 2.0; copyright, third-party notices and the list of derived files. |
| `MANIFEST.sha256` | SHA-256 of every file in this repository except the manifest itself. |

The Lean sources are those of commit `6c8dd13` of the author's source repository; only the comments were translated
into English (a script of the source repository checks that the code is otherwise identical).

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan) (it installs the toolchain of `lean-toolchain`, Lean
v4.33.1, automatically) and `git`; `lake exe cache get` downloads the Mathlib build cache. Run the commands in the
root of a clone of this repository.

```sh
sha256sum -c MANIFEST.sha256    # optional: compare the files with the manifest
lake exe cache get              # Mathlib build cache (commit 0df444a)
lake build                      # the whole project (verify/Axioms.lean imports MainB, Corollary, MatveevBridge)
lake env lean verify/Axioms.lean                    # statements and #print axioms (compare with verify/axioms.log)
lake env leanchecker --fresh GGMCollatz.Corollary   # kernel re-check of the closure, including Mathlib
```

The build of the project takes about 10 minutes on a many-core machine after the Mathlib cache is downloaded.
`lake env leanchecker --fresh GGMCollatz.Corollary` re-checks every declaration of the dependency closure of the
corollaries (which contains `GGMCollatz.MainB`), including Mathlib, with the kernel; it is single-threaded, and the
recorded run took about 35 minutes (`verify/leanchecker.log`).

## Versions

Lean v4.33.1 and Mathlib at commit 0df444a (pinned by `lake-manifest.json`). Both are stable releases; they are the
versions to which `tao-collatz` (commit 15efca2), from which 89 files are derived, is pinned, and we kept them so that
the derived files stay close to their sources. The project depends only on Mathlib. At the time of writing the latest
stable Lean release is v4.34; a rebuild on it has not been done.

## Verification records

The Lean code has not changed since revision r2 of the paper; the records below were made on commit `6c8dd13` of
the source repository (2026-09-27, Lean v4.33.1, Mathlib 0df444a) and apply to this revision.

- `verify/Axioms.lean`: `#check` of the main statements, of `Family.mainA`, `Family.mainB` and of
  `Matveev.hyp_of_B13`, and `#print axioms` for these and for `Family.prop33`, `Family.prop35` and `Family.prop51`.
- `verify/axioms.log`: the output of `lake env lean verify/Axioms.lean`, run on this bundle after `lake build`: the
  elaborated statements, and `[propext, Classical.choice, Quot.sound]` as the axioms of every declaration listed.
- `verify/build.log`: a clean clone of the source repository at commit `6c8dd13`: `lake exe cache get` and
  `lake build GGMCollatz.Corollary GGMCollatz.Spec GGMCollatz.General.Spec` completed successfully (8886 jobs), and
  the axiom report of `FamilyGen.corollaries`, `FamilyGen.density_one`, `FamilyGen.mainB_gen`,
  `FamilyGen.mainA_gen`, `Family.mainB` and `Family.mainA` gave the three axioms above.
- `verify/leanchecker.log`: `lake env leanchecker --fresh GGMCollatz.Corollary` on commit `6c8dd13`
  (2026-09-27, 02:37 to 03:12, UTC+09:00), exit code 0; `leanchecker --fresh` prints nothing on success. The closure
  contains `FamilyGen.corollaries`, `FamilyGen.density_one`, `FamilyGen.mainB_gen`, `FamilyGen.mainA_gen`,
  `Family.mainB`, `Family.mainA` and the four propositions of Gonçalves–Greenfeld–Madrid. Earlier runs, for
  `GGMCollatz.MainB`, `GGMCollatz.General` and `GGMCollatz.Main` (revision r1 and before), are recorded as well.

## License

The Lean code and scripts in this repository are licensed under the Apache License, Version 2.0 (see `LICENSE`).

| Component | Use in this repository | Copyright holder | License |
|---|---|---|---|
| [tao-collatz](https://github.com/gotrevor/tao-collatz), commit `15efca2` | 89 derived files included (modified; listed in `NOTICE`) | Trevor Morris (as stated in its README) | Apache-2.0 |
| [FirstPassageLinearTransport](https://github.com/shaikidris/FirstPassageLinearTransport), commit `7239f88` | 5 derived files included (modified; listed in `NOTICE`) | Idris Ali Shaik | Apache-2.0 |
| [Mathlib](https://github.com/leanprover-community/mathlib4), commit `0df444a` | dependency fetched at build time (not included) | the Mathlib authors (named in each file's header) | Apache-2.0 |
| batteries, aesop, plausible, Qq, importGraph, proofwidgets, LeanSearchClient (pinned in `lake-manifest.json`) | dependencies of Mathlib fetched at build time (not included) | see each repository | Apache-2.0 |
| Cli (lean4-cli, pinned in `lake-manifest.json`) | dependency of Mathlib fetched at build time (not included) | mhuisi | MIT |

`NOTICE` gives the copyright of this project, the third-party notices and the list of derived files. The paper
itself is not part of this repository; it is distributed on Zenodo
([doi:10.5281/zenodo.22986677](https://doi.org/10.5281/zenodo.22986677)) under the license stated there.

## How to cite

```bibtex
@misc{nashida2026generalized,
  author    = {Hiroyuki Nashida},
  title     = {A power saving in natural density for generalized Collatz maps},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.22986677},
  url       = {https://doi.org/10.5281/zenodo.22986677},
  note      = {Preprint}
}
```

## Attribution and the role of AI

- 89 files are derived from `tao-collatz` (https://github.com/gotrevor/tao-collatz, commit 15efca2), a Lean 4
  formalization of Tao's theorem, and 5 files (the seed) from Idris Ali Shaik's `FirstPassageLinearTransport`
  (https://github.com/shaikidris/FirstPassageLinearTransport, commit 7239f88), both under the Apache License 2.0.
  The derived files name their source in their headers; `NOTICE` lists them and states that they were modified.
- All code of this project, including the generalization of the derived files, was written with Anthropic Claude
  models accessed through Claude Code, directed by the author. The kernel check does not depend on how the code
  was produced.
