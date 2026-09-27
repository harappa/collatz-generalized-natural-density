import Mathlib.Analysis.Fourier.ZMod

/-!
# Parseval (Plancherel) identity for the discrete Fourier transform on `ZMod N`

Derived from `TaoCollatz/Fourier/Parseval.lean` of gotrevor/tao-collatz (Apache-2.0), commit 15efca2;
generalized to the GGM family: the content is general in the modulus `N`, so the body is unchanged. To avoid name clashes,
the namespace was moved from `ZMod` to `GGMCollatz`. The Plancherel step of GGM (arXiv:2111.06170) §5 Step 1.

* `dft_parseval_complex`: `∑ₖ 𝓕Φ(k)·conj(𝓕Φ(k)) = N · ∑ⱼ Φ(j)·conj(Φ(j))`.
* `dft_parseval`: the real form `∑ₖ ‖𝓕Φ(k)‖² = N · ∑ⱼ ‖Φ(j)‖²`.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GGMCollatz

variable {N : ℕ} [NeZero N]

/-- **Plancherel (complex form)**: `ZMod.dft` preserves the Hermitian inner product up to the factor `N`. -/
theorem dft_parseval_complex (Φ : ZMod N → ℂ) :
    ∑ k, ZMod.dft Φ k * conj (ZMod.dft Φ k) = (N : ℂ) * ∑ j, Φ j * conj (Φ j) := by
  have hortho : ∀ t : ZMod N, ∑ k : ZMod N, ZMod.stdAddChar (t * k)
      = if t = 0 then (N : ℂ) else 0 := by
    intro t
    split_ifs with h
    · simp [h]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)
  simp only [ZMod.dft_apply, smul_eq_mul]
  have hconj : ∀ k : ZMod N, conj (∑ l, ZMod.stdAddChar (-(l * k)) * Φ l)
      = ∑ l, ZMod.stdAddChar (l * k) * conj (Φ l) := by
    intro k
    rw [map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_mul, ← AddChar.map_neg_eq_conj, neg_neg]
  simp_rw [hconj]
  have step : ∀ k : ZMod N,
      (∑ j, ZMod.stdAddChar (-(j * k)) * Φ j) * (∑ l, ZMod.stdAddChar (l * k) * conj (Φ l))
        = ∑ j, ∑ l, (Φ j * conj (Φ l)) * ZMod.stdAddChar ((l - j) * k) := by
    intro k
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [show ZMod.stdAddChar (-(j * k)) * Φ j * (ZMod.stdAddChar (l * k) * conj (Φ l))
        = (Φ j * conj (Φ l)) * (ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (l * k)) from by ring,
      ← AddChar.map_add_eq_mul, show -(j * k) + l * k = (l - j) * k from by ring]
  simp_rw [step]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single j]
  · simp_rw [sub_self, zero_mul, AddChar.map_zero_eq_one, mul_one]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_comm]
  · intro l _ hl
    rw [← Finset.mul_sum, hortho (l - j), if_neg (fun h => hl (sub_eq_zero.mp h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Parseval (real `L²` form)**: `∑ₖ ‖𝓕Φ(k)‖² = N · ∑ⱼ ‖Φ(j)‖²`. -/
theorem dft_parseval (Φ : ZMod N → ℂ) :
    ∑ k, ‖ZMod.dft Φ k‖ ^ 2 = (N : ℝ) * ∑ j, ‖Φ j‖ ^ 2 := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj]; norm_cast; exact Complex.sq_norm z
  have hcast : ((∑ k, ‖ZMod.dft Φ k‖ ^ 2 : ℝ) : ℂ) = ((N : ℝ) * ∑ j, ‖Φ j‖ ^ 2 : ℝ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast,
      Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hz (ZMod.dft Φ k)),
      Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hz (Φ j))]
    exact dft_parseval_complex Φ
  exact_mod_cast hcast

end GGMCollatz
