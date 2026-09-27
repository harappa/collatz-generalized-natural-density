import GGMCollatz.Tao.Sec7.TriSep

/-!
# GGM §6 Step 2: the black set is a union of separated triangles (counterpart of §7.2 and Lemma 7.4 of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Triangles.lean`;
generalized to the GGM family (p, q, r). Modified. GGM §6 Step 2.

* `phaseC_not_dvd`: if `q ∤ ξ` then `q^{2B+2} ∤ ξ r(j₀)(p-1)` (`B = edgeB`). The `a`-adic valuation argument at the
  beginning of GGM §6 Step 2 (the treatment of the edge when `q` is composite).
* `black_structure`: **Lemma 7.4 (GGM form)**. If `ε` is small and `q^{2B+2} ∤ c`, then all black points of the strip
  `j + 1 ≤ n/2 - B` lie in a union of triangles (slope `log q² : log p`) that are mutually at distance at least `sepc · log(1/ε)`
  and at distance at least `sepc · log(1/ε)` from the edge `{j = n/2 - B}`.
-/

namespace GGMCollatz

namespace Family

variable (F : Family)

/-- **Arithmetic of the edge width** (GGM §6 Step 2): if `q ∤ ξ` then `q^{2B+2} ∤ ξ r(j₀)(p-1)`.
(From `q ∤ ξ r(j₀)` there is a prime `a` with `v_a(ξ r(j₀)) < v_a(q)`. If `q^m ∣ ξ r(j₀)(p-1)` then
`v_a(p-1) ≥ (m-1) v_a(q) + 1 ≥ m`, but `v_a(p-1) < p`, hence `m < p ≤ 2B+2`.) -/
theorem phaseC_not_dvd {ξ : ℕ} (hξ : ¬ F.q ∣ ξ) :
    ¬ (F.q : ℤ) ^ (2 * F.edgeB + 2) ∣ F.phaseC ξ := by
  intro hdvd
  have hξZ : ¬ (F.q : ℤ) ∣ (ξ : ℤ) := by exact_mod_cast hξ
  have hX := F.goodDigit_spec hξZ
  set X : ℤ := (ξ : ℤ) * F.r (F.goodDigit ξ) with hXdef
  have hX0 : X ≠ 0 := by
    intro h0; apply hX; rw [h0]; exact dvd_zero _
  set m : ℕ := 2 * F.edgeB + 2 with hm
  -- move to natural numbers: `q^m ∣ |X| (p-1)`, `q ∤ |X|`
  set a : ℕ := X.natAbs with ha
  set b : ℕ := F.p - 1 with hb
  have hp2 := F.two_le_p
  have ha0 : a ≠ 0 := by rw [ha]; exact Int.natAbs_ne_zero.mpr hX0
  have hb0 : b ≠ 0 := by omega
  have hq0 : F.q ≠ 0 := F.q_pos.ne'
  have hqa : ¬ F.q ∣ a := by
    intro h
    apply hX
    rw [← Int.natAbs_dvd_natAbs] at *
    simpa [ha] using h
  have hdvdN : F.q ^ m ∣ a * b := by
    have h1 : ((F.q : ℤ) ^ m).natAbs ∣ (F.phaseC ξ).natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
    have h2 : (F.phaseC ξ).natAbs = a * b := by
      unfold phaseC
      rw [← hXdef, Int.natAbs_mul]
      congr 1
      rw [hb]
      have : ((F.p : ℤ) - 1) = ((F.p - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ F.p)]; ring
      rw [this, Int.natAbs_natCast]
    rw [h2, Int.natAbs_pow, Int.natAbs_natCast] at h1
    exact h1
  -- a prime `r` with `v_r(a) < v_r(q)`
  have hnle : ¬ F.q.factorization ≤ a.factorization := by
    rw [Nat.factorization_le_iff_dvd hq0 ha0]; exact hqa
  rw [Finsupp.le_def] at hnle
  push Not at hnle
  obtain ⟨r, hr⟩ := hnle
  have hle : (F.q ^ m).factorization ≤ (a * b).factorization :=
    (Nat.factorization_le_iff_dvd (pow_ne_zero _ hq0) (mul_ne_zero ha0 hb0)).mpr hdvdN
  have hler := (Finsupp.le_def.mp hle) r
  rw [Nat.factorization_pow, Nat.factorization_mul ha0 hb0] at hler
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply] at hler
  have hbr : b.factorization r < b := Nat.factorization_lt r hb0
  have hQ : 1 ≤ F.q.factorization r := by omega
  have hB : F.edgeB = F.p := rfl
  -- `m v_r(q) ≤ v_r(a) + v_r(b)`, `v_r(a) < v_r(q)`, `v_r(b) < p - 1`
  have hmQ : (2 * F.p + 1) * F.q.factorization r ≥ 2 * F.p + 1 :=
    Nat.le_mul_of_pos_right _ hQ
  have hm' : m * F.q.factorization r
      = (2 * F.p + 1) * F.q.factorization r + F.q.factorization r := by
    rw [hm, hB]; ring
  omega

/-- **Lemma 7.4 (GGM form)**: the triangle structure of the black set. -/
theorem black_structure :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∀ (n : ℕ) (c : ℤ),
      ¬ (F.q : ℤ) ^ (2 * F.edgeB + 2) ∣ c →
      ∃ T : F.TriFam (n / 2 - F.edgeB) (F.sep ε),
        ∀ x : ℕ × ℤ, x.1 + 1 ≤ n / 2 - F.edgeB → F.black n c ε x.1 x.2 → x ∈ T.blk := by
  classical
  obtain ⟨ε₁, hε₁, hsmall⟩ := Tri.small_exists F
  refine ⟨ε₁, hε₁, ?_⟩
  intro ε hε hεle n c hc
  have S := hsmall ε hε hεle
  have H : Tri.Hyp F n c ε := ⟨hc, hε, S.le_w⟩
  set half := n / 2 - F.edgeB with hhalf
  have hstrip : ∀ x : ℕ × ℤ, x.1 + 1 ≤ half → 2 * x.1 + 2 * F.edgeB + 2 ≤ n := by
    intro x hx; omega
  have hsep0 : 0 ≤ F.sep ε := by
    have hL : 0 ≤ Real.log (1 / ε) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hε]
      have := Tri.wth_le F
      linarith [S.le_w]
    unfold Family.sep
    exact mul_nonneg (Tri.sepc_pos F).le hL
  -- corner triples and the black strip
  set cT : ℕ × ℤ → ℕ × ℤ × ℝ := fun x =>
    (Tri.jstar F n c ε x.1 x.2, Tri.lstar F n c ε x.1 x.2, Tri.cornerSize F n c ε x.1 x.2)
    with hcT
  set Bset : Set (ℕ × ℤ) := {x | x.1 + 1 ≤ half ∧ F.black n c ε x.1 x.2} with hBset
  have hsize : ∀ t ∈ cT '' Bset, 0 ≤ t.2.2 := by
    rintro t ⟨w, ⟨hws, hwb⟩, rfl⟩
    have h2j := hstrip w hws
    have hθpos := Tri.corner_phase_pos (l := w.2) H h2j
    have hcb : |Tri.th F n c (Tri.jstar F n c ε w.1 w.2) (Tri.lstar F n c ε w.1 w.2)| ≤ ε :=
      Tri.black_of_jstar_le H h2j hwb le_rfl (Tri.jstar_le w.1 w.2)
    show 0 ≤ Tri.cornerSize F n c ε w.1 w.2
    unfold Tri.cornerSize
    apply Real.log_nonneg
    rw [le_div_iff₀ hθpos, one_mul]
    exact hcb
  have hsepd : ∀ t ∈ cT '' Bset, ∀ t' ∈ cT '' Bset, t ≠ t' →
      ∀ x ∈ F.triangle t.1 t.2.1 t.2.2, ∀ x' ∈ F.triangle t'.1 t'.2.1 t'.2.2,
        F.sep ε ^ 2 ≤ ((x.1 : ℝ) - x'.1) ^ 2 + ((x.2 : ℝ) - x'.2) ^ 2 := by
    rintro t ⟨w, ⟨hws, hwb⟩, rfl⟩ t' ⟨w', ⟨hws', hwb'⟩, rfl⟩ hne x hx x' hx'
    by_contra hcon
    push Not at hcon
    have hw2j := hstrip w hws
    have hw2j' := hstrip w' hws'
    have hx2j := Tri.corner_triangle_strip H S hw2j hx
    have hxb := Tri.black_of_mem_corner_triangle H hw2j hx
    have hx'b := Tri.black_of_mem_corner_triangle H hw2j' hx'
    -- within `R = ⌈sep ε⌉` in each coordinate
    set R : ℕ := ⌈F.sep ε⌉₊ with hR
    have hσR : F.sep ε ≤ (R : ℝ) := Nat.le_ceil _
    have h1 : ((x.1 : ℝ) - x'.1) ^ 2 < F.sep ε ^ 2 := by
      nlinarith [sq_nonneg ((x.2 : ℝ) - x'.2)]
    have h2 : ((x.2 : ℝ) - x'.2) ^ 2 < F.sep ε ^ 2 := by
      nlinarith [sq_nonneg ((x.1 : ℝ) - x'.1)]
    obtain ⟨a1, a2⟩ := abs_lt.mp (abs_lt_of_sq_lt_sq h1 hsep0)
    obtain ⟨b1, b2⟩ := abs_lt.mp (abs_lt_of_sq_lt_sq h2 hsep0)
    have e1 : ((x.1 : ℤ) : ℝ) - ((x'.1 : ℤ) : ℝ) < ((R : ℤ) : ℝ) := by push_cast; linarith
    have e2 : ((x'.1 : ℤ) : ℝ) - ((x.1 : ℤ) : ℝ) < ((R : ℤ) : ℝ) := by push_cast; linarith
    have e3 : ((x.2 : ℤ) : ℝ) - ((x'.2 : ℤ) : ℝ) < ((R : ℤ) : ℝ) := by push_cast; linarith
    have e4 : ((x'.2 : ℤ) : ℝ) - ((x.2 : ℤ) : ℝ) < ((R : ℤ) : ℝ) := by push_cast; linarith
    have z1 : (x.1 : ℤ) - x'.1 < R := by exact_mod_cast e1
    have z2 : (x'.1 : ℤ) - x.1 < R := by exact_mod_cast e2
    have z3 : x.2 - x'.2 < (R : ℤ) := by exact_mod_cast e3
    have z4 : x'.2 - x.2 < (R : ℤ) := by exact_mod_cast e4
    have hnear := Tri.black_near_black_mem_corner H S.near hx2j hxb hx'b
      (by omega) (by omega) (by omega) (by omega)
    have hwx := Tri.corner_eq H hw2j hwb hx
    have hxx' := Tri.corner_eq H hx2j hxb hnear
    have hw'x' := Tri.corner_eq H hw2j' hwb' hx'
    have hj : Tri.jstar F n c ε w.1 w.2 = Tri.jstar F n c ε w'.1 w'.2 := by omega
    have hl : Tri.lstar F n c ε w.1 w.2 = Tri.lstar F n c ε w'.1 w'.2 := by omega
    apply hne
    simp only [hcT]
    unfold Tri.cornerSize
    rw [hj, hl]
  have hconf : ∀ t ∈ cT '' Bset, ∀ x ∈ F.triangle t.1 t.2.1 t.2.2,
      (x.1 : ℝ) + 1 ≤ (half : ℝ) - F.sep ε := by
    rintro t ⟨w, ⟨hws, hwb⟩, rfl⟩ x hx
    exact Tri.corner_triangle_confined H S (hstrip w hws) hx
  refine ⟨⟨cT '' Bset, hsize, hsepd, hconf⟩, ?_⟩
  intro x hx hb
  simp only [Family.TriFam.blk, Set.mem_iUnion, exists_prop]
  refine ⟨cT x, ⟨x, ⟨hx, hb⟩, rfl⟩, ?_⟩
  exact Tri.black_mem_corner_triangle H (hstrip x hx) hb

end Family

end GGMCollatz
