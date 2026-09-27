import GGMCollatz.Tao.Sec7.TriCorner

/-!
# Tools for GGM §6 Step 2: Claim (*) (nearby black points lie in the same corner triangle), smallness of `ε`, distance from the edge

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Triangles.lean`, second half
(`corner_scale_near_le`, `weaklyBlack_of_corner_scale_near`, `black_near_black_mem_corner`,
`corner_triangle_confined`, `corner_triangle_strip`); generalized to the GGM family (p, q, r). Modified.

The lattice window `300` of tao-collatz (a numerical value for `ε = 10⁻¹⁰⁰⁰`) is replaced by the ceiling `R = ⌈σ⌉` of the separation width `σ = sep ε` and
the condition `(q²p)^R ε ≤ w` (since `sepc · log(pq²) = 1/10`, we have `(q²p)^R ε ≤ q²p · ε^{9/10}`, which holds for small `ε`).
The edge condition `sep ε + B + 2 ≤ log(1/ε)/(2 log q)` also holds for small `ε` (`sepc < 1/(2 log q)`).
Namespace `GGMCollatz.Family.Tri`.
-/

namespace GGMCollatz

namespace Family

namespace Tri

variable (F : Family)

/-- The smallness condition on `ε`. -/
structure Small (ε : ℝ) : Prop where
  pos : 0 < ε
  le_w : ε ≤ wth F
  near : ((F.q : ℝ) ^ 2 * F.p) ^ (⌈F.sep ε⌉₊) * ε ≤ wth F
  conf : F.sep ε + F.edgeB + 2 ≤ Real.log (1 / ε) / (2 * Real.log F.q)

theorem log_q_pos : 0 < Real.log (F.q : ℝ) := by
  apply Real.log_pos
  have : (2 : ℝ) ≤ F.q := by exact_mod_cast F.two_le_q
  linarith

theorem log_pq2_pos : 0 < Real.log ((F.p : ℝ) * (F.q : ℝ) ^ 2) := by
  apply Real.log_pos
  have hp : (2 : ℝ) ≤ F.p := two_le_pR F
  have hq : (4 : ℝ) ≤ (F.q : ℝ) ^ 2 := four_le_q_sq F
  nlinarith

theorem sepc_pos : 0 < F.sepc := by
  unfold Family.sepc
  have := log_pq2_pos F
  positivity

theorem sepc_mul_log : F.sepc * Real.log ((F.p : ℝ) * (F.q : ℝ) ^ 2) = 1 / 10 := by
  unfold Family.sepc
  have := (log_pq2_pos F).ne'
  field_simp

/-- `sepc < 1/(2 log q)` (`log(pq²) > 2 log q`). -/
theorem sepc_lt : F.sepc < 1 / (2 * Real.log F.q) := by
  have hlq := log_q_pos F
  have hl : 2 * Real.log (F.q : ℝ) < Real.log ((F.p : ℝ) * (F.q : ℝ) ^ 2) := by
    have hp : (1 : ℝ) < F.p := by have := two_le_pR F; linarith
    have hq : (0 : ℝ) < (F.q : ℝ) ^ 2 := by have := four_le_q_sq F; linarith
    rw [Real.log_mul (by positivity) hq.ne', Real.log_pow]
    have := Real.log_pos hp
    push_cast
    linarith
  unfold Family.sepc
  rw [div_lt_div_iff₀ (by have := log_pq2_pos F; positivity) (by positivity)]
  linarith

/-- **Existence of small `ε`**: there is `ε₁ > 0` such that `Small F ε` for `0 < ε ≤ ε₁`. -/
theorem small_exists : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → Small F ε := by
  set K : ℝ := (F.q : ℝ) ^ 2 * F.p with hK
  have hK1 : 1 ≤ K := by
    have := one_le_q_sq F; have := one_le_p F; rw [hK]; nlinarith
  have hKpos : 0 < K := by linarith
  have hw := wth_pos F
  set α : ℝ := 1 / (2 * Real.log F.q) - F.sepc with hα
  have hαpos : 0 < α := by have := sepc_lt F; rw [hα]; linarith
  set L₀ : ℝ := max ((10 / 9) * (Real.log K - Real.log (wth F)) + 1)
    (((F.edgeB : ℝ) + 2) / α) with hL₀
  refine ⟨min (wth F) (Real.exp (-L₀)), lt_min hw (Real.exp_pos _), ?_⟩
  intro ε hε hε₁
  have hεw : ε ≤ wth F := le_trans hε₁ (min_le_left _ _)
  have hεe : ε ≤ Real.exp (-L₀) := le_trans hε₁ (min_le_right _ _)
  set L : ℝ := Real.log (1 / ε) with hLdef
  have hlogε : Real.log ε = -L := by rw [hLdef, one_div, Real.log_inv, neg_neg]
  have hLL₀ : L₀ ≤ L := by
    have h := Real.log_le_log hε hεe
    rw [Real.log_exp] at h
    linarith [hlogε]
  have hL1 : (10 / 9) * (Real.log K - Real.log (wth F)) + 1 ≤ L := le_trans (le_max_left _ _) hLL₀
  have hL2 : ((F.edgeB : ℝ) + 2) / α ≤ L := le_trans (le_max_right _ _) hLL₀
  have hL0 : 0 ≤ L := by
    have : 0 ≤ ((F.edgeB : ℝ) + 2) / α := by positivity
    linarith
  have hsep : F.sep ε = F.sepc * L := rfl
  have hsep0 : 0 ≤ F.sep ε := by rw [hsep]; exact mul_nonneg (sepc_pos F).le hL0
  refine ⟨hε, hεw, ?_, ?_⟩
  · -- `(q²p)^⌈σ⌉ ε ≤ w`
    set N : ℕ := ⌈F.sep ε⌉₊ with hN
    have hNle : (N : ℝ) ≤ F.sep ε + 1 := (Nat.ceil_lt_add_one hsep0).le
    have hlogK : Real.log K = Real.log ((F.p : ℝ) * (F.q : ℝ) ^ 2) := by
      rw [hK, mul_comm]
    have hlogKnn : 0 ≤ Real.log K := Real.log_nonneg hK1
    have hpos : 0 < K ^ N * ε := by positivity
    have hlog : Real.log (K ^ N * ε) ≤ Real.log (wth F) := by
      rw [Real.log_mul (by positivity) hε.ne', Real.log_pow, hlogε]
      have h1 : (N : ℝ) * Real.log K ≤ (F.sep ε + 1) * Real.log K :=
        mul_le_mul_of_nonneg_right hNle hlogKnn
      have h2 : F.sep ε * Real.log K = L / 10 := by
        rw [hsep, hlogK, mul_comm F.sepc L, mul_assoc, sepc_mul_log]; ring
      nlinarith
    exact (Real.log_le_log_iff hpos hw).mp hlog
  · -- the edge condition
    have hlq := log_q_pos F
    have h1 : α * L ≥ (F.edgeB : ℝ) + 2 := by
      rw [div_le_iff₀ hαpos] at hL2; linarith
    have h2 : L / (2 * Real.log F.q) = (1 / (2 * Real.log F.q)) * L := by ring
    rw [h2, hsep]
    rw [hα] at h1
    nlinarith

section Near

variable {F} {n : ℕ} {c : ℤ} {ε : ℝ}

theorem pow_le_KR {R a b : ℕ} (ha : a ≤ R) (hb : b ≤ R) :
    ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b ≤ ((F.q : ℝ) ^ 2 * F.p) ^ R := by
  have hq1 := one_le_q_sq F
  have hp1 := one_le_p F
  rw [mul_pow]
  exact mul_le_mul (pow_le_pow_right₀ hq1 ha) (pow_le_pow_right₀ hp1 hb) (by positivity)
    (by positivity)

/-- Scale bound at points within `R` steps of a point of the corner fibre (`corner_scale_near_le` of tao-collatz). -/
theorem corner_scale_near_le {R : ℕ} {θs : ℝ} {a b ap bp : ℕ}
    (hscale : ((F.q : ℝ) ^ 2) ^ ap * (F.p : ℝ) ^ bp * |θs| ≤ ε)
    (ha : a ≤ ap + R) (hb : b ≤ bp + R) :
    ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b * |θs| ≤ ((F.q : ℝ) ^ 2 * F.p) ^ R * ε := by
  have hq1 := one_le_q_sq F
  have hp1 := one_le_p F
  have h9 : ((F.q : ℝ) ^ 2) ^ a ≤ ((F.q : ℝ) ^ 2) ^ (ap + R) := pow_le_pow_right₀ hq1 ha
  have h2 : (F.p : ℝ) ^ b ≤ (F.p : ℝ) ^ (bp + R) := pow_le_pow_right₀ hp1 hb
  calc ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b * |θs|
      ≤ ((F.q : ℝ) ^ 2) ^ (ap + R) * (F.p : ℝ) ^ (bp + R) * |θs| := by gcongr
    _ = ((F.q : ℝ) ^ 2 * F.p) ^ R * (((F.q : ℝ) ^ 2) ^ ap * (F.p : ℝ) ^ bp * |θs|) := by
        rw [pow_add, pow_add, mul_pow]; ring
    _ ≤ ((F.q : ℝ) ^ 2 * F.p) ^ R * ε := by gcongr

/-- Points within `R` steps of a point of the corner fibre are weakly black (`(q²p)^R ε ≤ w`). -/
theorem wb_of_corner_scale_near {R J : ℕ} {L : ℤ} {a b ap bp : ℕ}
    (hR : ((F.q : ℝ) ^ 2 * F.p) ^ R * ε ≤ wth F)
    (hscale : ((F.q : ℝ) ^ 2) ^ ap * (F.p : ℝ) ^ bp * |th F n c J L| ≤ ε)
    (ha : a ≤ ap + R) (hb : b ≤ bp + R) :
    wb F n c (J + a) (L - b) := by
  have hnear := corner_scale_near_le hscale ha hb
  have hphase := th_iterate_abs_le F n c J L a b
  show |th F n c (J + a) (L - b)| ≤ wth F
  linarith

/-- **Claim (*)** (`black_near_black_mem_corner` of tao-collatz): for a black point `x` of the strip and a black point `y`
within `R` in each coordinate, `y` lies in the corner triangle of `x` (`(q²p)^R ε ≤ w`). -/
theorem black_near_black_mem_corner (H : Hyp F n c ε) {R : ℕ}
    (hR : ((F.q : ℝ) ^ 2 * F.p) ^ R * ε ≤ wth F)
    {x y : ℕ × ℤ} (hx2j : 2 * x.1 + 2 * F.edgeB + 2 ≤ n) (hxb : F.black n c ε x.1 x.2)
    (hyb : F.black n c ε y.1 y.2)
    (hxy1 : x.1 ≤ y.1 + R) (hyx1 : y.1 ≤ x.1 + R) (hxy2 : x.2 ≤ y.2 + R) (hyx2 : y.2 ≤ x.2 + R) :
    y ∈ F.triangle (jstar F n c ε x.1 x.2) (lstar F n c ε x.1 x.2)
      (cornerSize F n c ε x.1 x.2) := by
  set J := jstar F n c ε x.1 x.2 with hJ
  set L := lstar F n c ε x.1 x.2 with hL
  set ap := x.1 - J with hap
  set bp := (L - x.2).toNat with hbp
  have hJp : J ≤ x.1 := jstar_le x.1 x.2
  have hpL : x.2 ≤ L := le_lstar H hx2j hxb
  have hscale : ((F.q : ℝ) ^ 2) ^ ap * (F.p : ℝ) ^ bp * |th F n c J L| ≤ ε :=
    fibre_le_eps H hx2j hxb
  have hθ : 0 < |th F n c J L| := corner_phase_pos H hx2j
  have hw8 := wth_le F
  have hq1 := one_le_q_sq F
  have hp1 := one_le_p F
  have hεw := H.le_w
  have hyb' : |th F n c y.1 y.2| ≤ ε := hyb
  by_cases hyJ : J ≤ y.1
  · by_cases hyL : y.2 ≤ L
    · -- Case 1: below and to the right of the apex
      set aq := y.1 - J with haq
      set bq := (L - y.2).toNat with hbq
      have hyj : J + aq = y.1 := by omega
      have hyl : L - (bq : ℤ) = y.2 := by omega
      have hnear := corner_scale_near_le hscale (show aq ≤ ap + R by omega)
        (show bq ≤ bp + R by omega)
      have hsmall : ((F.q : ℝ) ^ 2) ^ aq * (F.p : ℝ) ^ bq * |th F n c J L| < 1 / 2 := by
        linarith
      have heq := th_iterate_exact F n c J L aq bq hsmall
      have hscaleq : ((F.q : ℝ) ^ 2) ^ aq * (F.p : ℝ) ^ bq * |th F n c J L| ≤ ε := by
        have habs : |th F n c (J + aq) (L - bq)|
            = ((F.q : ℝ) ^ 2) ^ aq * (F.p : ℝ) ^ bq * |th F n c J L| := by
          rw [heq, abs_mul, abs_mul,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((F.q : ℝ) ^ 2) ^ aq),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (F.p : ℝ) ^ bq)]
        rw [← habs, hyj, hyl]
        exact hyb'
      have hmem := (mem_triangle_iff_scale (F := F) H.pos hθ hyJ hyL).mpr hscaleq
      unfold cornerSize
      simpa using hmem
    · -- Case 2: above the apex
      have hLy : L + 1 ≤ y.2 := by omega
      set b := (y.2 - (L + 1)).toNat with hb
      have hbR : b ≤ R := by omega
      have hheight : y.2 - (b : ℤ) = L + 1 := by omega
      have htop : wb F n c y.1 (L + 1) := by
        show |th F n c y.1 (L + 1)| ≤ wth F
        rw [← hheight]
        have h0 := th_iterate_abs_le F n c y.1 y.2 0 b
        simp only [add_zero, pow_zero, one_mul] at h0
        have hK := pow_le_KR (F := F) (a := 0) (b := b) (R := R) (by omega) hbR
        simp only [pow_zero, one_mul] at hK
        calc |th F n c y.1 (y.2 - b)| ≤ (F.p : ℝ) ^ b * |th F n c y.1 y.2| := h0
          _ ≤ (F.p : ℝ) ^ b * ε := mul_le_mul_of_nonneg_left hyb' (by positivity)
          _ ≤ ((F.q : ℝ) ^ 2 * F.p) ^ R * ε :=
              mul_le_mul_of_nonneg_right hK H.pos.le
          _ ≤ wth F := hR
      have hxTopWhite : ¬ F.black n c ε x.1 (L + 1) := white_above_lstar H hx2j
      rcases le_or_gt x.1 y.1 with hxy | hyx
      · have hbase : ∀ j'', x.1 ≤ j'' → j'' < y.1 → wb F n c j'' L := by
          intro j'' hj1 hj2
          set a := j'' - J with ha
          have hja : J + a = j'' := by omega
          have hw := wb_of_corner_scale_near (F := F) (n := n) (c := c) (J := J) (L := L)
            (a := a) (b := 0) hR hscale (by omega) (by omega)
          simpa [hja] using hw
        have hxWeak := wb_row_left_of_weak_base hxy hbase htop
        exact False.elim (hxTopWhite (black_of_wb_pred_l hxWeak (by
          rw [show L + 1 - 1 = L from by ring]
          exact black_of_le_lstar H hx2j hpL le_rfl)))
      · have hrow : ∀ j'', y.1 ≤ j'' → j'' ≤ x.1 → F.black n c ε j'' L := by
          intro j'' hj1 hj2
          exact black_of_jstar_le H hx2j hxb (by omega) hj2
        have hxWeak := wb_row_right H.le_w hrow htop x.1 (by omega) (by omega)
        exact False.elim (hxTopWhite (black_of_wb_pred_l hxWeak (by
          rw [show L + 1 - 1 = L from by ring]
          exact black_of_le_lstar H hx2j hpL le_rfl)))
  · -- Case 3: to the left of the apex
    have hyJ' : y.1 < J := by omega
    have hJpos : 1 ≤ J := by omega
    set a := (J - 1) - y.1 with ha
    have haR : a ≤ R := by omega
    have hcol : y.1 + a = J - 1 := by omega
    have hleftAtY : wb F n c (J - 1) y.2 := by
      show |th F n c (J - 1) y.2| ≤ wth F
      rw [← hcol]
      have h0 := th_iterate_abs_le F n c y.1 y.2 a 0
      simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one] at h0
      have hK := pow_le_KR (F := F) (a := a) (b := 0) (R := R) haR (by omega)
      simp only [pow_zero, mul_one] at hK
      calc |th F n c (y.1 + a) y.2| ≤ ((F.q : ℝ) ^ 2) ^ a * |th F n c y.1 y.2| := h0
        _ ≤ ((F.q : ℝ) ^ 2) ^ a * ε := mul_le_mul_of_nonneg_left hyb' (by positivity)
        _ ≤ ((F.q : ℝ) ^ 2 * F.p) ^ R * ε := mul_le_mul_of_nonneg_right hK H.pos.le
        _ ≤ wth F := hR
    have hcornerBlack : F.black n c ε J L := black_of_jstar_le H hx2j hxb le_rfl hJp
    have hleftWhite : ¬ F.black n c ε (J - 1) L := by
      have hm := jstar_maximal H hx2j hxb
      exact hm.resolve_left (by omega)
    by_cases hLy : L ≤ y.2
    · set b := (y.2 - L).toNat with hb
      have hbR : b ≤ R := by omega
      have htarget : y.2 - (b : ℤ) = L := by omega
      have hweak : wb F n c (J - 1) L := by
        show |th F n c (J - 1) L| ≤ wth F
        rw [← hcol, ← htarget]
        have hK := pow_le_KR (F := F) haR hbR
        calc |th F n c (y.1 + a) (y.2 - b)|
            ≤ ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b * |th F n c y.1 y.2| :=
              th_iterate_abs_le F n c y.1 y.2 a b
          _ ≤ ((F.q : ℝ) ^ 2) ^ a * (F.p : ℝ) ^ b * ε :=
              mul_le_mul_of_nonneg_left hyb' (by positivity)
          _ ≤ ((F.q : ℝ) ^ 2 * F.p) ^ R * ε := mul_le_mul_of_nonneg_right hK H.pos.le
          _ ≤ wth F := hR
      exact False.elim (hleftWhite (black_of_wb_succ_j hweak (by
        rwa [show (J - 1) + 1 = J from by omega])))
    · have hyL : y.2 < L := by omega
      set t := (L - y.2).toNat with ht
      have htarget : y.2 + (t : ℤ) = L := by omega
      have hright : ∀ i : ℕ, i < t → wb F n c J (y.2 + (i + 1)) := by
        intro i hi
        set b := (L - (y.2 + (i + 1))).toNat with hb
        have hz : L - (b : ℤ) = y.2 + (i + 1) := by omega
        have hw := wb_of_corner_scale_near (F := F) (n := n) (c := c) (J := J) (L := L)
          (a := 0) (b := b) hR hscale (by omega) (by omega)
        simpa [hz] using hw
      have hweak := wb_col_up_of_weak_right t hJpos hleftAtY hright
      rw [htarget] at hweak
      exact False.elim (hleftWhite (black_of_wb_succ_j hweak (by
        rwa [show (J - 1) + 1 = J from by omega])))

end Near

/-! ### Distance from the edge -/

section Confined

variable {F} {n : ℕ} {c : ℤ} {ε : ℝ} {j : ℕ} {l : ℤ}

/-- **Distance of the corner triangle from the edge** (`corner_triangle_confined` of tao-collatz):
points of the corner triangle satisfy `j + 1 ≤ (n/2 - B) - sep ε`. -/
theorem corner_triangle_confined (H : Hyp F n c ε) (S : Small F ε)
    (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n) {x : ℕ × ℤ}
    (hx : x ∈ F.triangle (jstar F n c ε j l) (lstar F n c ε j l) (cornerSize F n c ε j l)) :
    (x.1 : ℝ) + 1 ≤ ((n / 2 - F.edgeB : ℕ) : ℝ) - F.sep ε := by
  obtain ⟨hj1, hl1, hlog⟩ := hx
  set J := jstar F n c ε j l with hJ
  set Ls := lstar F n c ε j l with hLs
  set θs : ℝ := th F n c J Ls with hθs
  have hjj : J ≤ j := jstar_le j l
  have h2J : 2 * J + 2 * F.edgeB + 2 ≤ n := by omega
  have hθpos : 0 < |θs| := corner_phase_pos H h2j
  have hlq := log_q_pos F
  have hq0 : 0 < F.q := F.q_pos
  -- logarithm of the corner lower bound: `-log|θ*| ≤ (n - 2J) log q`
  have hlb : 1 / (F.q : ℝ) ^ (n - 2 * J) ≤ |θs| := th_lower_bound F H.hc Ls h2J
  have hloglb : -Real.log |θs| ≤ ((n - 2 * J : ℕ) : ℝ) * Real.log F.q := by
    have h1 : Real.log (1 / (F.q : ℝ) ^ (n - 2 * J)) ≤ Real.log |θs| :=
      Real.log_le_log (by positivity) hlb
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_pow] at h1
    linarith
  set Lε := Real.log (1 / ε) with hLε
  have hlogε : Real.log ε = -Lε := by rw [hLε, one_div, Real.log_inv, neg_neg]
  have hsize : ((x.1 : ℝ) - (J : ℝ)) * Real.log ((F.q : ℝ) ^ 2)
      ≤ -Lε + ((n - 2 * J : ℕ) : ℝ) * Real.log F.q := by
    have hlogp : (0 : ℝ) ≤ ((Ls : ℝ) - (x.2 : ℝ)) * Real.log F.p := by
      apply mul_nonneg _ (Real.log_nonneg (one_le_p F))
      have : (x.2 : ℝ) ≤ (Ls : ℝ) := by exact_mod_cast hl1
      linarith
    have hsplit : cornerSize F n c ε j l = -Lε - Real.log |θs| := by
      unfold cornerSize
      rw [Real.log_div S.pos.ne' hθpos.ne', hlogε]
    rw [hsplit] at hlog
    linarith [hloglb]
  have hlogq2 : Real.log ((F.q : ℝ) ^ 2) = 2 * Real.log F.q := by
    rw [Real.log_pow]; push_cast; ring
  have hcastk : ((n - 2 * J : ℕ) : ℝ) = (n : ℝ) - 2 * (J : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 2 * J ≤ n)]; ring
  rw [hlogq2, hcastk] at hsize
  -- `x.1 ≤ n/2 - Lε/(2 log q)`
  have hx1 : (x.1 : ℝ) ≤ (n : ℝ) / 2 - Lε / (2 * Real.log F.q) := by
    have h2 : 2 * Real.log F.q * (x.1 : ℝ) ≤ (n : ℝ) * Real.log F.q - Lε := by nlinarith
    have e : (n : ℝ) / 2 - Lε / (2 * Real.log F.q)
        = ((n : ℝ) * Real.log F.q - Lε) / (2 * Real.log F.q) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  -- lower bound on `n/2 - B`
  have hB : F.edgeB ≤ n / 2 := by omega
  have hhalf : ((n / 2 - F.edgeB : ℕ) : ℝ) = ((n / 2 : ℕ) : ℝ) - F.edgeB := by
    rw [Nat.cast_sub hB]
  have hn2 : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
    have hn : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hn
    linarith
  have hconf := S.conf
  rw [hhalf]
  linarith

/-- Points of the corner triangle lie in the strip: `2 x.1 + 2B + 2 ≤ n`. -/
theorem corner_triangle_strip (H : Hyp F n c ε) (S : Small F ε)
    (h2j : 2 * j + 2 * F.edgeB + 2 ≤ n) {x : ℕ × ℤ}
    (hx : x ∈ F.triangle (jstar F n c ε j l) (lstar F n c ε j l) (cornerSize F n c ε j l)) :
    2 * x.1 + 2 * F.edgeB + 2 ≤ n := by
  have hreal := corner_triangle_confined H S h2j hx
  have hsep : 0 ≤ F.sep ε := by
    have h := S.conf
    have hlq := log_q_pos F
    have hL : 0 ≤ Real.log (1 / ε) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ S.pos]
      have := wth_le F
      linarith [S.le_w]
    unfold Family.sep
    exact mul_nonneg (sepc_pos F).le hL
  have h1 : (x.1 : ℝ) + 1 ≤ ((n / 2 - F.edgeB : ℕ) : ℝ) := by linarith
  have h2 : x.1 + 1 ≤ n / 2 - F.edgeB := by exact_mod_cast h1
  omega

end Confined

end Tri

end Family

end GGMCollatz
