import GGMCollatz.Tao.Sec7.FWEnc

/-!
# GGM §7: the deterministic encounter statement ((7.67) of tao-collatz)

Derived from gotrevor/tao-collatz (Apache-2.0), commit 15efca2, file `TaoCollatz/Sec7/Case3.lean`
(`encWindowIter`, `deterministic_encounter_claim_at`, `few_white_pointwise_dichotomy`);
generalized to the GGM family (p, q, r). Modified.

* `encWindowIter A K i`: an upper bound on the time of the `i`-th encounter (iterating windows of length `⌈4^A(1+p)³⌉ + K + 2`).
* `deterministic_encounter_claim` ((7.67)): a walk that stays in the deep strip, does not meet at time `p` a triangle of size `≥ 4^A(1+p)³`,
  and has `≤ K` white points, has `R` encounters. Proved.
  Outline of the proof: after an encounter, the barrier (the top of a triangle of size `< 4^A(1+p)³`) lies at height `≤ s_Δ/log p` above,
  and the height rises by `≥ 3` per step, so it is crossed within `⌈4^A(1+p)³⌉` steps. Among the following `K + 2` steps there is a non-white point
  (in the deep strip, a point whose phase point lies in `T.blk`), and an encounter occurs there.
* `few_white_pointwise_dichotomy`: a deep walk with few white points either has `R` encounters (`cumWhite ≤ K+1`)
  or meets a large triangle. Proved (from the statement above).
-/

open scoped ENNReal

namespace GGMCollatz

namespace Family

namespace FW

/-- Iteration of the window length (`encWindowIter` of tao-collatz). -/
noncomputable def encWindowIter (A : ℝ) (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => encWindowIter A K i
      + (⌈(4 : ℝ) ^ A * (1 + (encWindowIter A K i : ℝ)) ^ 3⌉₊ + K + 2)

theorem encWindowIter_succ (A : ℝ) (K i : ℕ) :
    encWindowIter A K (i + 1) = encWindowIter A K i
      + (⌈(4 : ℝ) ^ A * (1 + (encWindowIter A K i : ℝ)) ^ 3⌉₊ + K + 2) := rfl

theorem encWindowIter_mono (A : ℝ) (K : ℕ) {i j : ℕ} (h : i ≤ j) :
    encWindowIter A K i ≤ encWindowIter A K j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simp
  | succ k IH =>
    rw [show i + (k + 1) = (i + k) + 1 from rfl, encWindowIter_succ]
    omega

variable (F : Family)

/-! ### Stopped states and the envelope of their barriers -/

/-- One-step extension of the partial sums of a walk. -/
theorem pathSum_succ_of_lt {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) {p : ℕ} (hp : p < Tw) :
    pathSum v (p + 1) = pathSum v p + v ⟨p, hp⟩ := by
  rw [pathSum, pathSum, List.take_add_one, List.sum_append]
  congr 1
  have h : (List.ofFn v)[p]? = some (v ⟨p, hp⟩) := by
    rw [List.getElem?_eq_getElem (by simpa using hp)]
    simp
  rw [h]
  simp

/-- The state after the first `p` steps (`encFoldAt` of tao-collatz). -/
noncomputable def encFoldAt {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) (p : ℕ) : EncState :=
  ((List.ofFn v).take p).foldl (encStep F T R g) (encInit q₀.1 q₀.2)

variable {F}

theorem encFoldAt_succ {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) {p : ℕ} (hp : p < Tw) :
    encFoldAt F T R g q₀ v (p + 1)
      = encStep F T R g (encFoldAt F T R g q₀ v p) (v ⟨p, hp⟩) := by
  rw [encFoldAt, encFoldAt, List.take_add_one,
    List.getElem?_eq_getElem (by simpa using hp)]
  simp [List.foldl_append]

theorem encFoldAt_top {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) :
    encFoldAt F T R g q₀ v Tw
      = (List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2) := by
  rw [encFoldAt, List.take_of_length_le (by simp)]

theorem encFoldAt_pos {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) (p : ℕ) :
    (encFoldAt F T R g q₀ v p).pos = q₀ + pathSum v p := by
  rw [encFoldAt, encFold_pos, pathSum]
  rfl

theorem encFoldAt_count_mono {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) {p p' : ℕ} (h : p ≤ p') (hp' : p' ≤ Tw) :
    (encFoldAt F T R g q₀ v p).count ≤ (encFoldAt F T R g q₀ v p').count := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => simp
  | succ k IH =>
    rw [show p + (k + 1) = (p + k) + 1 from rfl,
      encFoldAt_succ T R g q₀ v (show p + k < Tw by omega)]
    exact le_trans (IH (by omega)) (encStep_count_le T R g _ _)

theorem encStep_barrier_of_count_eq {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (st : EncState) (d : ℕ × ℤ)
    (h : (encStep F T R g st d).count = st.count) :
    (encStep F T R g st d).barrier = st.barrier := by
  unfold encStep at h ⊢
  split at h
  · exfalso
    dsimp only at h
    omega
  · rename_i hq
    rw [if_neg hq]

theorem encFoldAt_barrier_of_count_eq {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) {p p' : ℕ} (h : p ≤ p') (hp' : p' ≤ Tw)
    (hcnt : (encFoldAt F T R g q₀ v p').count = (encFoldAt F T R g q₀ v p).count) :
    (encFoldAt F T R g q₀ v p').barrier = (encFoldAt F T R g q₀ v p).barrier := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => rfl
  | succ k IH =>
    have hpk : p + k < Tw := by omega
    have hmono1 := encFoldAt_count_mono T R g q₀ v (show p ≤ p + k by omega)
      (show p + k ≤ Tw by omega)
    have hstep := encStep_count_le T R g (encFoldAt F T R g q₀ v (p + k)) (v ⟨p + k, hpk⟩)
    rw [show p + (k + 1) = (p + k) + 1 from rfl, encFoldAt_succ T R g q₀ v hpk] at hcnt ⊢
    have hflat : (encStep F T R g (encFoldAt F T R g q₀ v (p + k)) (v ⟨p + k, hpk⟩)).count
        = (encFoldAt F T R g q₀ v (p + k)).count := by omega
    rw [encStep_barrier_of_count_eq T R g _ _ hflat]
    exact IH (by omega) (by omega : (encFoldAt F T R g q₀ v (p + k)).count
      = (encFoldAt F T R g q₀ v p).count)

/-- A walk on the support advances the column by `≥ 1` per step. -/
theorem pathSum_fst_ge {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) (hv : ∀ i, v i ∈ F.hold.support) :
    ∀ (p k : ℕ), p + k ≤ Tw → (pathSum v p).1 + k ≤ (pathSum v (p + k)).1 := by
  intro p k
  induction k with
  | zero => intro _; simp
  | succ k IH =>
    intro hk
    have hpk : p + k < Tw := by omega
    rw [show p + (k + 1) = (p + k) + 1 from rfl, pathSum_succ_of_lt v hpk]
    have h1 := F.hold_support_fst_pos _ (hv ⟨p + k, hpk⟩)
    have h2 := IH (by omega)
    show (pathSum v p).1 + (k + 1) ≤ (pathSum v (p + k)).1 + (v ⟨p + k, hpk⟩).1
    omega

/-- A walk on the support raises the height by `≥ 3` per step. -/
theorem pathSum_snd_ge {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) (hv : ∀ i, v i ∈ F.hold.support) :
    ∀ (p k : ℕ), p + k ≤ Tw → (pathSum v p).2 + 3 * k ≤ (pathSum v (p + k)).2 := by
  intro p k
  induction k with
  | zero => intro _; simp
  | succ k IH =>
    intro hk
    have hpk : p + k < Tw := by omega
    rw [show p + (k + 1) = (p + k) + 1 from rfl, pathSum_succ_of_lt v hpk]
    have h1 := F.hold_support_snd_ge _ (hv ⟨p + k, hpk⟩)
    have h2 := IH (by omega)
    show (pathSum v p).2 + 3 * ((k : ℤ) + 1) ≤ (pathSum v (p + k)).2 + (v ⟨p + k, hpk⟩).2
    linarith

/-- In the strip (`1 ≤ q₁ ≤ half`), the phase point of a non-white point lies in a triangle. -/
theorem blk_of_notMem_whiteStrip {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) {q : ℕ × ℤ}
    (h1 : 1 ≤ q.1) (h2 : q.1 ≤ half) (h : q ∉ whiteStrip half T.W) :
    (q.1 - 1, q.2) ∈ T.blk := by
  by_contra hb
  exact h ⟨h2, h1, hb⟩

/-- Height extent of a triangle: `(l₀ - q₂) log p ≤ s`. -/
theorem triangle_top_le {j₀ : ℕ} {l₀ : ℤ} {s : ℝ} {q : ℕ × ℤ}
    (hq : q ∈ F.triangle j₀ l₀ s) : ((l₀ - q.2 : ℤ) : ℝ) * Real.log F.p ≤ s := by
  obtain ⟨hj, hl, hlin⟩ := hq
  have hj' : (j₀ : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast hj
  have hq1 : (1 : ℝ) ≤ (F.q : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ F.q := by exact_mod_cast F.q_pos
    nlinarith
  have hcol : (0 : ℝ) ≤ ((q.1 : ℝ) - j₀) * Real.log ((F.q : ℝ) ^ 2) :=
    mul_nonneg (by linarith) (Real.log_nonneg hq1)
  push_cast
  linarith

open Classical in
/-- **Envelope of the barrier** (`encFoldAt_barrier_le` of tao-collatz): the barrier is not more than `2·4^A(1+p)³`
above the current height. -/
theorem encFoldAt_barrier_le {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (q₀ : ℕ × ℤ) {Tw : ℕ} (v : Fin Tw → ℕ × ℤ) (hv : ∀ i, v i ∈ F.hold.support)
    (A : ℝ) (hA : 0 ≤ A)
    (hsmall : ∀ p, p ≤ Tw → ∀ t ∈ T.T,
      ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ F.triangle t.1 t.2.1 t.2.2 →
      t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3) :
    ∀ p, p ≤ Tw →
      (((encFoldAt F T R g q₀ v p).barrier : ℝ))
        ≤ ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 2 * (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := by
  have h4A : (1 : ℝ) ≤ (4 : ℝ) ^ A := Real.one_le_rpow (by norm_num) hA
  intro p
  induction p with
  | zero =>
    intro _
    have hb : (encFoldAt F T R g q₀ v 0).barrier = q₀.2 := rfl
    have hz : (pathSum v 0).2 = 0 := by simp
    rw [hb, hz]
    push_cast
    nlinarith
  | succ p IH =>
    intro hp1
    have hp : p ≤ Tw := by omega
    have hplt : p < Tw := by omega
    rw [encFoldAt_succ T R g q₀ v hplt]
    have hgrow : ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 2 * (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3
        ≤ ((q₀.2 + (pathSum v (p + 1)).2 : ℤ) : ℝ)
          + 2 * (4 : ℝ) ^ A * (1 + ((p + 1 : ℕ) : ℝ)) ^ 3 := by
      have hht := pathSum_snd_ge v hv p 1 (by omega)
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      have hcube : (1 + (p : ℝ)) ^ 3 ≤ (1 + ((p + 1 : ℕ) : ℝ)) ^ 3 := by
        push_cast
        nlinarith
      have h2A : (0 : ℝ) ≤ 2 * (4 : ℝ) ^ A := by linarith
      have := mul_le_mul_of_nonneg_left hcube h2A
      have hht' : ((pathSum v p).2 : ℝ) + 3 ≤ ((pathSum v (p + 1)).2 : ℝ) := by
        exact_mod_cast hht
      have hhtR : ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ)
          ≤ ((q₀.2 + (pathSum v (p + 1)).2 : ℤ) : ℝ) := by
        push_cast
        linarith
      calc ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 2 * (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3
          ≤ ((q₀.2 + (pathSum v (p + 1)).2 : ℤ) : ℝ)
            + 2 * (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := by linarith
        _ ≤ _ := by linarith [this]
    unfold encStep
    split
    case isTrue hcond =>
      dsimp only
      set q : ℕ × ℤ := (encFoldAt F T R g q₀ v p).pos + v ⟨p, hplt⟩ with hq
      have hqpos : q = q₀ + pathSum v (p + 1) := by
        rw [hq, encFoldAt_pos, pathSum_succ_of_lt v hplt, add_assoc]
      obtain ⟨htmem, htcov⟩ := covTri_spec F T hcond.2.2.1
      set t := covTri F T (q.1 - 1, q.2) with ht
      have hsize : t.2.2 < (4 : ℝ) ^ A * (1 + ((p : ℝ) + 1)) ^ 3 := by
        have := hsmall (p + 1) hp1 t htmem (by rw [← hqpos]; exact htcov)
        push_cast at this ⊢
        linarith
      have hext : ((t.2.1 - q.2 : ℤ) : ℝ) * Real.log F.p ≤ t.2.2 :=
        triangle_top_le (q := (q.1 - 1, q.2)) htcov
      have hlogp : (1 / 2 : ℝ) < Real.log F.p := by
        have h2 : Real.log 2 ≤ Real.log F.p :=
          Real.log_le_log (by norm_num) (by exact_mod_cast F.two_le_p)
        have := Real.log_two_gt_d9
        linarith
      have htop : ((t.2.1 : ℤ) : ℝ) ≤ (q.2 : ℝ) + 2 * t.2.2 := by
        rcases le_or_gt t.2.1 q.2 with hle | hgt
        · have h0 : (0 : ℝ) ≤ t.2.2 := T.size_nonneg t htmem
          have : ((t.2.1 : ℤ) : ℝ) ≤ ((q.2 : ℤ) : ℝ) := by exact_mod_cast hle
          linarith
        · have hpos : (0 : ℝ) < ((t.2.1 - q.2 : ℤ) : ℝ) := by
            have : (0 : ℤ) < t.2.1 - q.2 := by omega
            exact_mod_cast this
          have hkey := mul_lt_mul_of_pos_left hlogp hpos
          push_cast at hext hpos hkey ⊢
          nlinarith
      have hq2 : (q.2 : ℝ) = ((q₀.2 + (pathSum v (p + 1)).2 : ℤ) : ℝ) := by
        rw [hqpos]
        simp only [Prod.snd_add]
      have h4Ap : (0 : ℝ) ≤ (4 : ℝ) ^ A * (1 + ((p : ℝ) + 1)) ^ 3 := by positivity
      calc ((t.2.1 : ℤ) : ℝ) ≤ (q.2 : ℝ) + 2 * t.2.2 := htop
        _ ≤ (q.2 : ℝ) + 2 * ((4 : ℝ) ^ A * (1 + ((p : ℝ) + 1)) ^ 3) := by linarith
        _ = ((q₀.2 + (pathSum v (p + 1)).2 : ℤ) : ℝ)
            + 2 * (4 : ℝ) ^ A * (1 + ((p : ℝ) + 1)) ^ 3 := by rw [hq2]; ring
        _ ≤ _ := by
            push_cast
            linarith
    case isFalse hcond =>
      exact le_trans (IH hp) hgrow

open Classical in
/-- **One window step of (7.67)** (`encFoldAt_count_step` of tao-collatz). -/
theorem encFoldAt_count_step {half : ℕ} {σ : ℝ} (T : F.TriFam half σ) (R g : ℕ)
    (q₀ : ℕ × ℤ) (hq₀ : 1 ≤ q₀.1) {Tw : ℕ} (v : Fin Tw → ℕ × ℤ)
    (hv : ∀ i, v i ∈ F.hold.support) (A : ℝ) (hA : 0 ≤ A) (K : ℕ)
    (hdepth : ∀ p, p ≤ Tw → (q₀ + pathSum v p).1 + g ≤ half)
    (hsmall : ∀ p, p ≤ Tw → ∀ t ∈ T.T,
      ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ F.triangle t.1 t.2.1 t.2.2 →
      t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3)
    (hfew : (Finset.range Tw).sum
      (fun p => if q₀ + pathSum v (p + 1) ∈ whiteStrip half T.W then 1 else 0) ≤ K)
    {p : ℕ} (hp : p + (⌈(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌉₊ + K + 2) ≤ Tw) :
    (encFoldAt F T R g q₀ v p).count + 1
      ≤ (encFoldAt F T R g q₀ v (p + (⌈(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌉₊ + K + 2))).count := by
  set D : ℕ := ⌈(4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3⌉₊ with hD
  set W : ℕ := D + K + 2 with hW
  by_contra hcon
  push Not at hcon
  have hflat : ∀ r, p ≤ r → r ≤ p + W →
      (encFoldAt F T R g q₀ v r).count = (encFoldAt F T R g q₀ v p).count := by
    intro r h1 h2
    have hmono1 := encFoldAt_count_mono T R g q₀ v h1 (by omega)
    have hmono2 := encFoldAt_count_mono T R g q₀ v h2 (by omega)
    omega
  have hbar : ∀ r, p ≤ r → r ≤ p + W →
      (encFoldAt F T R g q₀ v r).barrier = (encFoldAt F T R g q₀ v p).barrier := by
    intro r h1 h2
    exact encFoldAt_barrier_of_count_eq T R g q₀ v h1 (by omega) (hflat r h1 h2)
  have henv := encFoldAt_barrier_le T R g q₀ v hv A hA hsmall p (by omega)
  have hclear : ∀ r, p + D + 1 ≤ r → r ≤ p + W →
      (encFoldAt F T R g q₀ v p).barrier < (q₀ + pathSum v r).2 := by
    intro r h1 h2
    have hht := pathSum_snd_ge v hv p (r - p) (by omega)
    rw [show p + (r - p) = r from by omega] at hht
    have hDge : ((4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3) ≤ (D : ℝ) :=
      Nat.le_ceil _
    have h4Apos : (0 : ℝ) ≤ (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := by positivity
    have hstrict : (((encFoldAt F T R g q₀ v p).barrier : ℤ) : ℝ)
        < (((q₀ + pathSum v r).2 : ℤ) : ℝ) := by
      have hrp : (D : ℝ) + 1 ≤ ((r - p : ℕ) : ℝ) := by
        have : D + 1 ≤ r - p := by omega
        exact_mod_cast this
      have hht' : ((pathSum v p).2 : ℝ) + 3 * ((r - p : ℕ) : ℝ)
          ≤ ((pathSum v r).2 : ℝ) := by exact_mod_cast hht
      have hh2 : ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 3 * ((r - p : ℕ) : ℝ)
          ≤ (((q₀ + pathSum v r).2 : ℤ) : ℝ) := by
        have hr2 : (q₀ + pathSum v r).2 = q₀.2 + (pathSum v r).2 := rfl
        rw [hr2]
        push_cast
        linarith
      calc (((encFoldAt F T R g q₀ v p).barrier : ℤ) : ℝ)
          ≤ ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ)
            + 2 * (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 := henv
        _ < ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 3 * ((D : ℝ) + 1) := by nlinarith
        _ ≤ ((q₀.2 + (pathSum v p).2 : ℤ) : ℝ) + 3 * ((r - p : ℕ) : ℝ) := by linarith
        _ ≤ _ := hh2
    exact_mod_cast hstrict
  have hpigeon : ∃ r, p + D + 1 ≤ r ∧ r ≤ p + D + K + 1 ∧
      q₀ + pathSum v r ∉ whiteStrip half T.W := by
    by_contra hall
    push Not at hall
    have hone : ∀ i ∈ Finset.range (K + 1),
        (if q₀ + pathSum v (p + D + i + 1) ∈ whiteStrip half T.W then 1 else 0) = 1 := by
      intro i hi
      simp only [Finset.mem_range] at hi
      exact if_pos (hall (p + D + i + 1) (by omega) (by omega))
    have hsub : (Finset.range (K + 1)).sum
        (fun i => if q₀ + pathSum v (p + D + i + 1) ∈ whiteStrip half T.W then 1 else 0)
        = K + 1 := by
      rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_range]
    have hinj : (Finset.range (K + 1)).sum
        (fun i => if q₀ + pathSum v (p + D + i + 1) ∈ whiteStrip half T.W then 1 else 0)
        ≤ (Finset.range Tw).sum
          (fun r => if q₀ + pathSum v (r + 1) ∈ whiteStrip half T.W then 1 else 0) := by
      have hmap : (Finset.range (K + 1)).sum
          (fun i => if q₀ + pathSum v (p + D + i + 1) ∈ whiteStrip half T.W then 1 else 0)
          = ((Finset.range (K + 1)).image (fun i => p + D + i)).sum
            (fun r => if q₀ + pathSum v (r + 1) ∈ whiteStrip half T.W then 1 else 0) := by
        rw [Finset.sum_image (by intro a _ b _ h; simp only [] at h; omega)]
      rw [hmap]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro r hr
      simp only [Finset.mem_image, Finset.mem_range] at hr ⊢
      obtain ⟨i, hi, rfl⟩ := hr
      show p + D + i < Tw
      omega
    omega
  obtain ⟨r, hr1, hr2, hrblack⟩ := hpigeon
  have hr0 : 1 ≤ r := by omega
  have hrT : r ≤ Tw := by omega
  have hcol : 1 ≤ (q₀ + pathSum v r).1 := by
    show 1 ≤ q₀.1 + (pathSum v r).1
    omega
  have hdeep := hdepth r hrT
  have hblack : ((q₀ + pathSum v r).1 - 1, (q₀ + pathSum v r).2) ∈ T.blk :=
    blk_of_notMem_whiteStrip T hcol (by omega) hrblack
  have hbarrier : (encFoldAt F T R g q₀ v (r - 1)).barrier < (q₀ + pathSum v r).2 := by
    rw [hbar (r - 1) (by omega) (by omega)]
    exact hclear r (by omega) (by omega)
  have hrstep : r - 1 < Tw := by omega
  have hposr : (encFoldAt F T R g q₀ v (r - 1)).pos + v ⟨r - 1, hrstep⟩
      = q₀ + pathSum v r := by
    rw [encFoldAt_pos, add_assoc]
    congr 1
    rw [← pathSum_succ_of_lt v hrstep]
    congr 1
    omega
  have hcount : (encFoldAt F T R g q₀ v r).count
      = (encFoldAt F T R g q₀ v (r - 1)).count + 1 := by
    have hstep : encFoldAt F T R g q₀ v r
        = encStep F T R g (encFoldAt F T R g q₀ v (r - 1)) (v ⟨r - 1, hrstep⟩) := by
      rw [← encFoldAt_succ T R g q₀ v hrstep]
      congr 1
      omega
    rw [hstep]
    unfold encStep
    rw [if_pos (by
      rw [hposr]
      exact ⟨hcol, hdeep, hblack, hbarrier⟩)]
  have hflat1 := hflat (r - 1) (by omega) (by omega)
  have hflat2 := hflat r (by omega) (by omega)
  omega

variable (F)

open Classical in
/-- **The deterministic encounter statement** (`deterministic_encounter_claim_at` of tao-collatz, (7.67)). -/
theorem deterministic_encounter_claim {half : ℕ} {σ : ℝ} (T : F.TriFam half σ)
    (g R K : ℕ) (A : ℝ) (hA : 1 ≤ A) (Tw : ℕ) (hT : encWindowIter A K R ≤ Tw)
    (q₀ : ℕ × ℤ) (hq₀ : 1 ≤ q₀.1) (v : Fin Tw → ℕ × ℤ) (hv : ∀ i, v i ∈ F.hold.support)
    (hdepth : ∀ p, p ≤ Tw → (q₀ + pathSum v p).1 + g ≤ half)
    (hsmall : ∀ p, p ≤ Tw → ∀ t ∈ T.T,
        ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ F.triangle t.1 t.2.1 t.2.2 →
        t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3)
    (hfew : (Finset.range Tw).sum
        (fun p => if q₀ + pathSum v (p + 1) ∈ whiteStrip half T.W then 1 else 0) ≤ K) :
    R ≤ ((List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2)).count := by
  have key : ∀ i, i ≤ R → i ≤ (encFoldAt F T R g q₀ v (encWindowIter A K i)).count := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i IH =>
      intro hiR
      have hle : encWindowIter A K (i + 1) ≤ Tw :=
        le_trans (encWindowIter_mono A K hiR) hT
      have hstep := encFoldAt_count_step (F := F) (R := R) (g := g) T q₀ hq₀ v hv A
        (by linarith) K hdepth hsmall hfew
        (p := encWindowIter A K i) (by rw [← encWindowIter_succ]; exact hle)
      rw [← encWindowIter_succ] at hstep
      exact le_trans (Nat.succ_le_succ (IH (by omega))) hstep
  have hmono := encFoldAt_count_mono T R g q₀ v hT (le_refl Tw)
  rw [encFoldAt_top] at hmono
  exact le_trans (key R (le_refl R)) hmono

open Classical in
/-- **Pointwise dichotomy** (`few_white_pointwise_dichotomy` of tao-collatz): a deep walk whose forward count of white points
`Σ_{p<P} 1[q₀ + pathSum v p is white]` is `≤ K` either has `R` encounters with `cumWhite ≤ K+1`, or
at some time `p ≤ P` its phase point enters a triangle of size `≥ 4^A(1+p)³`. -/
theorem few_white_pointwise_dichotomy {half : ℕ} {σ : ℝ} (T : F.TriFam half σ)
    (g R K : ℕ) (A : ℝ) (hA : 1 ≤ A) (P : ℕ) (hP : encWindowIter A (K + 1) R ≤ P)
    (q₀ : ℕ × ℤ) (hq₀ : 1 ≤ q₀.1) (v : Fin P → ℕ × ℤ) (hv : ∀ i, v i ∈ F.hold.support)
    (hdepth : ∀ p, p ≤ P → (q₀ + pathSum v p).1 + g ≤ half)
    (hmyNw : (∑ p ∈ Finset.range P,
        (if q₀ + pathSum v p ∈ whiteStrip half T.W then (1 : ℕ) else 0)) ≤ K) :
    (R ≤ ((List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2)).count
        ∧ ((List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K + 1)
    ∨ (∃ p, p ≤ P ∧ ∃ t ∈ T.T,
        ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ F.triangle t.1 t.2.1 t.2.2
        ∧ (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3 ≤ t.2.2) := by
  have hpos : (encInit q₀.1 q₀.2).pos = q₀ := rfl
  have hcum : ((List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2)).cumWhite
      = ∑ p ∈ Finset.range P,
          (if q₀ + pathSum v (p + 1) ∈ whiteStrip half T.W then (1 : ℕ) else 0) := by
    rw [encFold_cumWhite T R g P v (encInit q₀.1 q₀.2), hpos]
    simp only [encInit, zero_add]
  have hSple : (∑ p ∈ Finset.range P,
      (if q₀ + pathSum v (p + 1) ∈ whiteStrip half T.W then (1 : ℕ) else 0)) ≤ K + 1 := by
    have e1 : (∑ p ∈ Finset.range (P + 1),
          (if q₀ + pathSum v p ∈ whiteStrip half T.W then (1 : ℕ) else 0))
        = (∑ p ∈ Finset.range P,
            (if q₀ + pathSum v (p + 1) ∈ whiteStrip half T.W then (1 : ℕ) else 0))
          + (if q₀ + pathSum v 0 ∈ whiteStrip half T.W then (1 : ℕ) else 0) :=
      Finset.sum_range_succ' _ P
    have e2 : (∑ p ∈ Finset.range (P + 1),
          (if q₀ + pathSum v p ∈ whiteStrip half T.W then (1 : ℕ) else 0))
        = (∑ p ∈ Finset.range P,
            (if q₀ + pathSum v p ∈ whiteStrip half T.W then (1 : ℕ) else 0))
          + (if q₀ + pathSum v P ∈ whiteStrip half T.W then (1 : ℕ) else 0) :=
      Finset.sum_range_succ _ P
    have hb : (if q₀ + pathSum v P ∈ whiteStrip half T.W then (1 : ℕ) else 0) ≤ 1 := by
      split_ifs <;> omega
    omega
  have hcumK : ((List.ofFn v).foldl (encStep F T R g) (encInit q₀.1 q₀.2)).cumWhite ≤ K + 1 := by
    rw [hcum]; exact hSple
  by_cases hE : ∀ p, p ≤ P → ∀ t ∈ T.T,
      ((q₀ + pathSum v p).1 - 1, (q₀ + pathSum v p).2) ∈ F.triangle t.1 t.2.1 t.2.2 →
      t.2.2 < (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3
  · exact Or.inl ⟨deterministic_encounter_claim F T g R (K + 1) A hA P hP q₀ hq₀ v hv
      hdepth hE hSple, hcumK⟩
  · refine Or.inr ?_
    push Not at hE
    obtain ⟨p, hp, t, ht, hmem, hbig⟩ := hE
    exact ⟨p, hp, t, ht, hmem, hbig⟩

end FW

end Family

end GGMCollatz
