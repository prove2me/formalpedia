-- Prove2me | solution 1 for ConvexOptimization.lowner_john_ball_subset_hull_of_kkt
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T03:42:25.688001+00:00
-- url     : https://prove2.me/submissions/dbd3536d-39d9-43a6-91f1-8a24acc748d1

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open Matrix

theorem solution {nn m : ℕ} (hnn : 0 < nn)
    (x : Fin m → Fin nn → ℝ) (lam : Fin m → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hI : (∑ i, lam i • Matrix.vecMulVec (x i) (x i)) = (1 : Matrix (Fin nn) (Fin nn) ℝ))
    (hz : (∑ i, lam i • x i) = 0)
    (hcs : ∀ i, lam i * (1 - x i ⬝ᵥ x i) = 0)
    (v : Fin nn → ℝ) (hv : v ⬝ᵥ v ≤ 1 / (nn : ℝ) ^ 2) :
    v ∈ convexHull ℝ (Set.range x) := by
  by_contra hvnot
  have hnnR : (0 : ℝ) < (nn : ℝ) := by exact_mod_cast hnn
  -- Strictly separate `v` from the (compact, convex) hull.
  have hKc : IsCompact (convexHull ℝ (Set.range x)) := (Set.finite_range x).isCompact_convexHull (𝕜 := ℝ)
  obtain ⟨F, u0, hFlt, hFu⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ (Set.range x)) hKc.isClosed hvnot
  -- Represent the separating functional as a dot product.
  set c : Fin nn → ℝ := fun j => F (Pi.single j 1) with hc
  have hFrep : ∀ y : Fin nn → ℝ, F y = y ⬝ᵥ c := by
    intro y
    have hy : (∑ j, Pi.single j (y j) : Fin nn → ℝ) = y := Finset.univ_sum_single y
    calc F y = F (∑ j, Pi.single j (y j)) := by rw [hy]
      _ = ∑ j, F (Pi.single j (y j)) := map_sum _ _ _
      _ = ∑ j, y j * c j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have hsingle : (Pi.single j (y j) : Fin nn → ℝ) = y j • Pi.single j (1 : ℝ) := by
            ext k; by_cases h : k = j <;> simp [Pi.single_apply, h]
          rw [hsingle, map_smul, hc]
          simp [smul_eq_mul]
      _ = y ⬝ᵥ c := rfl
  set s : Fin m → ℝ := fun i => x i ⬝ᵥ c with hs
  set uu : ℝ := v ⬝ᵥ c with huu
  have hlt : ∀ i, s i < uu := by
    intro i
    have h1 : F (x i) < u0 := hFlt _ (subset_convexHull ℝ _ ⟨i, rfl⟩)
    have h2 := lt_trans h1 hFu
    rwa [hFrep, hFrep] at h2
  -- (1) `Σ λᵢ sᵢ = 0`, from `Σ λᵢ xᵢ = 0`.
  have hsum0 : ∑ i, lam i * s i = 0 := by
    have h : (∑ i, lam i • x i) ⬝ᵥ c = 0 := by rw [hz]; simp
    rw [sum_dotProduct] at h
    simpa [hs, smul_dotProduct, smul_eq_mul] using h
  -- (2) `Σ λᵢ sᵢ² = ⟪c, c⟫`, from `Σ λᵢ xᵢxᵢᵀ = I`.
  have hquad : ∑ i, lam i * s i ^ 2 = c ⬝ᵥ c := by
    have h1 : c ⬝ᵥ ((∑ i, lam i • Matrix.vecMulVec (x i) (x i)) *ᵥ c) = c ⬝ᵥ c := by
      rw [hI, Matrix.one_mulVec]
    rw [Matrix.sum_mulVec] at h1
    have h2 : ∀ i : Fin m, (lam i • Matrix.vecMulVec (x i) (x i)) *ᵥ c
        = (lam i * (x i ⬝ᵥ c)) • x i := by
      intro i
      ext j
      simp [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum, Finset.sum_mul,
        mul_comm, mul_assoc, mul_left_comm]
    rw [Finset.sum_congr rfl fun i _ => h2 i, dotProduct_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct_smul, smul_eq_mul, hs]
    have : c ⬝ᵥ x i = x i ⬝ᵥ c := dotProduct_comm _ _
    rw [this]
    ring
  -- (3) `Σ λᵢ = n`, from the trace of the same identity plus complementary slackness.
  have hcard : ∑ i, lam i = (nn : ℝ) := by
    have h1 : Matrix.trace (∑ i, lam i • Matrix.vecMulVec (x i) (x i)) = (nn : ℝ) := by
      rw [hI, Matrix.trace_one]; simp
    rw [Matrix.trace_sum] at h1
    have h2 : ∀ i : Fin m, Matrix.trace (lam i • Matrix.vecMulVec (x i) (x i))
        = lam i * (x i ⬝ᵥ x i) := by
      intro i; rw [Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul]
    have h3 : ∀ i : Fin m, lam i * (x i ⬝ᵥ x i) = lam i := by
      intro i
      have h := hcs i
      rw [mul_sub, mul_one, sub_eq_zero] at h
      exact h.symm
    rw [Finset.sum_congr rfl fun i _ => (h2 i).trans (h3 i)] at h1
    exact h1
  -- Set `w = ‖c‖`, so `sᵢ² ≤ w²` for active `i` and `n·uu ≤ w`.
  have hcc : (0 : ℝ) ≤ c ⬝ᵥ c := by
    simpa [dotProduct] using Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (c j)
  set w : ℝ := Real.sqrt (c ⬝ᵥ c) with hw
  have hw0 : (0 : ℝ) ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = c ⬝ᵥ c := Real.sq_sqrt hcc
  have hCS : ∀ a b : Fin nn → ℝ, (a ⬝ᵥ b) ^ 2 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
    intro a b
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
    simpa [dotProduct, sq] using h
  -- `uu > 0`.
  have hexists : ∃ i, 0 < lam i := by
    by_contra hno
    push_neg at hno
    have hzero : ∀ i, lam i = 0 := fun i => le_antisymm (hno i) (hlam i)
    rw [Finset.sum_congr rfl fun i _ => hzero i] at hcard
    simp at hcard
    exact absurd hcard.symm (ne_of_gt hnnR)
  have huupos : 0 < uu := by
    obtain ⟨i0, hi0⟩ := hexists
    have hlt2 : ∑ i, lam i * s i < ∑ i, lam i * uu :=
      Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hlt i).le (hlam i))
        ⟨i0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hlt i0) hi0⟩
    rw [hsum0, ← Finset.sum_mul, hcard] at hlt2
    nlinarith [hlt2, hnnR]
  -- `n · uu ≤ w`.
  have huuw : (nn : ℝ) * uu ≤ w := by
    have h1 : uu ^ 2 ≤ (c ⬝ᵥ c) * (v ⬝ᵥ v) := by
      have := hCS v c
      rw [huu]
      nlinarith [this, dotProduct_comm v c]
    have h2 : ((nn : ℝ) * uu) ^ 2 ≤ w ^ 2 := by
      have hle : (c ⬝ᵥ c) * (v ⬝ᵥ v) ≤ (c ⬝ᵥ c) * (1 / (nn : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hv hcc
      have hnn2 : (0 : ℝ) < (nn : ℝ) ^ 2 := by positivity
      have h3 : uu ^ 2 ≤ (c ⬝ᵥ c) * (1 / (nn : ℝ) ^ 2) := le_trans h1 hle
      have h4 : ((nn : ℝ) ^ 2) * uu ^ 2 ≤ ((nn : ℝ) ^ 2) * ((c ⬝ᵥ c) * (1 / (nn : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 hnn2.le
      have h5 : ((nn : ℝ) ^ 2) * ((c ⬝ᵥ c) * (1 / (nn : ℝ) ^ 2)) = c ⬝ᵥ c := by
        field_simp
      rw [hw2]
      nlinarith [h4, h5]
    nlinarith [h2, hw0, mul_nonneg hnnR.le huupos.le]
  -- Every term of `Σ λᵢ (sᵢ + w)(sᵢ − uu)` is ≤ 0, yet the sum is ≥ 0.
  have hsbound : ∀ i, 0 < lam i → -w ≤ s i := by
    intro i hi
    have hxx : x i ⬝ᵥ x i = 1 := by
      have h := hcs i
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (ne_of_gt hi)
      · linarith [sub_eq_zero.mp h']
    have h1 : s i ^ 2 ≤ w ^ 2 := by
      rw [hw2, hs]
      have := hCS (x i) c
      rw [hxx, one_mul] at this
      exact this
    nlinarith [h1, hw0]
  have hterm : ∀ i, lam i * ((s i + w) * (s i - uu)) ≤ 0 := by
    intro i
    rcases eq_or_lt_of_le (hlam i) with h | h
    · rw [← h]; simp
    · have h1 : 0 ≤ s i + w := by linarith [hsbound i h]
      have h2 : s i - uu < 0 := by linarith [hlt i]
      exact mul_nonpos_of_nonneg_of_nonpos h.le (mul_nonpos_of_nonneg_of_nonpos h1 h2.le)
  have hexpand : ∑ i, lam i * ((s i + w) * (s i - uu))
      = (∑ i, lam i * s i ^ 2) + (w - uu) * (∑ i, lam i * s i)
        - uu * w * (∑ i, lam i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsumzero : ∑ i, lam i * ((s i + w) * (s i - uu)) = 0 := by
    refine le_antisymm (Finset.sum_nonpos fun i _ => hterm i) ?_
    rw [hexpand, hquad, hsum0, hcard, ← hw2]
    nlinarith [huuw, hw0, huupos]
  -- Hence every active `sᵢ` equals `−w`, forcing `w = 0` and contradicting `uu > 0`.
  have heach : ∀ i, lam i * s i = lam i * (-w) := by
    intro i
    rcases eq_or_lt_of_le (hlam i) with h | h
    · rw [← h]; simp
    · have hz0 : lam i * ((s i + w) * (s i - uu)) = 0 :=
        le_antisymm (hterm i) (by
          have := (Finset.sum_eq_zero_iff_of_nonpos fun i _ => hterm i).mp hsumzero i
            (Finset.mem_univ i)
          exact le_of_eq this.symm)
      have h1 : (s i + w) * (s i - uu) = 0 := by
        rcases mul_eq_zero.mp hz0 with h' | h'
        · exact absurd h' (ne_of_gt h)
        · exact h'
      rcases mul_eq_zero.mp h1 with h' | h'
      · have : s i = -w := by linarith
        rw [this]
      · exact absurd h' (ne_of_lt (by linarith [hlt i] : s i - uu < 0))
  have hwzero : w = 0 := by
    have h1 : ∑ i, lam i * s i = ∑ i, lam i * (-w) :=
      Finset.sum_congr rfl fun i _ => heach i
    rw [hsum0, ← Finset.sum_mul, hcard] at h1
    have : (nn : ℝ) * (-w) = 0 := h1.symm
    have := mul_eq_zero.mp this
    rcases this with h' | h'
    · exact absurd h' (ne_of_gt hnnR)
    · linarith
  rw [hwzero] at huuw
  nlinarith [huuw, huupos, hnnR]
