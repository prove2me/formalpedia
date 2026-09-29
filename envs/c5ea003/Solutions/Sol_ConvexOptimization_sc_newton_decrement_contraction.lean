-- Prove2me | solution 1 for ConvexOptimization.sc_newton_decrement_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-17T00:28:38.509639+00:00
-- url     : https://prove2.me/submissions/dab64506-a89c-4e71-a4de-e62d55b872ca

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open Filter Topology InnerProductSpace
open ConvexOptimization

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000


-- ## Banach's theorem for symmetric trilinear forms (two equal arguments, sharp constant)

namespace TriAux

variable {n : ℕ}

/-- If `t * A ≤ B * t²` for every real `t` with `B ≥ 0`, then `A = 0`. -/
theorem eq_zero_of_le_sq {A B : ℝ} (hB : 0 ≤ B) (h : ∀ t : ℝ, t * A ≤ B * t ^ 2) : A = 0 := by
  by_contra hA
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · set t : ℝ := -(min 1 (-A / (B + 1))) with ht
    have hpos1 : 0 < -A / (B + 1) := div_pos (by linarith) (by linarith)
    have htneg : t < 0 := by
      rw [ht]
      simp only [neg_neg, neg_lt_zero]
      exact lt_min one_pos hpos1
    have htle : -t ≤ -A / (B + 1) := by rw [ht]; simp only [neg_neg]; exact min_le_right _ _
    have hkey := h t
    have h2 : A ≥ B * t := by nlinarith only [hkey, htneg]
    have h3 : B * (-t) ≤ B * (-A / (B + 1)) := by
      exact mul_le_mul_of_nonneg_left htle hB
    have h4 : B * (-A / (B + 1)) < -A := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < B + 1)]
      nlinarith
    nlinarith
  · set t : ℝ := min 1 (A / (B + 1)) with ht
    have hpos1 : 0 < A / (B + 1) := div_pos (by linarith) (by linarith)
    have htpos : 0 < t := lt_min one_pos hpos1
    have htle : t ≤ A / (B + 1) := min_le_right _ _
    have hkey := h t
    have h2 : A ≤ B * t := by nlinarith only [hkey, htpos]
    have h3 : B * t ≤ B * (A / (B + 1)) := mul_le_mul_of_nonneg_left htle hB
    have h4 : B * (A / (B + 1)) < A := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < B + 1)]
      nlinarith
    linarith

/-- Cauchy–Schwarz for a positive semidefinite symmetric bilinear form. -/
theorem quad_cs {A C B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ s : ℝ, 0 ≤ A + 2 * s * C + s ^ 2 * B) : C ^ 2 ≤ A * B := by
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · have hC : C = 0 := by
      by_contra hC
      have hkey := h (-(A + 1) / (2 * C))
      rw [← hB0] at hkey
      have hs : 2 * (-(A + 1) / (2 * C)) * C = -(A + 1) := by field_simp
      have hz : ((-(A + 1) / (2 * C)) ^ 2 * (0:ℝ)) = 0 := by ring
      rw [hs, hz, add_zero] at hkey
      linarith
    rw [hC]
    simpa using mul_nonneg hA hB
  · have hkey := h (-C / B)
    have hBne : B ≠ 0 := ne_of_gt hBpos
    have hs : 2 * (-C / B) * C + (-C / B) ^ 2 * B = -(C ^ 2 / B) := by field_simp; ring
    rw [add_assoc, hs] at hkey
    have h2 : C ^ 2 / B ≤ A := by linarith
    rw [div_le_iff₀ hBpos] at h2
    linarith

/-- A positive definite quadratic form is coercive. -/
theorem exists_pos_lower (Hx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hHpd : ∀ a : EuclideanSpace ℝ (Fin n), a ≠ 0 → 0 < ⟪Hx a, a⟫) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : EuclideanSpace ℝ (Fin n), c * ‖a‖ ^ 2 ≤ ⟪Hx a, a⟫ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, fun a => ?_⟩
    have ha : a = 0 := by
      ext i
      exact absurd i.isLt (by omega)
    simp [ha]
  · have hsph : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := isCompact_sphere 0 1
    have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty := by
      refine ⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), ?_⟩
      simp [EuclideanSpace.norm_single]
    obtain ⟨a₀, ha₀, hmin⟩ := hsph.exists_isMinOn hne
      (by fun_prop : ContinuousOn (fun a : EuclideanSpace ℝ (Fin n) => ⟪Hx a, a⟫) _)
    have ha₀ne : a₀ ≠ 0 := by
      intro h
      rw [h] at ha₀
      simp at ha₀
    refine ⟨⟪Hx a₀, a₀⟫, hHpd a₀ ha₀ne, fun a => ?_⟩
    by_cases ha : a = 0
    · simp [ha]
    · have hn0 : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
      have hmem : ‖a‖⁻¹ • a ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simp [norm_smul, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr ha)), hn0]
      have hcmp := isMinOn_iff.mp hmin _ hmem
      simp only [real_inner_smul_left, real_inner_smul_right, map_smul] at hcmp
      have hsq : (0:ℝ) < ‖a‖ ^ 2 := by positivity
      rw [← sub_nonneg] at hcmp ⊢
      have hexp : ⟪Hx a, a⟫ - ⟪Hx a₀, a₀⟫ * ‖a‖ ^ 2
          = ‖a‖ ^ 2 * (‖a‖⁻¹ * (‖a‖⁻¹ * ⟪Hx a, a⟫) - ⟪Hx a₀, a₀⟫) := by
        field_simp
      rw [hexp]
      exact mul_nonneg hsq.le hcmp

theorem isCompact_ball (Hx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hHpd : ∀ a : EuclideanSpace ℝ (Fin n), a ≠ 0 → 0 < ⟪Hx a, a⟫) :
    IsCompact {a : EuclideanSpace ℝ (Fin n) | ⟪Hx a, a⟫ ≤ 1} := by
  obtain ⟨c, hc, hlow⟩ := exists_pos_lower Hx hHpd
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) continuous_const) ?_
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨Real.sqrt (1 / c), fun a ha => ?_⟩
  simp only [Set.mem_setOf_eq] at ha
  have h1 : c * ‖a‖ ^ 2 ≤ 1 := le_trans (hlow a) ha
  have h2 : ‖a‖ ^ 2 ≤ 1 / c := by rw [le_div_iff₀ hc]; linarith
  simp only [Metric.mem_closedBall, dist_zero_right]
  have := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg a)] at this

/-- **Sharp mixed bound.**  A symmetric trilinear form whose diagonal is dominated by
`2 Q(v)^{3/2}` satisfies `|T(u,w,w)| ≤ 2 Q(u)^{1/2} Q(w)`.  This is the two-equal-arguments
case of Banach's theorem on symmetric multilinear forms, with the sharp constant. -/
theorem trilinear_sharp
    (Hx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (DH : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hHsym : ∀ a b, ⟪Hx a, b⟫ = ⟪Hx b, a⟫)
    (hHpd : ∀ a : EuclideanSpace ℝ (Fin n), a ≠ 0 → 0 < ⟪Hx a, a⟫)
    (hD12 : ∀ a b, DH a b = DH b a)
    (hD23 : ∀ a b c, ⟪DH a b, c⟫ = ⟪DH a c, b⟫)
    (hdiag : ∀ v, |⟪DH v v, v⟫| ≤ 2 * (⟪Hx v, v⟫) ^ ((3:ℝ)/2)) :
    ∀ u w, |⟪DH u w, w⟫| ≤ 2 * Real.sqrt ⟪Hx u, u⟫ * ⟪Hx w, w⟫ := by
  classical
  set Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ := fun a b => ⟪Hx a, b⟫ with hQ
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) → ℝ := fun a b c => ⟪DH a b, c⟫ with hT
  have hQapp : ∀ a b, Q a b = ⟪Hx a, b⟫ := by intro a b; rw [hQ]
  have hTapp : ∀ a b c, T a b c = ⟪DH a b, c⟫ := by intro a b c; rw [hT]
  have hdiag' : ∀ v, |T v v v| ≤ 2 * (Q v v) ^ ((3:ℝ)/2) := by
    intro v; rw [hTapp, hQapp]; exact hdiag v
  suffices hgoal : ∀ u w, |T u w w| ≤ 2 * Real.sqrt (Q u u) * Q w w by
    intro u w
    have hg := hgoal u w
    rwa [hTapp, hQapp, hQapp] at hg
  -- basic algebra
  have hQnn : ∀ a, 0 ≤ Q a a := by
    intro a
    by_cases h : a = 0
    · simp [hQ, h]
    · exact (hHpd a h).le
  have hQsym : ∀ a b, Q a b = Q b a := hHsym
  have hQsm1 : ∀ (r : ℝ) a b, Q (r • a) b = r * Q a b := by
    intro r a b; simp [hQ, real_inner_smul_left]
  have hQsm2 : ∀ (r : ℝ) a b, Q a (r • b) = r * Q a b := by
    intro r a b; simp [hQ, real_inner_smul_right]
  have hQadd1 : ∀ a a' b, Q (a + a') b = Q a b + Q a' b := by
    intro a a' b; simp [hQ, inner_add_left]
  have hQadd2 : ∀ a b b', Q a (b + b') = Q a b + Q a b' := by
    intro a b b'; simp [hQ, inner_add_right]
  have hT12 : ∀ a b c, T a b c = T b a c := by intro a b c; simp only [hT, hD12]
  have hT23 : ∀ a b c, T a b c = T a c b := by intro a b c; simp only [hT]; exact hD23 a b c
  have hT13 : ∀ a b c, T a b c = T c b a := by intro a b c; rw [hT23, hT12, hT23]
  have hTsm1 : ∀ (r : ℝ) a b c, T (r • a) b c = r * T a b c := by
    intro r a b c; simp [hT, real_inner_smul_left]
  have hTsm2 : ∀ (r : ℝ) a b c, T a (r • b) c = r * T a b c := by
    intro r a b c; simp [hT, real_inner_smul_left]
  have hTsm3 : ∀ (r : ℝ) a b c, T a b (r • c) = r * T a b c := by
    intro r a b c; simp [hT, real_inner_smul_right]
  have hTadd1 : ∀ a a' b c, T (a + a') b c = T a b c + T a' b c := by
    intro a a' b c; simp [hT, inner_add_left]
  have hTadd2 : ∀ a b b' c, T a (b + b') c = T a b c + T a b' c := by
    intro a b b' c; simp [hT, inner_add_left]
  have hTadd3 : ∀ a b c c', T a b (c + c') = T a b c + T a b c' := by
    intro a b c c'; simp [hT, inner_add_right]
  -- cubic expansion along a two-dimensional plane
  have hexp3 : ∀ (c s : ℝ) (a b : EuclideanSpace ℝ (Fin n)),
      T (c • a + s • b) (c • a + s • b) (c • a + s • b)
        = c ^ 3 * T a a a + 3 * c ^ 2 * s * T a a b + 3 * c * s ^ 2 * T a b b
          + s ^ 3 * T b b b := by
    intro c s a b
    simp only [hTadd1, hTadd2, hTadd3, hTsm1, hTsm2, hTsm3]
    rw [show T a b a = T a a b from hT23 a b a, show T b a a = T a a b from hT13 b a a,
      show T b a b = T a b b from hT12 b a b, show T b b a = T a b b from hT13 b b a]
    ring
  have hQexp : ∀ (c s : ℝ) (a b : EuclideanSpace ℝ (Fin n)), Q a b = 0 →
      Q (c • a + s • b) (c • a + s • b) = c ^ 2 * Q a a + s ^ 2 * Q b b := by
    intro c s a b hab
    have hba : Q b a = 0 := by rw [hQsym b a]; exact hab
    simp only [hQadd1, hQadd2, hQsm1, hQsm2]
    rw [hab, hba]
    ring
  -- the compact ball and the maximiser
  set Ball : Set (EuclideanSpace ℝ (Fin n)) := {a | Q a a ≤ 1} with hBall
  have hBc : IsCompact Ball := isCompact_ball Hx hHpd
  have hBne : (Ball ×ˢ Ball).Nonempty := ⟨(0, 0), by simp [hBall, hQ]⟩
  obtain ⟨p, hp, hmax⟩ := (hBc.prod hBc).exists_isMaxOn hBne
    (by fun_prop : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      T p.1 p.1 p.2) _)
  set u0 := p.1 with hu0d
  set v0 := p.2 with hv0d
  set K : ℝ := T u0 u0 v0 with hK
  have hKmax : ∀ a ∈ Ball, ∀ b ∈ Ball, T a a b ≤ K := fun a ha b hb =>
    hmax (Set.mk_mem_prod ha hb)
  have hK0 : 0 ≤ K := by
    have := hKmax 0 (by simp [hBall, hQ]) 0 (by simp [hBall, hQ])
    simpa [hT] using this
  -- `K ≤ 2`
  have hKle : K ≤ 2 := by
    rcases eq_or_lt_of_le hK0 with hK00 | hKpos
    · linarith
    have hu0B : u0 ∈ Ball := hp.1
    have hv0B : v0 ∈ Ball := hp.2
    have hu0ne : u0 ≠ 0 := by intro h; rw [hK, h] at hKpos; simp [hT] at hKpos
    have hv0ne : v0 ≠ 0 := by intro h; rw [hK, h] at hKpos; simp [hT] at hKpos
    have hu0pos : 0 < Q u0 u0 := hHpd u0 hu0ne
    have hv0pos : 0 < Q v0 v0 := hHpd v0 hv0ne
    have hQsc : ∀ (r : ℝ) a, Q (r • a) (r • a) = r ^ 2 * Q a a := by
      intro r a; rw [hQsm1, hQsm2]; ring
    have hu0one : Q u0 u0 = 1 := by
      by_contra hne
      have hlt : Q u0 u0 < 1 := lt_of_le_of_ne hu0B hne
      set t : ℝ := (Real.sqrt (Q u0 u0))⁻¹ with ht
      have hs : 0 < Real.sqrt (Q u0 u0) := Real.sqrt_pos.mpr hu0pos
      have hsq : Real.sqrt (Q u0 u0) ^ 2 = Q u0 u0 := Real.sq_sqrt hu0pos.le
      have htpos : 0 < t := by positivity
      have hmem : t • u0 ∈ Ball := by
        simp only [hBall, Set.mem_setOf_eq, hQsc, ht, inv_pow, hsq]
        rw [inv_mul_cancel₀ (ne_of_gt hu0pos)]
      have hbig := hKmax (t • u0) hmem v0 hv0B
      rw [hTsm1, hT12, hTsm1, hT12, ← hK] at hbig
      have ht2 : t * (t * K) = t ^ 2 * K := by ring
      have hgt : 1 < t ^ 2 := by
        rw [ht]
        rw [inv_pow, one_lt_inv_iff₀]
        exact ⟨by positivity, by rw [hsq]; exact hlt⟩
      nlinarith only [hbig, hKpos, hgt, ht2]
    have hv0one : Q v0 v0 = 1 := by
      by_contra hne
      have hlt : Q v0 v0 < 1 := lt_of_le_of_ne hv0B hne
      set t : ℝ := (Real.sqrt (Q v0 v0))⁻¹ with ht
      have hs : 0 < Real.sqrt (Q v0 v0) := Real.sqrt_pos.mpr hv0pos
      have hsq : Real.sqrt (Q v0 v0) ^ 2 = Q v0 v0 := Real.sq_sqrt hv0pos.le
      have htpos : 0 < t := by positivity
      have hmem : t • v0 ∈ Ball := by
        simp only [hBall, Set.mem_setOf_eq, hQsc, ht, inv_pow, hsq]
        rw [inv_mul_cancel₀ (ne_of_gt hv0pos)]
      have hbig := hKmax u0 hu0B (t • v0) hmem
      rw [hTsm3, ← hK] at hbig
      have hgt : 1 < t := by
        rw [ht, lt_inv_comm₀ (by norm_num) hs]
        nlinarith only [hs, hsq, hlt]
      nlinarith only [hbig, hKpos, hgt]
    -- first-order conditions
    have hfoc_v : ∀ z, T u0 u0 z = K * Q v0 z := by
      have key : ∀ z, Q v0 z = 0 → T u0 u0 z = 0 := by
        intro z hz
        refine eq_zero_of_le_sq (B := K * Q z z / 2)
          (div_nonneg (mul_nonneg hK0 (hQnn z)) (by norm_num)) ?_
        intro t
        set r : ℝ := Real.sqrt (1 + t ^ 2 * Q z z) with hr
        have hin : (0:ℝ) < 1 + t ^ 2 * Q z z := by nlinarith only [hQnn z, sq_nonneg t]
        have hrpos : 0 < r := Real.sqrt_pos.mpr hin
        have hr2 : r ^ 2 = 1 + t ^ 2 * Q z z := Real.sq_sqrt hin.le
        have hrne : r ≠ 0 := ne_of_gt hrpos
        have hexpand : Q (r⁻¹ • (v0 + t • z)) (r⁻¹ • (v0 + t • z))
            = r⁻¹ * r⁻¹ * (Q v0 v0 + 2 * t * Q v0 z + t ^ 2 * Q z z) := by
          simp only [hQsm1, hQsm2, hQadd1, hQadd2]
          rw [hQsym z v0]
          ring
        have hmem : (r⁻¹ • (v0 + t • z)) ∈ Ball := by
          show Q (r⁻¹ • (v0 + t • z)) (r⁻¹ • (v0 + t • z)) ≤ 1
          rw [hexpand, hz, hv0one]
          rw [show r⁻¹ * r⁻¹ * (1 + 2 * t * 0 + t ^ 2 * Q z z) = 1 by
            rw [show (1:ℝ) + 2 * t * 0 + t ^ 2 * Q z z = r ^ 2 by rw [hr2]; ring]
            field_simp]
        have hbig := hKmax u0 hu0B _ hmem
        rw [hTsm3, hTadd3, hTsm3, ← hK] at hbig
        have hxnn : 0 ≤ t ^ 2 * Q z z := mul_nonneg (sq_nonneg t) (hQnn z)
        have hrsq : r ≤ 1 + t ^ 2 * Q z z / 2 := by
          have h1 : 1 + t ^ 2 * Q z z ≤ (1 + t ^ 2 * Q z z / 2) ^ 2 := by
            nlinarith only [sq_nonneg (t ^ 2 * Q z z)]
          have h2 := Real.sqrt_le_sqrt h1
          rw [Real.sqrt_sq (by linarith)] at h2
          rw [hr]; exact h2
        have h1 : K + t * T u0 u0 z ≤ K * r := by
          have hmul := mul_le_mul_of_nonneg_left hbig hrpos.le
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hrpos), one_mul] at hmul
          linarith [hmul]
        have h2 : K * r ≤ K * (1 + t ^ 2 * Q z z / 2) := mul_le_mul_of_nonneg_left hrsq hK0
        nlinarith only [h1, h2]
      intro z
      have hdec : z = (Q v0 z) • v0 + (z - (Q v0 z) • v0) := by abel
      have hzero : Q v0 (z - (Q v0 z) • v0) = 0 := by
        rw [show z - (Q v0 z) • v0 = z + (-(Q v0 z)) • v0 by module, hQadd2, hQsm2, hv0one]
        ring
      have := key _ hzero
      rw [show z - (Q v0 z) • v0 = z + (-(Q v0 z)) • v0 by module, hTadd3, hTsm3, ← hK] at this
      linarith
    have hfoc_u : ∀ z, T u0 z v0 = K * Q u0 z := by
      have key : ∀ z, Q u0 z = 0 → T u0 z v0 = 0 := by
        intro z hz
        refine eq_zero_of_le_sq (B := |K * Q z z - T z z v0| / 2)
          (div_nonneg (abs_nonneg _) (by norm_num)) ?_
        intro t
        set r : ℝ := Real.sqrt (1 + t ^ 2 * Q z z) with hr
        have hin : (0:ℝ) < 1 + t ^ 2 * Q z z := by nlinarith only [hQnn z, sq_nonneg t]
        have hrpos : 0 < r := Real.sqrt_pos.mpr hin
        have hr2 : r ^ 2 = 1 + t ^ 2 * Q z z := Real.sq_sqrt hin.le
        have hrne : r ≠ 0 := ne_of_gt hrpos
        have hexpand : Q (r⁻¹ • (u0 + t • z)) (r⁻¹ • (u0 + t • z))
            = r⁻¹ * r⁻¹ * (Q u0 u0 + 2 * t * Q u0 z + t ^ 2 * Q z z) := by
          simp only [hQsm1, hQsm2, hQadd1, hQadd2]
          rw [hQsym z u0]
          ring
        have hmem : (r⁻¹ • (u0 + t • z)) ∈ Ball := by
          show Q (r⁻¹ • (u0 + t • z)) (r⁻¹ • (u0 + t • z)) ≤ 1
          rw [hexpand, hz, hu0one]
          rw [show r⁻¹ * r⁻¹ * (1 + 2 * t * 0 + t ^ 2 * Q z z) = 1 by
            rw [show (1:ℝ) + 2 * t * 0 + t ^ 2 * Q z z = r ^ 2 by rw [hr2]; ring]
            field_simp]
        have hTexp : T (r⁻¹ • (u0 + t • z)) (r⁻¹ • (u0 + t • z)) v0
            = r⁻¹ * r⁻¹ * (T u0 u0 v0 + 2 * t * T u0 z v0 + t ^ 2 * T z z v0) := by
          simp only [hTsm1, hTsm2, hTadd1, hTadd2]
          rw [hT12 z u0]
          ring
        have hbig := hKmax _ hmem v0 hv0B
        rw [hTexp, ← hK] at hbig
        have h1 : K + 2 * t * T u0 z v0 + t ^ 2 * T z z v0 ≤ K * r ^ 2 := by
          have hrr : (0:ℝ) < r ^ 2 := by positivity
          have hmul := mul_le_mul_of_nonneg_left hbig hrr.le
          rw [show r ^ 2 * (r⁻¹ * r⁻¹ * (K + 2 * t * T u0 z v0 + t ^ 2 * T z z v0))
              = K + 2 * t * T u0 z v0 + t ^ 2 * T z z v0 by field_simp <;> ring] at hmul
          linarith [hmul]
        rw [hr2] at h1
        have habs : K * Q z z - T z z v0 ≤ |K * Q z z - T z z v0| := le_abs_self _
        nlinarith only [h1, habs]
      intro z
      have hzero : Q u0 (z - (Q u0 z) • u0) = 0 := by
        rw [show z - (Q u0 z) • u0 = z + (-(Q u0 z)) • u0 by module, hQadd2, hQsm2, hu0one]
        ring
      have := key _ hzero
      rw [show z - (Q u0 z) • u0 = z + (-(Q u0 z)) • u0 by module, hTadd2, hTsm2, ← hK] at this
      linarith
    -- the plane spanned by `u0` and the normalised complement of `v0`
    set α : ℝ := Q u0 v0 with hα
    have hαsq : α ^ 2 ≤ 1 := by
      have hcs := quad_cs (A := Q u0 u0) (C := α) (B := Q v0 v0) (hQnn u0) (hQnn v0) ?_
      · rw [hu0one, hv0one] at hcs; linarith
      · intro s
        have hexp : Q (u0 + s • v0) (u0 + s • v0)
            = Q u0 u0 + 2 * s * Q u0 v0 + s ^ 2 * Q v0 v0 := by
          simp only [hQadd1, hQadd2, hQsm1, hQsm2]
          rw [hQsym v0 u0]
          ring
        have h := hQnn (u0 + s • v0)
        rw [hexp] at h
        have hgoal : Q u0 u0 + 2 * s * Q u0 v0 + s ^ 2 * Q v0 v0
            = Q u0 u0 + 2 * s * α + s ^ 2 * Q v0 v0 := by rw [hα]
        linarith [h, hgoal]
    have hvu : Q v0 u0 = α := by rw [hα]; exact (hQsym u0 v0).symm
    rcases eq_or_lt_of_le hαsq with hone | hlt1
    · -- `v0 = ± u0`
      have hzero : Q (v0 - α • u0) (v0 - α • u0) = 0 := by
        have hexp : Q (v0 - α • u0) (v0 - α • u0)
            = Q v0 v0 - 2 * α * Q v0 u0 + α ^ 2 * Q u0 u0 := by
          rw [show v0 - α • u0 = v0 + (-α) • u0 by module]
          simp only [hQadd1, hQadd2, hQsm1, hQsm2]
          rw [hQsym u0 v0]
          ring
        rw [hexp, hu0one, hv0one, hvu]
        nlinarith only [hone]
      have hveq : v0 = α • u0 := by
        by_contra hcon
        have hne : v0 - α • u0 ≠ 0 := sub_ne_zero.mpr hcon
        exact absurd hzero (ne_of_gt (hHpd _ hne))
      have hd := hdiag' u0
      rw [hu0one] at hd
      have : K = α * T u0 u0 u0 := by rw [hK, hveq, hTsm3]
      have hα1 : |α| = 1 := by
        have hsq : |α| ^ 2 = 1 := by rw [sq_abs]; exact hone
        nlinarith only [abs_nonneg α, hsq]
      have habs : |K| ≤ |T u0 u0 u0| := by
        rw [this, abs_mul, hα1, one_mul]
      simp only [Real.one_rpow, mul_one] at hd
      calc K ≤ |K| := le_abs_self K
        _ ≤ |T u0 u0 u0| := habs
        _ ≤ 2 := hd
    · -- the generic case
      have hβsq : 0 < 1 - α ^ 2 := by linarith
      set β : ℝ := Real.sqrt (1 - α ^ 2) with hβ
      have hβpos : 0 < β := Real.sqrt_pos.mpr hβsq
      have hβ2 : β ^ 2 = 1 - α ^ 2 := Real.sq_sqrt hβsq.le
      set e : EuclideanSpace ℝ (Fin n) := β⁻¹ • (v0 - α • u0) with he
      have hue : Q u0 e = 0 := by
        rw [he, show v0 - α • u0 = v0 + (-α) • u0 by module]
        simp only [hQsm2, hQadd2]
        rw [hu0one, hQsym u0 v0]
        rw [hQsym v0 u0, ← hα]
        ring
      have hβne : β ≠ 0 := ne_of_gt hβpos
      have hee : Q e e = 1 := by
        have hexp : Q e e
            = β⁻¹ * β⁻¹ * (Q v0 v0 - 2 * α * Q v0 u0 + α ^ 2 * Q u0 u0) := by
          rw [he, show v0 - α • u0 = v0 + (-α) • u0 by module]
          simp only [hQsm1, hQsm2, hQadd1, hQadd2]
          rw [hQsym u0 v0]
          ring
        rw [hexp, hu0one, hv0one, hvu]
        rw [show (1:ℝ) - 2 * α * α + α ^ 2 * 1 = β ^ 2 by rw [hβ2]; ring]
        field_simp
      have hv0e : v0 = α • u0 + β • e := by
        rw [he, smul_smul, mul_inv_cancel₀ (ne_of_gt hβpos), one_smul]
        module
      -- the four cubic coefficients
      have hA1 : T u0 u0 u0 = K * α := by
        rw [hfoc_v u0, hQsym v0 u0, ← hα]
      have hQv0e : Q v0 e = β := by
        nth_rewrite 1 [hv0e]
        rw [hQadd1, hQsm1, hQsm1, hue, hee]
        ring
      have hA2 : T u0 u0 e = K * β := by rw [hfoc_v e, hQv0e]
      have hA3 : T u0 e e = -(K * α) := by
        have h0 := hfoc_u e
        rw [hue, mul_zero] at h0
        rw [hv0e, hTadd3, hTsm3, hTsm3, show T u0 e u0 = T u0 u0 e from hT23 u0 e u0, hA2] at h0
        have : β * T u0 e e = -(α * (K * β)) := by linarith
        field_simp at this ⊢
        nlinarith only [this, hβpos]
      have hA4 : |T e e e| ≤ 2 := by
        have hde := hdiag' e
        rw [hee] at hde
        simpa using hde
      -- the three-angle argument
      have hcubic : ∀ θ : ℝ,
          T (Real.cos θ • u0 + Real.sin θ • e) (Real.cos θ • u0 + Real.sin θ • e)
            (Real.cos θ • u0 + Real.sin θ • e)
            = K * (α * Real.cos (3 * θ) + β * Real.sin (3 * θ))
              + (K * β + T e e e) * Real.sin θ ^ 3 := by
        intro θ
        rw [hexp3, hA1, hA2, hA3, Real.cos_three_mul, Real.sin_three_mul]
        have hpyth := Real.sin_sq_add_cos_sq θ
        linear_combination (3 * K * β * Real.sin θ - 3 * K * α * Real.cos θ) * hpyth
      have hnorm : ∀ θ : ℝ,
          Q (Real.cos θ • u0 + Real.sin θ • e) (Real.cos θ • u0 + Real.sin θ • e) = 1 := by
        intro θ
        rw [hQexp _ _ _ _ hue, hu0one, hee]
        nlinarith only [Real.sin_sq_add_cos_sq θ]
      have hbnd : ∀ θ : ℝ,
          T (Real.cos θ • u0 + Real.sin θ • e) (Real.cos θ • u0 + Real.sin θ • e)
            (Real.cos θ • u0 + Real.sin θ • e) ≤ 2 := by
        intro θ
        have hd := hdiag' (Real.cos θ • u0 + Real.sin θ • e)
        rw [hnorm θ] at hd
        simp only [Real.one_rpow, mul_one] at hd
        calc _ ≤ |T (Real.cos θ • u0 + Real.sin θ • e) (Real.cos θ • u0 + Real.sin θ • e)
                    (Real.cos θ • u0 + Real.sin θ • e)| := le_abs_self _
          _ ≤ 2 := hd
      -- pick the angle
      set φ : ℝ := Real.arccos α with hφ
      have hcosφ : Real.cos φ = α :=
        Real.cos_arccos (by nlinarith only [hlt1]) (by nlinarith only [hlt1])
      have hsinφ : Real.sin φ = β := by rw [hφ, Real.sin_arccos, hβ]
      have hφpos : 0 < φ := by
        rw [hφ]
        have : α < 1 := by nlinarith only [hlt1]
        exact Real.arccos_pos.mpr this
      have hφlt : φ < Real.pi := by
        rw [hφ]
        have : -1 < α := by nlinarith only [hlt1]
        exact Real.arccos_lt_pi.mpr this
      have hpi := Real.pi_pos
      by_cases hsign : 0 ≤ K * β + T e e e
      · have hθ : (0:ℝ) < φ / 3 := by linarith
        have hθ2 : φ / 3 < Real.pi := by linarith
        have hsinpos : 0 < Real.sin (φ / 3) := Real.sin_pos_of_pos_of_lt_pi hθ hθ2
        have h3 : 3 * (φ / 3) = φ := by ring
        have hc := hcubic (φ / 3)
        rw [h3, hcosφ, hsinφ] at hc
        have hb := hbnd (φ / 3)
        rw [hc] at hb
        nlinarith only [hb, hβ2, hsinpos, mul_nonneg hsign (pow_pos hsinpos 3).le]
      · push_neg at hsign
        have hθ : φ / 3 - 2 * Real.pi / 3 < 0 := by linarith
        have hθ2 : -Real.pi < φ / 3 - 2 * Real.pi / 3 := by linarith
        have hsinneg : Real.sin (φ / 3 - 2 * Real.pi / 3) < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt hθ hθ2
        have h3 : 3 * (φ / 3 - 2 * Real.pi / 3) = φ - 2 * Real.pi := by ring
        have hc := hcubic (φ / 3 - 2 * Real.pi / 3)
        rw [h3, Real.cos_sub_two_pi, Real.sin_sub_two_pi, hcosφ, hsinφ] at hc
        have hb := hbnd (φ / 3 - 2 * Real.pi / 3)
        rw [hc] at hb
        have hsqpos : 0 < Real.sin (φ / 3 - 2 * Real.pi / 3) ^ 2 := by nlinarith only [hsinneg]
        have hcube : Real.sin (φ / 3 - 2 * Real.pi / 3) ^ 3 < 0 := by
          nlinarith only [hsinneg, hsqpos]
        nlinarith only [hb, hβ2, mul_nonneg (le_of_lt (neg_pos.mpr hsign)) (le_of_lt (neg_pos.mpr hcube))]
  -- homogenise
  intro u w
  by_cases hw : w = 0
  · simp [hT, hw, hQ]
  by_cases hu : u = 0
  · simp [hT, hu, hQ]
  have hup : 0 < Q u u := hHpd u hu
  have hwp : 0 < Q w w := hHpd w hw
  set su := Real.sqrt (Q u u) with hsu
  set sw := Real.sqrt (Q w w) with hsw
  have hsup : 0 < su := Real.sqrt_pos.mpr hup
  have hswp : 0 < sw := Real.sqrt_pos.mpr hwp
  have hsu2 : su ^ 2 = Q u u := Real.sq_sqrt hup.le
  have hsw2 : sw ^ 2 = Q w w := Real.sq_sqrt hwp.le
  have hQsc : ∀ (r : ℝ) a, Q (r • a) (r • a) = r ^ 2 * Q a a := by
    intro r a; rw [hQsm1, hQsm2]; ring
  have hsune : su ≠ 0 := ne_of_gt hsup
  have hswne : sw ≠ 0 := ne_of_gt hswp
  have hmemu : (su⁻¹ • u) ∈ Ball := by
    show Q (su⁻¹ • u) (su⁻¹ • u) ≤ 1
    rw [hQsc, ← hsu2, show su⁻¹ ^ 2 * su ^ 2 = 1 by field_simp]
  have hmemw : (sw⁻¹ • w) ∈ Ball := by
    show Q (sw⁻¹ • w) (sw⁻¹ • w) ≤ 1
    rw [hQsc, ← hsw2, show sw⁻¹ ^ 2 * sw ^ 2 = 1 by field_simp]
  have hmemun : ((-su⁻¹) • u) ∈ Ball := by
    show Q ((-su⁻¹) • u) ((-su⁻¹) • u) ≤ 1
    rw [hQsc, ← hsu2, show (-su⁻¹) ^ 2 * su ^ 2 = 1 by field_simp]
  have h1 := hKmax _ hmemw _ hmemu
  have h2 := hKmax _ hmemw _ hmemun
  rw [hTsm1, hTsm2, hTsm3] at h1 h2
  have hprod : (0:ℝ) < sw ^ 2 * su := by positivity
  have hA : T w w u ≤ K * (sw ^ 2 * su) := by
    have hmul := mul_le_mul_of_nonneg_left h1 hprod.le
    rw [show sw ^ 2 * su * (sw⁻¹ * (sw⁻¹ * (su⁻¹ * T w w u))) = T w w u by
      field_simp <;> ring] at hmul
    linarith [hmul]
  have hB : -(K * (sw ^ 2 * su)) ≤ T w w u := by
    have hmul := mul_le_mul_of_nonneg_left h2 hprod.le
    rw [show sw ^ 2 * su * (sw⁻¹ * (sw⁻¹ * (-su⁻¹ * T w w u))) = -(T w w u) by
      field_simp <;> ring] at hmul
    linarith [hmul]
  have hkey : |T w w u| ≤ K * (sw ^ 2 * su) := abs_le.mpr ⟨hB, hA⟩
  have hfinal : |T u w w| ≤ 2 * su * Q w w := by
    rw [show T u w w = T w w u from hT13 u w w]
    calc |T w w u| ≤ K * (sw ^ 2 * su) := hkey
      _ ≤ 2 * (sw ^ 2 * su) := by nlinarith only [hKle, mul_pos (pow_pos hswp 2) hsup]
      _ = 2 * su * Q w w := by rw [hsw2]; ring
  exact hfinal

end TriAux


-- ## The derivative of the Hessian field and its permutation symmetries

namespace DHAux

variable {n : ℕ}

/-- The inverse Riesz identification, as a plain continuous linear map. -/
noncomputable def rieszInvL (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun φ => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }

@[simp] theorem rieszInvL_apply (φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    rieszInvL n φ = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ := rfl

/-- The Hessian field of a `C³` function is differentiable. -/
theorem hessian_differentiable
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf3 : ContDiffOn ℝ 3 f Ω)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x) :
    ∀ x ∈ Ω, DifferentiableAt ℝ H x := by
  -- `g` agrees with `rieszInvL ∘ fderiv f` on `Ω`
  have hgeq : ∀ y ∈ Ω, g y = rieszInvL n (fderiv ℝ f y) := by
    intro y hy
    have h1 : fderiv ℝ f y = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (g y) :=
      (hg y hy).hasFDerivAt.fderiv
    rw [rieszInvL_apply, h1, LinearIsometryEquiv.symm_apply_apply]
  -- hence `g` is `C²` on `Ω`
  have hfd : ContDiffOn ℝ 2 (fderiv ℝ f) Ω := hf3.fderiv_of_isOpen hΩo (by norm_num)
  have hgC : ContDiffOn ℝ 2 g Ω := by
    refine ContDiffOn.congr ?_ hgeq
    exact (rieszInvL n).contDiff.comp_contDiffOn hfd
  -- hence `fderiv g` is `C¹`, in particular differentiable, on `Ω`
  have hHeq : ∀ y ∈ Ω, H y = fderiv ℝ g y := fun y hy => (hH y hy).fderiv.symm
  have hfg : ContDiffOn ℝ 1 (fderiv ℝ g) Ω := hgC.fderiv_of_isOpen hΩo (by norm_num)
  have hdiff : DifferentiableOn ℝ (fderiv ℝ g) Ω := hfg.differentiableOn (by norm_num)
  intro x hx
  have hd : DifferentiableOn ℝ H Ω := hdiff.congr (fun y hy => (hHeq y hy))
  exact (hd x hx).differentiableAt (hΩo.mem_nhds hx)


noncomputable def rieszL (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) a)
      map_add' := fun a b => by ext w; simp [inner_add_left]
      map_smul' := fun c a => by ext w; simp [real_inner_smul_left] }

@[simp] theorem rieszL_apply (a b : EuclideanSpace ℝ (Fin n)) : rieszL n a b = ⟪a, b⟫ := rfl

/-- Evaluation of an operator against a fixed pair, as a continuous linear functional. -/
noncomputable def evalCLM (b c : EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun φ => ⟪φ b, c⟫
      map_add' := fun φ ψ => by simp [inner_add_left]
      map_smul' := fun r φ => by simp [real_inner_smul_left] }

@[simp] theorem evalCLM_apply (b c : EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    evalCLM b c φ = ⟪φ b, c⟫ := rfl

variable (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))

/-- Symmetry of the derivative of the Hessian field in its first two slots. -/
theorem DH_sym12 (hΩo : IsOpen Ω) (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (DH : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hDH : HasFDerivAt H DH x) (a b : EuclideanSpace ℝ (Fin n)) :
    DH a b = DH b a := by
  have hev : ∀ᶠ y in 𝓝 x, HasFDerivAt g (H y) y := by
    filter_upwards [hΩo.mem_nhds hx] with y hy using hH y hy
  exact second_derivative_symmetric_of_eventually hev hDH a b

/-- Symmetry of the derivative of the Hessian field in its last two slots. -/
theorem DH_sym23 (hΩo : IsOpen Ω) (hHsym : ∀ y ∈ Ω, ∀ a b, ⟪H y a, b⟫ = ⟪H y b, a⟫)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (DH : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hDH : HasFDerivAt H DH x) (a b c : EuclideanSpace ℝ (Fin n)) :
    ⟪DH a b, c⟫ = ⟪DH a c, b⟫ := by
  -- the function `y ↦ ⟪H y b, c⟫ - ⟪H y c, b⟫` vanishes near `x`
  set Ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ⟪H y b, c⟫ - ⟪H y c, b⟫ with hΨ
  have h1 : HasFDerivAt (fun y => ⟪H y b, c⟫)
      (((evalCLM b c) : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ).comp DH)
      x := (evalCLM b c).hasFDerivAt.comp x hDH
  have h2 : HasFDerivAt (fun y => ⟪H y c, b⟫)
      (((evalCLM c b) : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ).comp DH)
      x := (evalCLM c b).hasFDerivAt.comp x hDH
  have hΨd : HasFDerivAt Ψ ((evalCLM b c).comp DH - (evalCLM c b).comp DH) x := h1.sub h2
  have hzero : HasFDerivAt Ψ (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x := by
    have hev : Ψ =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [hΩo.mem_nhds hx] with y hy
      simp only [hΨ]
      rw [hHsym y hy b c]
      ring
    exact (hasFDerivAt_const (0:ℝ) x).congr_of_eventuallyEq hev
  have hLzero : (evalCLM b c).comp DH - (evalCLM c b).comp DH = 0 := hΨd.unique hzero
  have hap := congrArg (fun (M : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) => M a) hLzero
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    evalCLM_apply, ContinuousLinearMap.zero_apply] at hap
  linarith [hap]

/-- The third derivative along a line, expressed through `DH`. -/
theorem iteratedDeriv3_eq (hΩo : IsOpen Ω)
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (DH : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hDH : HasFDerivAt H DH x) (v : EuclideanSpace ℝ (Fin n)) :
    iteratedDeriv 3 (fun t : ℝ => f (x + t • v)) 0 = ⟪DH v v, v⟫ := by
  classical
  set S : Set ℝ := {t : ℝ | x + t • v ∈ Ω} with hS
  have hSopen : IsOpen S := hΩo.preimage (by fun_prop)
  have h0S : (0:ℝ) ∈ S := by simpa [hS] using hx
  set φ : ℝ → ℝ := fun t => f (x + t • v) with hφ
  set d1 : ℝ → ℝ := fun t => ⟪g (x + t • v), v⟫ with hd1
  set d2 : ℝ → ℝ := fun t => ⟪H (x + t • v) v, v⟫ with hd2
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hφd : ∀ t ∈ S, HasDerivAt φ (d1 t) t := by
    intro t ht
    have hcomp := ((hg _ ht).hasFDerivAt).comp_hasDerivAt t (hline t)
    simpa [hφ, hd1, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hcomp
  have hd1d : ∀ t ∈ S, HasDerivAt d1 (d2 t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => g (x + s • v)) (H (x + t • v) v) t :=
      (hH _ ht).comp_hasDerivAt t (hline t)
    exact (h1.inner ℝ (hasDerivAt_const t v)).congr_deriv (by simp [hd2])
  have hev : ∀ t ∈ S, deriv φ =ᶠ[𝓝 t] d1 := by
    intro t ht
    filter_upwards [hSopen.mem_nhds ht] with s hs using (hφd s hs).deriv
  have hu2 : ∀ t ∈ S, iteratedDeriv 2 φ t = d2 t := by
    intro t ht
    rw [iteratedDeriv_succ, iteratedDeriv_one, (hev t ht).deriv_eq]
    exact (hd1d t ht).deriv
  have hev2 : iteratedDeriv 2 φ =ᶠ[𝓝 (0:ℝ)] d2 := by
    filter_upwards [hSopen.mem_nhds h0S] with s hs using hu2 s hs
  have hd2d : HasDerivAt d2 ⟪DH v v, v⟫ 0 := by
    have hcomp : HasDerivAt (fun t : ℝ => H (x + t • v)) (DH v) 0 := by
      have hDH' : HasFDerivAt H DH ((fun t : ℝ => x + t • v) 0) := by simpa using hDH
      have hc := hDH'.comp_hasDerivAt (0:ℝ) (hline 0)
      simpa using hc
    have := (hcomp.clm_apply (hasDerivAt_const (0:ℝ) v)).inner ℝ (hasDerivAt_const (0:ℝ) v)
    simpa [hd2] using this
  rw [iteratedDeriv_succ, hev2.deriv_eq, hd2d.deriv]


end DHAux

namespace DHAux

variable {m : ℕ}

/-- The second derivative along a line, expressed through the Hessian field. -/
theorem iteratedDeriv2_eq (Ω : Set (EuclideanSpace ℝ (Fin m))) (hΩo : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ Ω) (v : EuclideanSpace ℝ (Fin m)) :
    iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 = ⟪H x v, v⟫ := by
  classical
  set S : Set ℝ := {t : ℝ | x + t • v ∈ Ω} with hS
  have hSopen : IsOpen S := hΩo.preimage (by fun_prop)
  have h0S : (0:ℝ) ∈ S := by simpa [hS] using hx
  set φ : ℝ → ℝ := fun t => f (x + t • v) with hφ
  set d1 : ℝ → ℝ := fun t => ⟪g (x + t • v), v⟫ with hd1
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hφd : ∀ t ∈ S, HasDerivAt φ (d1 t) t := by
    intro t ht
    have hcomp := ((hg _ ht).hasFDerivAt).comp_hasDerivAt t (hline t)
    simpa [hφ, hd1, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hcomp
  have hd1d : HasDerivAt d1 ⟪H x v, v⟫ 0 := by
    have h1 : HasDerivAt (fun s : ℝ => g (x + s • v)) (H (x + (0:ℝ) • v) v) 0 :=
      (hH _ h0S).comp_hasDerivAt 0 (hline 0)
    have h2 := h1.inner ℝ (hasDerivAt_const (0:ℝ) v)
    simpa [hd1] using h2
  have hev : deriv φ =ᶠ[𝓝 (0:ℝ)] d1 := by
    filter_upwards [hSopen.mem_nhds h0S] with s hs using (hφd s hs).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
  exact hd1d.deriv

/-- Differentiating the Hessian field along a line. -/
theorem hess_line_deriv (Ω : Set (EuclideanSpace ℝ (Fin m)))
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (DHf : EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin m) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hDH : ∀ y ∈ Ω, HasFDerivAt H (DHf y) y)
    (x v a b : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : x + t • v ∈ Ω) :
    HasDerivAt (fun s : ℝ => ⟪H (x + s • v) a, b⟫) ⟪DHf (x + t • v) v a, b⟫ t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hcomp : HasDerivAt (fun s : ℝ => H (x + s • v)) (DHf (x + t • v) v) t :=
    (hDH _ ht).comp_hasDerivAt t hline
  have h2 := (hcomp.clm_apply (hasDerivAt_const t a)).inner ℝ (hasDerivAt_const t b)
  simpa using h2

/-- Differentiating the gradient field along a line. -/
theorem grad_line_deriv (Ω : Set (EuclideanSpace ℝ (Fin m)))
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hH : ∀ y ∈ Ω, HasFDerivAt g (H y) y)
    (x v b : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : x + t • v ∈ Ω) :
    HasDerivAt (fun s : ℝ => ⟪g (x + s • v), b⟫) ⟪H (x + t • v) v, b⟫ t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hcomp : HasDerivAt (fun s : ℝ => g (x + s • v)) (H (x + t • v) v) t :=
    (hH _ ht).comp_hasDerivAt t hline
  have h2 := hcomp.inner ℝ (hasDerivAt_const t b)
  simpa using h2

/-- Differentiating the function itself along a line. -/
theorem fun_line_deriv (Ω : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hg : ∀ y ∈ Ω, HasGradientAt f (g y) y)
    (x v : EuclideanSpace ℝ (Fin m)) (t : ℝ) (ht : x + t • v ∈ Ω) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) ⟪g (x + t • v), v⟫ t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hcomp := ((hg _ ht).hasFDerivAt).comp_hasDerivAt t hline
  simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hcomp

end DHAux


-- ## One-dimensional self-concordance comparison estimates

namespace SCUp

/-- **The one-dimensional self-concordance comparison.**  If `u > 0` is differentiable on an
interval containing `[0, b]` with `|u'| ≤ 2 u^{3/2}`, then with `r = √(u 0)`,

* `u t ≥ r²/(1 + r t)²`  (always), and
* `u t ≤ r²/(1 - r t)²`  (as long as `r t < 1`).

Both are obtained by noting that `ψ = u^{-1/2}` is `1`-Lipschitz. -/
theorem u_bounds (S : Set ℝ) (hSc : Convex ℝ S) (b : ℝ) (hb : 0 ≤ b)
    (hIcc : Set.Icc (0:ℝ) b ⊆ S)
    (u u' : ℝ → ℝ)
    (hud : ∀ t ∈ S, HasDerivAt u (u' t) t)
    (hupos : ∀ t ∈ S, 0 < u t)
    (hscb : ∀ t ∈ S, |u' t| ≤ 2 * (u t) ^ ((3:ℝ)/2)) :
    ∀ t ∈ Set.Icc (0:ℝ) b,
      (Real.sqrt (u 0)) ^ 2 / (1 + Real.sqrt (u 0) * t) ^ 2 ≤ u t ∧
      (Real.sqrt (u 0) * t < 1 →
        u t ≤ (Real.sqrt (u 0)) ^ 2 / (1 - Real.sqrt (u 0) * t) ^ 2) := by
  classical
  have h0S : (0:ℝ) ∈ S := hIcc ⟨le_refl 0, hb⟩
  set r : ℝ := Real.sqrt (u 0) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (hupos 0 h0S)
  have hr2 : r ^ 2 = u 0 := Real.sq_sqrt (hupos 0 h0S).le
  set ψ : ℝ → ℝ := fun t => (Real.sqrt (u t))⁻¹ with hψ
  have hsp : ∀ t ∈ S, 0 < Real.sqrt (u t) := fun t ht => Real.sqrt_pos.mpr (hupos t ht)
  have hsq : ∀ t ∈ S, Real.sqrt (u t) ^ 2 = u t := fun t ht => Real.sq_sqrt (hupos t ht).le
  have hψd : ∀ t ∈ S, HasDerivAt ψ (-(u' t / (2 * Real.sqrt (u t))) / (u t)) t := by
    intro t ht
    have hs : HasDerivAt (fun s => Real.sqrt (u s)) (u' t / (2 * Real.sqrt (u t))) t := by
      have h0 := (Real.hasDerivAt_sqrt (ne_of_gt (hupos t ht))).comp t (hud t ht)
      have heq : 1 / (2 * Real.sqrt (u t)) * u' t = u' t / (2 * Real.sqrt (u t)) := by ring
      rw [heq] at h0
      exact h0
    have hne : Real.sqrt (u t) ≠ 0 := ne_of_gt (hsp t ht)
    have hinv := hs.inv hne
    rw [hsq t ht] at hinv
    exact hinv
  have hψlip : ∀ t ∈ S, |(-(u' t / (2 * Real.sqrt (u t))) / (u t))| ≤ 1 := by
    intro t ht
    have hup := hupos t ht
    have hspt := hsp t ht
    have hbb := hscb t ht
    have hpow : (u t) ^ ((3:ℝ)/2) = u t * Real.sqrt (u t) := by
      rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add hup, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    rw [hpow] at hbb
    rw [abs_div, abs_neg, abs_div, abs_of_pos hup,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt (u t))]
    rw [div_div, div_le_one (by positivity)]
    calc |u' t| ≤ 2 * (u t * Real.sqrt (u t)) := hbb
      _ = 2 * Real.sqrt (u t) * u t := by ring
  -- `ψ t ≤ ψ 0 + t` and `ψ 0 - t ≤ ψ t` on `[0, b]`
  have hψ0 : ψ 0 = r⁻¹ := by rw [hψ, hr]
  have hupper : ∀ t ∈ Set.Icc (0:ℝ) b, ψ t ≤ ψ 0 + t := by
    have hanti : AntitoneOn (fun t => ψ t - t) (Set.Icc (0:ℝ) b) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 b) ?_ ?_ ?_
      · intro t ht
        exact (((hψd t (hIcc ht)).sub (hasDerivAt_id t)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hψd t (hIcc (Set.mem_Icc_of_Ioo ht))).sub
          (hasDerivAt_id t)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htS : t ∈ S := hIcc (Set.mem_Icc_of_Ioo ht)
        have hd : HasDerivAt (fun s : ℝ => ψ s - s)
            (-(u' t / (2 * Real.sqrt (u t))) / (u t) - 1) t :=
          (hψd t htS).sub (hasDerivAt_id t)
        rw [hd.deriv]
        linarith [(abs_le.mp (hψlip t htS)).2]
    intro t ht
    have := hanti (Set.left_mem_Icc.mpr hb) ht ht.1
    simp only at this
    linarith
  have hlower : ∀ t ∈ Set.Icc (0:ℝ) b, ψ 0 - t ≤ ψ t := by
    have hmono : MonotoneOn (fun t => ψ t + t) (Set.Icc (0:ℝ) b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 b) ?_ ?_ ?_
      · intro t ht
        exact (((hψd t (hIcc ht)).add (hasDerivAt_id t)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hψd t (hIcc (Set.mem_Icc_of_Ioo ht))).add
          (hasDerivAt_id t)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htS : t ∈ S := hIcc (Set.mem_Icc_of_Ioo ht)
        have hd : HasDerivAt (fun s : ℝ => ψ s + s)
            (-(u' t / (2 * Real.sqrt (u t))) / (u t) + 1) t :=
          (hψd t htS).add (hasDerivAt_id t)
        rw [hd.deriv]
        linarith [(abs_le.mp (hψlip t htS)).1]
    intro t ht
    have := hmono (Set.left_mem_Icc.mpr hb) ht ht.1
    simp only at this
    linarith
  intro t ht
  have htS : t ∈ S := hIcc ht
  have hspt := hsp t htS
  constructor
  · -- lower bound on `u`
    have hden : (0:ℝ) < 1 + r * t := by nlinarith only [ht.1, hrpos]
    have hb2 : (Real.sqrt (u t))⁻¹ ≤ (1 + r * t) / r := by
      have := hupper t ht
      rw [hψ0] at this
      calc (Real.sqrt (u t))⁻¹ ≤ r⁻¹ + t := this
        _ = (1 + r * t) / r := by field_simp
    have hkey : r / (1 + r * t) ≤ Real.sqrt (u t) := by
      rw [div_le_iff₀ hden]
      have h1 := mul_le_mul_of_nonneg_left hb2 (le_of_lt (mul_pos hrpos hspt))
      rw [show (r * Real.sqrt (u t)) * (Real.sqrt (u t))⁻¹ = r by field_simp,
        show (r * Real.sqrt (u t)) * ((1 + r * t) / r) = Real.sqrt (u t) * (1 + r * t) by
          field_simp] at h1
      exact h1
    calc r ^ 2 / (1 + r * t) ^ 2 = (r / (1 + r * t)) ^ 2 := (div_pow r (1 + r * t) 2).symm
      _ ≤ (Real.sqrt (u t)) ^ 2 := pow_le_pow_left₀ (by positivity) hkey 2
      _ = u t := hsq t htS
  · -- upper bound on `u`
    intro hrt
    have hden : (0:ℝ) < 1 - r * t := by linarith
    have hb2 : (1 - r * t) / r ≤ (Real.sqrt (u t))⁻¹ := by
      have := hlower t ht
      rw [hψ0] at this
      calc (1 - r * t) / r = r⁻¹ - t := by field_simp
        _ ≤ (Real.sqrt (u t))⁻¹ := this
    have hkey : Real.sqrt (u t) ≤ r / (1 - r * t) := by
      rw [le_div_iff₀ hden]
      have h1 := mul_le_mul_of_nonneg_left hb2 (le_of_lt (mul_pos hrpos hspt))
      rw [show (r * Real.sqrt (u t)) * ((1 - r * t) / r) = Real.sqrt (u t) * (1 - r * t) by
          field_simp,
        show (r * Real.sqrt (u t)) * (Real.sqrt (u t))⁻¹ = r by field_simp] at h1
      exact h1
    calc u t = (Real.sqrt (u t)) ^ 2 := (hsq t htS).symm
      _ ≤ (r / (1 - r * t)) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hkey 2
      _ = r ^ 2 / (1 - r * t) ^ 2 := div_pow r (1 - r * t) 2

variable {n : ℕ}

/-- Gronwall-type comparison: `|q'/q| ≤ 2r/(1-rt)` forces `q` to stay within the factor
`(1-r)^{±2}`.  Proved by monotonicity of `log q ∓ 2 log (1 - r t)`, with no integration. -/
theorem log_comparison (S : Set ℝ) (hIcc : Set.Icc (0:ℝ) 1 ⊆ S)
    (q q' : ℝ → ℝ) (hqd : ∀ t ∈ S, HasDerivAt q (q' t) t) (hqpos : ∀ t ∈ S, 0 < q t)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbnd : ∀ t ∈ Set.Icc (0:ℝ) 1, |q' t| ≤ 2 * r / (1 - r * t) * q t) :
    (1 - r) ^ 2 * q 0 ≤ q 1 ∧ q 1 ≤ q 0 / (1 - r) ^ 2 := by
  classical
  have hden : ∀ t ∈ Set.Icc (0:ℝ) 1, (0:ℝ) < 1 - r * t := by
    intro t ht
    nlinarith only [ht.1, ht.2, hr0, hr1]
  have hlogd : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun s => Real.log (1 - r * s)) (-r / (1 - r * t)) t := by
    intro t ht
    have hin : HasDerivAt (fun s : ℝ => 1 - r * s) (-r) t := by
      simpa using (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).const_mul r)
    exact hin.log (ne_of_gt (hden t ht))
  have hqld : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun s => Real.log (q s)) (q' t / q t) t := fun t ht =>
    (hqd t (hIcc ht)).log (ne_of_gt (hqpos t (hIcc ht)))
  -- upper: `log q + 2 log (1 - r t)` is antitone
  have hup : q 1 ≤ q 0 / (1 - r) ^ 2 := by
    have hanti : AntitoneOn (fun t => Real.log (q t) + 2 * Real.log (1 - r * t))
        (Set.Icc (0:ℝ) 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
      · intro t ht
        exact (((hqld t ht).add ((hlogd t ht).const_mul 2)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hqld t (Set.mem_Icc_of_Ioo ht)).add
          ((hlogd t (Set.mem_Icc_of_Ioo ht)).const_mul 2)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ioo ht
        have hd : HasDerivAt (fun s => Real.log (q s) + 2 * Real.log (1 - r * s))
            (q' t / q t + 2 * (-r / (1 - r * t))) t := (hqld t htI).add ((hlogd t htI).const_mul 2)
        rw [hd.deriv]
        have hb := (abs_le.mp (hbnd t htI)).2
        have hqp := hqpos t (hIcc htI)
        have hdp := hden t htI
        have hle : q' t / q t ≤ 2 * r / (1 - r * t) := by
          rw [div_le_iff₀ hqp]
          exact hb
        have h2 : 2 * (-r / (1 - r * t)) = -(2 * r / (1 - r * t)) := by ring
        rw [h2]
        linarith [hle]
    have hcmp := hanti (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))
      (by norm_num)
    simp only [mul_zero, mul_one, sub_zero, Real.log_one, mul_zero, add_zero] at hcmp
    have hq0 := hqpos 0 (hIcc (Set.left_mem_Icc.mpr (by norm_num)))
    have hq1 := hqpos 1 (hIcc (Set.right_mem_Icc.mpr (by norm_num)))
    have hrr : (0:ℝ) < 1 - r := by linarith
    have hlg : Real.log (q 1) + 2 * Real.log (1 - r) ≤ Real.log (q 0) := hcmp
    have hexp : Real.log (q 1 * (1 - r) ^ 2) ≤ Real.log (q 0) := by
      rw [Real.log_mul (ne_of_gt hq1) (by positivity), Real.log_pow]
      push_cast
      linarith
    have hAB : q 1 * (1 - r) ^ 2 ≤ q 0 := by
      have h1 : Real.exp (Real.log (q 1 * (1 - r) ^ 2)) ≤ Real.exp (Real.log (q 0)) :=
        Real.exp_le_exp.mpr hexp
      rwa [Real.exp_log (by positivity), Real.exp_log hq0] at h1
    rw [le_div_iff₀ (by positivity)]
    linarith [hAB]
  -- lower: `log q - 2 log (1 - r t)` is monotone
  have hlow : (1 - r) ^ 2 * q 0 ≤ q 1 := by
    have hmono : MonotoneOn (fun t => Real.log (q t) - 2 * Real.log (1 - r * t))
        (Set.Icc (0:ℝ) 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
      · intro t ht
        exact (((hqld t ht).sub ((hlogd t ht).const_mul 2)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hqld t (Set.mem_Icc_of_Ioo ht)).sub
          ((hlogd t (Set.mem_Icc_of_Ioo ht)).const_mul 2)).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ioo ht
        have hd : HasDerivAt (fun s => Real.log (q s) - 2 * Real.log (1 - r * s))
            (q' t / q t - 2 * (-r / (1 - r * t))) t := (hqld t htI).sub ((hlogd t htI).const_mul 2)
        rw [hd.deriv]
        have hb := (abs_le.mp (hbnd t htI)).1
        have hqp := hqpos t (hIcc htI)
        have hdp := hden t htI
        have hge : -(2 * r / (1 - r * t)) ≤ q' t / q t := by
          rw [le_div_iff₀ hqp]
          linarith [hb]
        have h2 : 2 * (-r / (1 - r * t)) = -(2 * r / (1 - r * t)) := by ring
        rw [h2]
        linarith [hge]
    have hcmp := hmono (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))
      (by norm_num)
    simp only [mul_zero, mul_one, sub_zero, Real.log_one, mul_zero, sub_zero] at hcmp
    have hq0 := hqpos 0 (hIcc (Set.left_mem_Icc.mpr (by norm_num)))
    have hq1 := hqpos 1 (hIcc (Set.right_mem_Icc.mpr (by norm_num)))
    have hrr : (0:ℝ) < 1 - r := by linarith
    have hexp : Real.log ((1 - r) ^ 2 * q 0) ≤ Real.log (q 1) := by
      rw [Real.log_mul (by positivity) (ne_of_gt hq0), Real.log_pow]
      push_cast
      linarith [hcmp]
    have h1 : Real.exp (Real.log ((1 - r) ^ 2 * q 0)) ≤ Real.exp (Real.log (q 1)) :=
      Real.exp_le_exp.mpr hexp
    rwa [Real.exp_log (by positivity), Real.exp_log hq1] at h1
  exact ⟨hlow, hup⟩

/-- A symmetric form dominated on the diagonal by `κ Q` is dominated off-diagonal too. -/
theorem sym_form_bound
    (Q D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hDsym : ∀ a b, ⟪D a, b⟫ = ⟪D b, a⟫)
    (hQpd : ∀ a : EuclideanSpace ℝ (Fin n), a ≠ 0 → 0 < ⟪Q a, a⟫)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hdiag : ∀ a, |⟪D a, a⟫| ≤ κ * ⟪Q a, a⟫) :
    ∀ a b, |⟪D a, b⟫| ≤ κ * Real.sqrt ⟪Q a, a⟫ * Real.sqrt ⟪Q b, b⟫ := by
  classical
  have hQnn : ∀ a : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪Q a, a⟫ := by
    intro a
    by_cases h : a = 0
    · simp [h]
    · exact (hQpd a h).le
  -- polarisation
  have hpol : ∀ a b : EuclideanSpace ℝ (Fin n),
      |⟪D a, b⟫| ≤ κ / 2 * (⟪Q a, a⟫ + ⟪Q b, b⟫) := by
    intro a b
    have hexp : ⟪D (a + b), a + b⟫ - ⟪D (a - b), a - b⟫ = 4 * ⟪D a, b⟫ := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      rw [hDsym b a]
      ring
    have hQexp : ⟪Q (a + b), a + b⟫ + ⟪Q (a - b), a - b⟫ = 2 * (⟪Q a, a⟫ + ⟪Q b, b⟫) := by
      have hQsym : ∀ p q : EuclideanSpace ℝ (Fin n), ⟪Q p, q⟫ + ⟪Q q, p⟫
          = ⟪Q (p + q), p + q⟫ - ⟪Q p, p⟫ - ⟪Q q, q⟫ := by
        intro p q
        simp only [map_add, inner_add_left, inner_add_right]
        ring
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      ring
    have h1 := hdiag (a + b)
    have h2 := hdiag (a - b)
    have habs : |4 * ⟪D a, b⟫| ≤ |⟪D (a + b), a + b⟫| + |⟪D (a - b), a - b⟫| := by
      rw [← hexp, sub_eq_add_neg]
      calc |⟪D (a + b), a + b⟫ + -⟪D (a - b), a - b⟫|
          ≤ |⟪D (a + b), a + b⟫| + |-⟪D (a - b), a - b⟫| := abs_add_le _ _
        _ = |⟪D (a + b), a + b⟫| + |⟪D (a - b), a - b⟫| := by rw [abs_neg]
    rw [abs_mul, show |(4:ℝ)| = 4 by norm_num] at habs
    nlinarith only [habs, h1, h2, hQexp, hκ]
  intro a b
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hQa : 0 < ⟪Q a, a⟫ := hQpd a ha
  have hQb : 0 < ⟪Q b, b⟫ := hQpd b hb
  set sa := Real.sqrt ⟪Q a, a⟫ with hsa
  set sb := Real.sqrt ⟪Q b, b⟫ with hsb
  have hsap : 0 < sa := Real.sqrt_pos.mpr hQa
  have hsbp : 0 < sb := Real.sqrt_pos.mpr hQb
  have hsa2 : sa ^ 2 = ⟪Q a, a⟫ := Real.sq_sqrt hQa.le
  have hsb2 : sb ^ 2 = ⟪Q b, b⟫ := Real.sq_sqrt hQb.le
  set c : ℝ := Real.sqrt (sb / sa) with hc
  have hcp : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = sb / sa := Real.sq_sqrt (by positivity)
  have hkey := hpol (c • a) (c⁻¹ • b)
  rw [map_smul, real_inner_smul_left, real_inner_smul_right, map_smul, real_inner_smul_left,
    real_inner_smul_right, map_smul, real_inner_smul_left, real_inner_smul_right] at hkey
  rw [show c * (c⁻¹ * ⟪D a, b⟫) = ⟪D a, b⟫ by field_simp] at hkey
  rw [show c * (c * ⟪Q a, a⟫) = c ^ 2 * ⟪Q a, a⟫ by ring,
    show c⁻¹ * (c⁻¹ * ⟪Q b, b⟫) = (c ^ 2)⁻¹ * ⟪Q b, b⟫ by field_simp] at hkey
  rw [hc2, ← hsa2, ← hsb2] at hkey
  have hsimp : sb / sa * sa ^ 2 + (sb / sa)⁻¹ * sb ^ 2 = 2 * (sa * sb) := by
    field_simp
    ring
  rw [hsimp] at hkey
  calc |⟪D a, b⟫| ≤ κ / 2 * (2 * (sa * sb)) := hkey
    _ = κ * sa * sb := by ring

end SCUp

namespace SCUp

/-- `log_comparison` on an arbitrary right endpoint `b`, obtained by rescaling. -/
theorem log_comparison' (S : Set ℝ) (b : ℝ) (hb : 0 ≤ b) (hIcc : Set.Icc (0:ℝ) b ⊆ S)
    (q q' : ℝ → ℝ) (hqd : ∀ t ∈ S, HasDerivAt q (q' t) t) (hqpos : ∀ t ∈ S, 0 < q t)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρb : ρ * b < 1)
    (hbnd : ∀ t ∈ Set.Icc (0:ℝ) b, |q' t| ≤ 2 * ρ / (1 - ρ * t) * q t) :
    (1 - ρ * b) ^ 2 * q 0 ≤ q b ∧ q b ≤ q 0 / (1 - ρ * b) ^ 2 := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst_vars
    simp
  -- rescale `t ↦ b t`
  set S' : Set ℝ := {t : ℝ | b * t ∈ S} with hS'
  have hIcc' : Set.Icc (0:ℝ) 1 ⊆ S' := by
    intro t ht
    have h1 : (0:ℝ) ≤ b * t := mul_nonneg hbpos.le ht.1
    have h2 : b * t ≤ b := by nlinarith only [ht.1, ht.2, hbpos]
    exact hIcc ⟨h1, h2⟩
  set Q : ℝ → ℝ := fun t => q (b * t) with hQ
  set Q' : ℝ → ℝ := fun t => b * q' (b * t) with hQ'
  have hQd : ∀ t ∈ S', HasDerivAt Q (Q' t) t := by
    intro t ht
    have hin : HasDerivAt (fun s : ℝ => b * s) b t := by
      simpa using (hasDerivAt_id t).const_mul b
    have := (hqd _ ht).comp t hin
    simpa [hQ, hQ', mul_comm] using this
  have hQpos : ∀ t ∈ S', 0 < Q t := fun t ht => hqpos _ ht
  have hbnd' : ∀ t ∈ Set.Icc (0:ℝ) 1,
      |Q' t| ≤ 2 * (ρ * b) / (1 - (ρ * b) * t) * Q t := by
    intro t ht
    have hmem : b * t ∈ Set.Icc (0:ℝ) b := by
      refine ⟨mul_nonneg hbpos.le ht.1, ?_⟩
      nlinarith only [ht.1, ht.2, hbpos]
    have hden : (0:ℝ) < 1 - ρ * (b * t) := by
      nlinarith only [mul_nonneg (mul_nonneg hρ0 hbpos.le) (sub_nonneg.mpr ht.2), hρb]
    have h := hbnd _ hmem
    have habs : |Q' t| = b * |q' (b * t)| := by
      rw [hQ']
      simp only [abs_mul, abs_of_pos hbpos]
    rw [habs]
    have hrw : 2 * (ρ * b) / (1 - ρ * b * t) * Q t = b * (2 * ρ / (1 - ρ * (b * t)) * q (b * t)) := by
      rw [hQ]
      rw [show ρ * b * t = ρ * (b * t) by ring]
      field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_left h hbpos.le
  have hmain := log_comparison S' hIcc' Q Q' hQd hQpos (ρ * b) (by positivity) hρb hbnd'
  simpa [hQ] using hmain

end SCUp


-- ## The Newton-decrement contraction

namespace NCAux

variable {n : ℕ}

/-- Symmetry of the Hessian field. -/
theorem hess_symm {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩo : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪H x a, b⟫ = ⟪H x b, a⟫ := by
  have hf' : ∀ᶠ z in 𝓝 x, HasFDerivAt f (DHAux.rieszL n (g z)) z := by
    filter_upwards [hΩo.mem_nhds hx] with z hz
    exact (hg z hz).hasFDerivAt
  have hf'' : HasFDerivAt (fun z => DHAux.rieszL n (g z)) ((DHAux.rieszL n).comp (H x)) x :=
    (DHAux.rieszL n).hasFDerivAt.comp x (hH x hx)
  have hsymm := second_derivative_symmetric_of_eventually hf' hf'' a b
  simpa using hsymm

/-- **B&V (9.55).**  One full Newton step from `x` stays in the domain and squares the
Newton decrement, up to the factor `(1 - λ)⁻²`. -/
theorem newton_contraction
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (hclosed : ∀ c : ℝ, IsClosed {y | y ∈ Ω ∧ f y ≤ c})
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (Δ : EuclideanSpace ℝ (Fin n)) (hΔ : H x Δ = -g x)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam ^ 2 = ⟪g x, -Δ⟫) (hlt : lam < 1) :
    x + Δ ∈ Ω ∧
    ∀ (Δ' : EuclideanSpace ℝ (Fin n)) (lam' : ℝ),
      H (x + Δ) Δ' = -g (x + Δ) → 0 ≤ lam' → lam' ^ 2 = ⟪g (x + Δ), -Δ'⟫ →
      lam' ≤ (lam / (1 - lam)) ^ 2 := by
  classical
  -- ## Structural facts about the Hessian field and its derivative
  have hHs : ∀ y ∈ Ω, ∀ a b, ⟪H y a, b⟫ = ⟪H y b, a⟫ := fun y hy a b =>
    hess_symm hΩo f g hg H hH y hy a b
  have hHnn : ∀ y ∈ Ω, ∀ v : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪H y v, v⟫ := by
    intro y hy v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hHpd y hy v hv).le
  set DHf : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    fun y => fderiv ℝ H y with hDHf
  have hDH : ∀ y ∈ Ω, HasFDerivAt H (DHf y) y := fun y hy =>
    (DHAux.hessian_differentiable Ω hΩo f hsc.2.1 g hg H hH y hy).hasFDerivAt
  have hdiag : ∀ y ∈ Ω, ∀ v, |⟪DHf y v v, v⟫| ≤ 2 * (⟪H y v, v⟫) ^ ((3:ℝ)/2) := by
    intro y hy v
    have h3 := DHAux.iteratedDeriv3_eq (Ω := Ω) (f := f) (g := g) (H := H) hΩo hg hH y hy
      (DHf y) (hDH y hy) v
    have h2 := DHAux.iteratedDeriv2_eq Ω hΩo f g hg H hH y hy v
    have hb := hsc.2.2 y hy v
    rw [h3, h2] at hb
    exact hb
  have hmix : ∀ y ∈ Ω, ∀ u w : EuclideanSpace ℝ (Fin n),
      |⟪DHf y u w, w⟫| ≤ 2 * Real.sqrt ⟪H y u, u⟫ * ⟪H y w, w⟫ := by
    intro y hy
    refine TriAux.trilinear_sharp (H y) (DHf y) (hHs y hy) (hHpd y hy) ?_ ?_ (hdiag y hy)
    · exact fun a b => DHAux.DH_sym12 (Ω := Ω) (g := g) (H := H) hΩo hH y hy (DHf y) (hDH y hy) a b
    · exact fun a b c =>
        DHAux.DH_sym23 (Ω := Ω) (H := H) hΩo hHs y hy (DHf y) (hDH y hy) a b c
  have hlamsq : lam ^ 2 = ⟪H x Δ, Δ⟫ := by
    rw [hlam, hΔ]; simp
  -- ## Degenerate case: the Newton step vanishes
  by_cases hΔ0 : Δ = 0
  · subst hΔ0
    have hgx : g x = 0 := by
      have h : (0 : EuclideanSpace ℝ (Fin n)) = -g x := by simpa using hΔ
      exact neg_eq_zero.mp h.symm
    refine ⟨by simpa using hx, ?_⟩
    intro Δ' lam' hΔ' hlam'0 hlam'
    have hxx : x + (0 : EuclideanSpace ℝ (Fin n)) = x := by simp
    rw [hxx, hgx] at hΔ' hlam'
    have hΔ'0 : Δ' = 0 := by
      by_contra hne
      have hpos := hHpd x hx Δ' hne
      rw [hΔ'] at hpos
      simp at hpos
    have hz : lam' ^ 2 = 0 := by rw [hlam', hΔ'0]; simp
    have hz2 : lam' = 0 := by nlinarith only [hlam'0, hz]
    rw [hz2]; positivity
  -- ## Main case
  have hlampos : 0 < lam := by
    have h := hHpd x hx Δ hΔ0
    nlinarith only [hlamsq, hlam0, h]
  have h1l : (0:ℝ) < 1 - lam := by linarith
  -- the slice of `Ω` along the Newton direction
  set S : Set ℝ := {t : ℝ | x + t • Δ ∈ Ω} with hS
  have hSopen : IsOpen S := hΩo.preimage (by fun_prop)
  have hSconv : Convex ℝ S := by
    intro a ha b hb p q hp hq hpq
    have ha' : x + a • Δ ∈ Ω := ha
    have hb' : x + b • Δ ∈ Ω := hb
    have hmem : p • (x + a • Δ) + q • (x + b • Δ) ∈ Ω := hΩc ha' hb' hp hq hpq
    have hrw : p • (x + a • Δ) + q • (x + b • Δ) = x + (p * a + q * b) • Δ := by
      have h1 : p • (x + a • Δ) + q • (x + b • Δ) = (p + q) • x + (p * a + q * b) • Δ := by
        module
      rw [h1, hpq, one_smul]
    rw [hrw] at hmem
    exact hmem
  have h0S : (0:ℝ) ∈ S := by simpa [hS] using hx
  -- the second derivative along the ray
  set φ : ℝ → ℝ := fun t => ⟪H (x + t • Δ) Δ, Δ⟫ with hφdef
  set φ' : ℝ → ℝ := fun t => ⟪DHf (x + t • Δ) Δ Δ, Δ⟫ with hφ'def
  have hφd : ∀ t ∈ S, HasDerivAt φ (φ' t) t := fun t ht =>
    DHAux.hess_line_deriv Ω H DHf hDH x Δ Δ Δ t ht
  have hφpos : ∀ t ∈ S, 0 < φ t := fun t ht => hHpd _ ht Δ hΔ0
  have hφsc : ∀ t ∈ S, |φ' t| ≤ 2 * (φ t) ^ ((3:ℝ)/2) := fun t ht => hdiag _ ht Δ
  have hφ0 : φ 0 = lam ^ 2 := by
    show (⟪H (x + (0:ℝ) • Δ) Δ, Δ⟫ : ℝ) = lam ^ 2
    rw [show x + (0:ℝ) • Δ = x by simp]
    exact hlamsq.symm
  have hφub : ∀ b : ℝ, 0 ≤ b → b ≤ 1 → Set.Icc (0:ℝ) b ⊆ S →
      ∀ t ∈ Set.Icc (0:ℝ) b, φ t ≤ lam ^ 2 / (1 - lam * t) ^ 2 := by
    intro b hb hb1 hIccb t ht
    have h := (SCUp.u_bounds S hSconv b hb hIccb φ φ' hφd hφpos hφsc t ht).2
    rw [hφ0, Real.sqrt_sq hlam0] at h
    refine h ?_
    have ht1 : t ≤ 1 := le_trans ht.2 hb1
    nlinarith only [ht.1, hlampos, hlt, ht1]
  -- ## Step 1: the Dikin ellipsoid — the full Newton step stays in `Ω`
  have hbound1 : (1:ℝ) ∈ S := by
    by_contra h1notS
    set A : Set ℝ := S ∩ Set.Icc (0:ℝ) 1 with hA
    have hA0 : (0:ℝ) ∈ A := ⟨h0S, by norm_num⟩
    have hAne : A.Nonempty := ⟨0, hA0⟩
    have hAbdd : BddAbove A := ⟨1, fun z hz => hz.2.2⟩
    set T : ℝ := sSup A with hTdef
    have hT0 : (0:ℝ) ≤ T := le_csSup hAbdd hA0
    have hT1 : T ≤ 1 := csSup_le hAne (fun z hz => hz.2.2)
    have hsub : ∀ t : ℝ, 0 ≤ t → t < T → t ∈ S := by
      intro t ht0 htT
      obtain ⟨s, hsA, hts⟩ := exists_lt_of_lt_csSup hAne htT
      have hspos : (0:ℝ) < s := lt_of_le_of_lt ht0 hts
      have hc1 : (0:ℝ) ≤ 1 - t / s := by
        have h := (div_le_one hspos).mpr hts.le
        linarith
      have hc2 : (0:ℝ) ≤ t / s := div_nonneg ht0 hspos.le
      have hmem := hSconv h0S hsA.1 hc1 hc2 (by ring)
      have hrw : (1 - t / s) • (0:ℝ) + (t / s) • s = t := by
        simp only [smul_eq_mul, mul_zero, zero_add]
        field_simp
      rwa [hrw] at hmem
    have hTS : T ∉ S := by
      intro hTmem
      rcases eq_or_lt_of_le hT1 with hTeq | hTlt
      · exact h1notS (hTeq ▸ hTmem)
      · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hSopen T hTmem
        have hTu : T < min (T + ε / 2) 1 := lt_min (by linarith) hTlt
        have huS : min (T + ε / 2) 1 ∈ S := by
          refine hball ?_
          simp only [Metric.mem_ball, Real.dist_eq]
          have h1 : min (T + ε / 2) 1 ≤ T + ε / 2 := min_le_left _ _
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ min (T + ε / 2) 1 - T)]
          linarith
        have huA : min (T + ε / 2) 1 ∈ A :=
          ⟨huS, ⟨by linarith, min_le_right _ _⟩⟩
        have hle := le_csSup hAbdd huA
        linarith
    have hTpos : (0:ℝ) < T := lt_of_le_of_ne hT0 (fun h => hTS (h ▸ h0S))
    -- an a-priori bound on `f` along `[0, T)`
    set C : ℝ := lam ^ 2 / (1 - lam) ^ 2 with hC
    have hCnn : (0:ℝ) ≤ C := by rw [hC]; positivity
    set D1 : ℝ → ℝ := fun s => ⟪g (x + s • Δ), Δ⟫ with hD1def
    have hD1d : ∀ s ∈ S, HasDerivAt D1 (φ s) s := fun s hs =>
      DHAux.grad_line_deriv Ω g H hH x Δ Δ s hs
    have hFd : ∀ s ∈ S, HasDerivAt (fun r : ℝ => f (x + r • Δ)) (D1 s) s := fun s hs =>
      DHAux.fun_line_deriv Ω f g hg x Δ s hs
    have hD10 : D1 0 = ⟪g x, Δ⟫ := by
      show (⟪g (x + (0:ℝ) • Δ), Δ⟫ : ℝ) = ⟪g x, Δ⟫
      rw [show x + (0:ℝ) • Δ = x by simp]
    set c : ℝ := f x + |⟪g x, Δ⟫| + C / 2 with hcdef
    have hkey : ∀ b : ℝ, 0 ≤ b → b < T → f (x + b • Δ) ≤ c := by
      intro b hb hbT
      have hIccb : Set.Icc (0:ℝ) b ⊆ S := fun s hs => hsub s hs.1 (lt_of_le_of_lt hs.2 hbT)
      have hb1 : b ≤ 1 := le_trans hbT.le hT1
      have hφC : ∀ s ∈ Set.Icc (0:ℝ) b, φ s ≤ C := by
        intro s hs
        have h1 := hφub b hb hb1 hIccb s hs
        have hs1 : s ≤ 1 := le_trans hs.2 hb1
        have hd2 : 1 - lam ≤ 1 - lam * s := by nlinarith only [hs.1, hlam0, hs1]
        have hsq : (1 - lam) ^ 2 ≤ (1 - lam * s) ^ 2 := pow_le_pow_left₀ h1l.le hd2 2
        have h2 : lam ^ 2 / (1 - lam * s) ^ 2 ≤ C := by
          rw [hC, div_le_div_iff₀ (pow_pos (by linarith : (0:ℝ) < 1 - lam * s) 2)
            (pow_pos h1l 2)]
          nlinarith only [mul_le_mul_of_nonneg_left hsq (sq_nonneg lam)]
        linarith
      -- first integration: `D1 s ≤ D1 0 + C s`
      have hstep1 : ∀ s ∈ Set.Icc (0:ℝ) b, D1 s ≤ D1 0 + C * s := by
        have hlin : ∀ s : ℝ, HasDerivAt (fun r : ℝ => C * r) C s := by
          intro s; simpa using (hasDerivAt_id s).const_mul C
        have hanti : AntitoneOn (fun s => D1 s - C * s) (Set.Icc (0:ℝ) b) := by
          refine antitoneOn_of_deriv_nonpos (convex_Icc 0 b) ?_ ?_ ?_
          · intro s hs
            exact (((hD1d s (hIccb hs)).sub (hlin s)).continuousAt).continuousWithinAt
          · intro s hs
            rw [interior_Icc] at hs
            exact (((hD1d s (hIccb (Set.mem_Icc_of_Ioo hs))).sub
              (hlin s)).differentiableAt).differentiableWithinAt
          · intro s hs
            rw [interior_Icc] at hs
            have hsI : s ∈ Set.Icc (0:ℝ) b := Set.mem_Icc_of_Ioo hs
            have hd : HasDerivAt (fun r : ℝ => D1 r - C * r) (φ s - C) s :=
              (hD1d s (hIccb hsI)).sub (hlin s)
            rw [hd.deriv]
            linarith [hφC s hsI]
        intro s hs
        have h := hanti (Set.left_mem_Icc.mpr hb) hs hs.1
        simp only [mul_zero, sub_zero] at h
        linarith
      -- second integration: `f (x + bΔ) ≤ f x + D1 0 · b + C b²/2`
      have hstep2 : f (x + b • Δ) ≤ f x + D1 0 * b + C * b ^ 2 / 2 := by
        have hlin2 : ∀ s : ℝ,
            HasDerivAt (fun r : ℝ => D1 0 * r + C * r ^ 2 / 2) (D1 0 + C * s) s := by
          intro s
          have h1 : HasDerivAt (fun r : ℝ => D1 0 * r) (D1 0) s := by
            simpa using (hasDerivAt_id s).const_mul (D1 0)
          have h2 : HasDerivAt (fun r : ℝ => C * r ^ 2 / 2) (C * s) s := by
            have h := ((hasDerivAt_pow 2 s).const_mul C).div_const 2
            refine h.congr_deriv ?_
            push_cast
            ring
          exact h1.add h2
        have hanti : AntitoneOn (fun s => f (x + s • Δ) - (D1 0 * s + C * s ^ 2 / 2))
            (Set.Icc (0:ℝ) b) := by
          refine antitoneOn_of_deriv_nonpos (convex_Icc 0 b) ?_ ?_ ?_
          · intro s hs
            exact (((hFd s (hIccb hs)).sub (hlin2 s)).continuousAt).continuousWithinAt
          · intro s hs
            rw [interior_Icc] at hs
            exact (((hFd s (hIccb (Set.mem_Icc_of_Ioo hs))).sub
              (hlin2 s)).differentiableAt).differentiableWithinAt
          · intro s hs
            rw [interior_Icc] at hs
            have hsI : s ∈ Set.Icc (0:ℝ) b := Set.mem_Icc_of_Ioo hs
            have hd : HasDerivAt (fun r : ℝ => f (x + r • Δ) - (D1 0 * r + C * r ^ 2 / 2))
                (D1 s - (D1 0 + C * s)) s := (hFd s (hIccb hsI)).sub (hlin2 s)
            rw [hd.deriv]
            linarith [hstep1 s hsI]
        have h := hanti (Set.left_mem_Icc.mpr hb) (Set.right_mem_Icc.mpr hb) hb
        simp only [zero_smul, add_zero, mul_zero, zero_add] at h
        norm_num at h
        linarith
      have habs : D1 0 * b ≤ |⟪g x, Δ⟫| := by
        rw [hD10]
        nlinarith only [le_abs_self ⟪g x, Δ⟫, abs_nonneg ⟪g x, Δ⟫, hb, hb1]
      have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
      have hCb : C * b ^ 2 / 2 ≤ C / 2 := by
        nlinarith only [mul_nonneg hCnn (sub_nonneg.mpr hb2)]
      rw [hcdef]
      linarith
    -- pass to the limit: the sublevel set is closed
    have htend : Filter.Tendsto (fun t : ℝ => x + t • Δ) (𝓝[<] T) (𝓝 (x + T • Δ)) :=
      (Continuous.tendsto (by fun_prop) T).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[<] T, (x + t • Δ) ∈ {y | y ∈ Ω ∧ f y ≤ c} := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds hTpos).filter_mono nhdsWithin_le_nhds] with t ht1 ht2
      exact ⟨hsub t ht2.le ht1, hkey t ht2.le ht1⟩
    exact hTS ((hclosed c).mem_of_tendsto htend hev).1
  have hIcc1 : Set.Icc (0:ℝ) 1 ⊆ S := by
    intro t ht
    have h := hSconv h0S hbound1 (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1 (by ring)
    simpa using h
  have hxΔ : x + Δ ∈ Ω := by
    have h : x + (1:ℝ) • Δ ∈ Ω := hbound1
    simpa using h
  refine ⟨hxΔ, ?_⟩
  intro Δ' lam' hΔ' hlam'0 hlam'
  by_cases hΔ'0 : Δ' = 0
  · subst hΔ'0
    have hz : lam' ^ 2 = 0 := by rw [hlam']; simp
    have hz2 : lam' = 0 := by nlinarith only [hlam'0, hz]
    rw [hz2]; positivity
  have hlam'sq : lam' ^ 2 = ⟪H (x + Δ) Δ', Δ'⟫ := by
    rw [hlam', hΔ']; simp
  have hlam'pos : 0 < lam' := by
    have h := hHpd _ hxΔ Δ' hΔ'0
    nlinarith only [hlam'sq, hlam'0, h]
  set K : ℝ := Real.sqrt ⟪H x Δ', Δ'⟫ with hKdef
  have hKnn : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K ^ 2 = ⟪H x Δ', Δ'⟫ := Real.sq_sqrt (hHnn x hx Δ')
  -- ## Step 2: the third-derivative bound along the segment
  have hgenbnd : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ v : EuclideanSpace ℝ (Fin n),
      |⟪DHf (x + s • Δ) Δ v, v⟫| ≤ 2 * lam / (1 - lam * s) * ⟪H (x + s • Δ) v, v⟫ := by
    intro s hs v
    have hmem : x + s • Δ ∈ Ω := hIcc1 hs
    have h1 := hmix _ hmem Δ v
    have hden : (0:ℝ) < 1 - lam * s := by nlinarith only [hs.1, hs.2, hlam0, hlt]
    have hφs : φ s ≤ lam ^ 2 / (1 - lam * s) ^ 2 := hφub 1 (by norm_num) le_rfl hIcc1 s hs
    have hsqle : Real.sqrt (φ s) ≤ lam / (1 - lam * s) := by
      have h2 : φ s ≤ (lam / (1 - lam * s)) ^ 2 := by rw [div_pow]; exact hφs
      calc Real.sqrt (φ s) ≤ Real.sqrt ((lam / (1 - lam * s)) ^ 2) := Real.sqrt_le_sqrt h2
        _ = lam / (1 - lam * s) := Real.sqrt_sq (div_nonneg hlam0 hden.le)
    have hQnn : 0 ≤ ⟪H (x + s • Δ) v, v⟫ := hHnn _ hmem v
    have hstep : |⟪DHf (x + s • Δ) Δ v, v⟫| ≤
        2 * Real.sqrt (φ s) * ⟪H (x + s • Δ) v, v⟫ := h1
    have hfin : 2 * Real.sqrt (φ s) * ⟪H (x + s • Δ) v, v⟫ ≤
        2 * lam / (1 - lam * s) * ⟪H (x + s • Δ) v, v⟫ := by
      have hrw : 2 * lam / (1 - lam * s) = 2 * (lam / (1 - lam * s)) := by ring
      rw [hrw]
      nlinarith only [hsqle, hQnn, Real.sqrt_nonneg (φ s)]
    linarith
  -- ## Step 3: two-sided Hessian comparison along the segment
  have hOp : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ v : EuclideanSpace ℝ (Fin n),
      |⟪H (x + t • Δ) v, v⟫ - ⟪H x v, v⟫| ≤ (1 / (1 - lam * t) ^ 2 - 1) * ⟪H x v, v⟫ := by
    intro t ht v
    have hden : (0:ℝ) < 1 - lam * t := by nlinarith only [ht.1, ht.2, hlam0, hlt]
    have ha : (0:ℝ) < (1 - lam * t) ^ 2 := pow_pos hden 2
    have hQnn : 0 ≤ ⟪H x v, v⟫ := hHnn x hx v
    by_cases hv : v = 0
    · subst hv; simp
    have hIcct : Set.Icc (0:ℝ) t ⊆ S := fun s hs => hIcc1 ⟨hs.1, le_trans hs.2 ht.2⟩
    have hcmp := SCUp.log_comparison' S t ht.1 hIcct
      (fun s => ⟪H (x + s • Δ) v, v⟫) (fun s => ⟪DHf (x + s • Δ) Δ v, v⟫)
      (fun s hs => DHAux.hess_line_deriv Ω H DHf hDH x Δ v v s hs)
      (fun s hs => hHpd _ hs v hv)
      lam hlam0 (by nlinarith only [ht.1, ht.2, hlam0, hlt])
      (fun s hs => hgenbnd s ⟨hs.1, le_trans hs.2 ht.2⟩ v)
    simp only [zero_smul, add_zero] at hcmp
    obtain ⟨hlo, hup⟩ := hcmp
    have hRa : ⟪H (x + t • Δ) v, v⟫ * (1 - lam * t) ^ 2 ≤ ⟪H x v, v⟫ := (le_div_iff₀ ha).mp hup
    have hκa : (1 / (1 - lam * t) ^ 2 - 1) * ⟪H x v, v⟫ * (1 - lam * t) ^ 2
        = ⟪H x v, v⟫ - (1 - lam * t) ^ 2 * ⟪H x v, v⟫ := by
      field_simp
    rw [abs_le]
    constructor
    · refine le_of_mul_le_mul_right ?_ ha
      rw [neg_mul, hκa]
      nlinarith only [mul_le_mul_of_nonneg_right hlo ha.le,
        mul_nonneg hQnn (sq_nonneg ((1 - lam * t) ^ 2 - 1))]
    · refine le_of_mul_le_mul_right ?_ ha
      rw [hκa]
      nlinarith only [hRa]
  -- polarised form of the comparison, applied to `(Δ, Δ')`
  have hD : ∀ t ∈ Set.Icc (0:ℝ) 1,
      |⟪H (x + t • Δ) Δ, Δ'⟫ - ⟪H x Δ, Δ'⟫| ≤ (1 / (1 - lam * t) ^ 2 - 1) * lam * K := by
    intro t ht
    have hmem : x + t • Δ ∈ Ω := hIcc1 ht
    have hden : (0:ℝ) < 1 - lam * t := by nlinarith only [ht.1, ht.2, hlam0, hlt]
    have h0lt : (0:ℝ) ≤ lam * t := mul_nonneg hlam0 ht.1
    have hle1 : (1 - lam * t) ^ 2 ≤ 1 := by
      nlinarith only [h0lt, hden, mul_nonneg h0lt (by linarith : (0:ℝ) ≤ 2 - lam * t)]
    have hκ0 : (0:ℝ) ≤ 1 / (1 - lam * t) ^ 2 - 1 := by
      have ha : (0:ℝ) < (1 - lam * t) ^ 2 := pow_pos hden 2
      rw [sub_nonneg, le_div_iff₀ ha]
      linarith
    have hsym : ∀ a b : EuclideanSpace ℝ (Fin n),
        ⟪(H (x + t • Δ) - H x) a, b⟫ = ⟪(H (x + t • Δ) - H x) b, a⟫ := by
      intro a b
      simp only [ContinuousLinearMap.sub_apply, inner_sub_left]
      rw [hHs _ hmem a b, hHs x hx a b]
    have hdg : ∀ a : EuclideanSpace ℝ (Fin n),
        |⟪(H (x + t • Δ) - H x) a, a⟫| ≤ (1 / (1 - lam * t) ^ 2 - 1) * ⟪H x a, a⟫ := by
      intro a
      simp only [ContinuousLinearMap.sub_apply, inner_sub_left]
      exact hOp t ht a
    have h := SCUp.sym_form_bound (H x) (H (x + t • Δ) - H x) hsym (hHpd x hx) _ hκ0 hdg Δ Δ'
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left] at h
    rw [show Real.sqrt ⟪H x Δ, Δ⟫ = lam by rw [← hlamsq, Real.sqrt_sq hlam0]] at h
    exact h
  -- ## Step 4: the gradient increment
  set E : ℝ → ℝ := fun t => ⟪g (x + t • Δ), Δ'⟫ - ⟪g x, Δ'⟫ - t * ⟪H x Δ, Δ'⟫ with hEdef
  set M : ℝ → ℝ := fun t => K * lam ^ 2 * t ^ 2 / (1 - lam * t) with hMdef
  have hEd : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt E (⟪H (x + t • Δ) Δ, Δ'⟫ - ⟪H x Δ, Δ'⟫) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => ⟪g (x + s • Δ), Δ'⟫) ⟪H (x + t • Δ) Δ, Δ'⟫ t :=
      DHAux.grad_line_deriv Ω g H hH x Δ Δ' t (hIcc1 ht)
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪H x Δ, Δ'⟫) ⟪H x Δ, Δ'⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪H x Δ, Δ'⟫
    exact (h1.sub_const ⟪g x, Δ'⟫).sub h2
  have hMd : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt M ((1 / (1 - lam * t) ^ 2 - 1) * lam * K) t := by
    intro t ht
    have hden : (0:ℝ) < 1 - lam * t := by nlinarith only [ht.1, ht.2, hlam0, hlt]
    have hnum : HasDerivAt (fun s : ℝ => K * lam ^ 2 * s ^ 2) (K * lam ^ 2 * (2 * t)) t := by
      have h := (hasDerivAt_pow 2 t).const_mul (K * lam ^ 2)
      refine h.congr_deriv ?_
      push_cast
      ring
    have hd : HasDerivAt (fun s : ℝ => 1 - lam * s) (-lam) t := by
      simpa using (hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).const_mul lam)
    have h := hnum.div hd (ne_of_gt hden)
    refine h.congr_deriv ?_
    field_simp
    ring
  have hMmono : ∀ t ∈ Set.Icc (0:ℝ) 1, |E t| ≤ M t := by
    have hgap : ∀ t ∈ Set.Icc (0:ℝ) 1,
        |⟪H (x + t • Δ) Δ, Δ'⟫ - ⟪H x Δ, Δ'⟫| ≤ (1 / (1 - lam * t) ^ 2 - 1) * lam * K :=
      hD
    have hE0 : E 0 = 0 := by
      show (⟪g (x + (0:ℝ) • Δ), Δ'⟫ - ⟪g x, Δ'⟫ - (0:ℝ) * ⟪H x Δ, Δ'⟫ : ℝ) = 0
      rw [show x + (0:ℝ) • Δ = x by simp]
      ring
    have hM0 : M 0 = 0 := by
      show (K * lam ^ 2 * (0:ℝ) ^ 2 / (1 - lam * 0) : ℝ) = 0
      norm_num
    have hmono1 : MonotoneOn (fun t => M t - E t) (Set.Icc (0:ℝ) 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
      · intro t ht
        exact (((hMd t ht).sub (hEd t ht)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hMd t (Set.mem_Icc_of_Ioo ht)).sub
          (hEd t (Set.mem_Icc_of_Ioo ht))).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ioo ht
        have hd : HasDerivAt (fun s : ℝ => M s - E s)
            ((1 / (1 - lam * t) ^ 2 - 1) * lam * K
              - (⟪H (x + t • Δ) Δ, Δ'⟫ - ⟪H x Δ, Δ'⟫)) t := (hMd t htI).sub (hEd t htI)
        rw [hd.deriv]
        have h := abs_le.mp (hgap t htI)
        linarith [h.2]
    have hmono2 : MonotoneOn (fun t => M t + E t) (Set.Icc (0:ℝ) 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
      · intro t ht
        exact (((hMd t ht).add (hEd t ht)).continuousAt).continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (((hMd t (Set.mem_Icc_of_Ioo ht)).add
          (hEd t (Set.mem_Icc_of_Ioo ht))).differentiableAt).differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have htI : t ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ioo ht
        have hd : HasDerivAt (fun s : ℝ => M s + E s)
            ((1 / (1 - lam * t) ^ 2 - 1) * lam * K
              + (⟪H (x + t • Δ) Δ, Δ'⟫ - ⟪H x Δ, Δ'⟫)) t := (hMd t htI).add (hEd t htI)
        rw [hd.deriv]
        have h := abs_le.mp (hgap t htI)
        linarith [h.1]
    intro t ht
    have h1 : M 0 - E 0 ≤ M t - E t :=
      hmono1 (Set.left_mem_Icc.mpr (by norm_num)) ht ht.1
    have h2 : M 0 + E 0 ≤ M t + E t :=
      hmono2 (Set.left_mem_Icc.mpr (by norm_num)) ht ht.1
    rw [abs_le]
    constructor <;> linarith [h1, h2, hM0, hE0]
  -- ## Step 5: put everything together
  have hE1 : E 1 = ⟪g (x + Δ), Δ'⟫ := by
    show (⟪g (x + (1:ℝ) • Δ), Δ'⟫ - ⟪g x, Δ'⟫ - (1:ℝ) * ⟪H x Δ, Δ'⟫ : ℝ) = ⟪g (x + Δ), Δ'⟫
    rw [one_smul, hΔ]
    simp
  have hM1 : M 1 = K * lam ^ 2 / (1 - lam) := by
    show (K * lam ^ 2 * (1:ℝ) ^ 2 / (1 - lam * 1) : ℝ) = K * lam ^ 2 / (1 - lam)
    norm_num
  have hgrad : |⟪g (x + Δ), Δ'⟫| ≤ K * lam ^ 2 / (1 - lam) := by
    have h := hMmono 1 (Set.right_mem_Icc.mpr (by norm_num))
    rwa [hE1, hM1] at h
  have hKb : (1 - lam) * K ≤ lam' := by
    have hHcomp : (1 - lam) ^ 2 * ⟪H x Δ', Δ'⟫ ≤ ⟪H (x + Δ) Δ', Δ'⟫ := by
      have h := SCUp.log_comparison S hIcc1
        (fun s => ⟪H (x + s • Δ) Δ', Δ'⟫) (fun s => ⟪DHf (x + s • Δ) Δ Δ', Δ'⟫)
        (fun s hs => DHAux.hess_line_deriv Ω H DHf hDH x Δ Δ' Δ' s hs)
        (fun s hs => hHpd _ hs Δ' hΔ'0)
        lam hlam0 hlt (fun s hs => hgenbnd s hs Δ')
      simp only [zero_smul, add_zero, one_smul] at h
      exact h.1
    have h1 : ((1 - lam) * K) ^ 2 ≤ lam' ^ 2 := by
      rw [mul_pow, hKsq, hlam'sq]
      exact hHcomp
    have h2 : 0 ≤ (1 - lam) * K := mul_nonneg h1l.le hKnn
    nlinarith only [h1, h2, hlam'0]
  -- final contraction
  have hstep : lam' ^ 2 * (1 - lam) ≤ K * lam ^ 2 := by
    have hneg : (⟪g (x + Δ), -Δ'⟫ : ℝ) = -⟪g (x + Δ), Δ'⟫ := by simp
    have h1 : lam' ^ 2 ≤ K * lam ^ 2 / (1 - lam) := by
      rw [hlam', hneg]
      linarith [(abs_le.mp hgrad).1]
    rwa [le_div_iff₀ h1l] at h1
  have hfin : lam' ^ 2 * (1 - lam) ^ 2 ≤ lam ^ 2 * lam' := by
    have h2 : lam' ^ 2 * (1 - lam) * (1 - lam) ≤ K * lam ^ 2 * (1 - lam) :=
      mul_le_mul_of_nonneg_right hstep h1l.le
    have h3 : K * (1 - lam) * lam ^ 2 ≤ lam' * lam ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hKb]) (sq_nonneg lam)
    nlinarith only [h2, h3]
  rw [div_pow, le_div_iff₀ (pow_pos h1l 2)]
  nlinarith only [hfin, hlam'pos]

end NCAux


open NCAux in
/-- **B&V (9.55).**  For a self-concordant `f` with Newton decrement `λ(x) < 1`, the
undamped Newton step keeps `x + Δ` inside the domain and the decrement at the new
point satisfies `λ(x⁺) ≤ (λ(x)/(1 - λ(x)))²`. -/
theorem solution {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (hclosed : ∀ c : ℝ, IsClosed {y | y ∈ Ω ∧ f y ≤ c})
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (Δ : EuclideanSpace ℝ (Fin n)) (hΔ : H x Δ = -g x)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam ^ 2 = ⟪g x, -Δ⟫) (hlt : lam < 1) :
    x + Δ ∈ Ω ∧
    ∀ (Δ' : EuclideanSpace ℝ (Fin n)) (lam' : ℝ),
      H (x + Δ) Δ' = -g (x + Δ) → 0 ≤ lam' → lam' ^ 2 = ⟪g (x + Δ), -Δ'⟫ →
      lam' ≤ (lam / (1 - lam)) ^ 2 :=
  newton_contraction Ω hΩo hΩc f hsc g hg H hH hHpd hclosed x hx Δ hΔ lam hlam0 hlam hlt
