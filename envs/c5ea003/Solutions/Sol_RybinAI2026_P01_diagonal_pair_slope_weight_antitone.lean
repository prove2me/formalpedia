-- Prove2me | solution 1 for RybinAI2026.P01.diagonal_pair_slope_weight_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T00:24:35.230704+00:00
-- url     : https://prove2.me/submissions/10b10fae-c65a-452b-b2b4-d3139f7d18f0

import Mathlib

theorem solution (G G' : ℝ → ℝ)
    (hGpos : ∀ t, 0 < t → 0 < G t)
    (hGderiv : ∀ t, 0 < t → HasDerivAt G (G' t) t)
    (hslope : ∀ t, 0 < t →
      t * G' t / G t ≤ 1 / (2 * (1 + Real.sqrt t))) :
    AntitoneOn (fun t : ℝ => G t * (1 + (Real.sqrt t)⁻¹)) (Set.Ioi 0) := by
  let H : ℝ → ℝ := fun t => G t * (1 + (Real.sqrt t)⁻¹)
  have hderiv (t : ℝ) (ht : 0 < t) :
      HasDerivAt H
        (G' t * (1 + (Real.sqrt t)⁻¹) +
          G t * (-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2)) t := by
    have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t :=
      Real.hasDerivAt_sqrt (ne_of_gt ht)
    have hi : HasDerivAt (fun x : ℝ => (Real.sqrt x)⁻¹)
        (-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2) t :=
      hs.inv (ne_of_gt (Real.sqrt_pos.2 ht))
    have hw : HasDerivAt (fun x : ℝ => 1 + (Real.sqrt x)⁻¹)
        (-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2) t := by
      exact hi.const_add 1
    simpa [H] using (hGderiv t ht).mul hw
  have hderiv_nonpos (t : ℝ) (ht : 0 < t) :
      G' t * (1 + (Real.sqrt t)⁻¹) +
          G t * (-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2) ≤ 0 := by
    have hg : 0 < G t := hGpos t ht
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hs2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
    have hc : 0 < 2 * (1 + Real.sqrt t) * G t := by positivity
    have hmul := mul_le_mul_of_nonneg_right (hslope t ht) (le_of_lt hc)
    have hleft :
        (t * G' t / G t) * (2 * (1 + Real.sqrt t) * G t) =
          2 * t * (1 + Real.sqrt t) * G' t := by
      field_simp [hg.ne'] <;> ring
    have hright :
        (1 / (2 * (1 + Real.sqrt t))) *
            (2 * (1 + Real.sqrt t) * G t) = G t := by
      field_simp [ne_of_gt (show 0 < 2 * (1 + Real.sqrt t) by positivity)] <;> ring
    have hbound : 2 * t * (1 + Real.sqrt t) * G' t ≤ G t := by
      rw [hleft, hright] at hmul
      exact hmul
    have hscale : 0 < 2 * t * Real.sqrt t := by positivity
    have hproduct :
        (2 * t * Real.sqrt t) *
            (G' t * (1 + (Real.sqrt t)⁻¹) +
              G t * (-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2)) =
          2 * t * (1 + Real.sqrt t) * G' t - G t := by
      field_simp [hs.ne']
      rw [hs2]
      ring
    have hproduct_nonpos :
        (2 * t * Real.sqrt t) *
            (G' t * (1 + (Real.sqrt t)⁻¹) +
              G t * (-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2)) ≤ 0 := by
      rw [hproduct]
      linarith
    by_contra h
    have hpos : 0 <
        G' t * (1 + (Real.sqrt t)⁻¹) +
          G t * (-(1 / (2 * Real.sqrt t)) / (Real.sqrt t) ^ 2) := lt_of_not_ge h
    have := mul_pos hscale hpos
    linarith
  change AntitoneOn H (Set.Ioi 0)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi (0 : ℝ))
  · intro t ht
    exact (hderiv t (Set.mem_Ioi.mp ht)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioi (0 : ℝ) := by simpa only [interior_Ioi] using ht
    exact (hderiv t (Set.mem_Ioi.mp ht')).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioi (0 : ℝ) := by simpa only [interior_Ioi] using ht
    exact hderiv_nonpos t (Set.mem_Ioi.mp ht')
