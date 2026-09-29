-- Prove2me | solution 1 for HenonCanonicalHeight.normalized_height_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:13.537923+00:00
-- url     : https://prove2.me/submissions/ab46f153-3da9-4972-9ad5-3934720f67f3

-- Sol generated from Bridges/HenonCanonicalHeight.lean
import Mathlib
import Definitions.Def_Bridges_HenonCanonicalHeight

/-!
# Escape regions and normalized heights for a Hénon map

This file formalizes algebraic and analytic ingredients used in the study of the map
`φ(x,y) = (y, x + y^D + b)`.  The escape region below is a slightly strengthened,
robust version of the usual archimedean escape region: the additional condition
`3 |y| < |y|^D` makes forward invariance transparent even in the presence of
cancellation.  No global arithmetic-height machinery is assumed.
-/

open HenonCanonicalHeight













open HenonCanonicalHeight in
theorem solution    {D : ℕ} (hD : 2 ≤ D) (h : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hscale : ∀ n, |h (n + 1) - (D : ℝ) * h n| ≤ C) :
    ∀ n, |h n / (D : ℝ) ^ n - h 0| ≤ C / ((D : ℝ) - 1) := by
  -- Stronger bound: |h n / D^n - h 0| ≤ C * (1 - 1/D^n) / (D - 1)
  have key : ∀ n, |h n / (D : ℝ) ^ n - h 0| ≤ C * (1 - 1 / (D : ℝ) ^ n) / ((D : ℝ) - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hD_pos : (0 : ℝ) < D := by linarith [show (2 : ℝ) ≤ D by exact_mod_cast hD]
      have hDn_pos : (0 : ℝ) < D ^ n := pow_pos hD_pos n
      have hDn1_pos : (0 : ℝ) < D ^ (n + 1) := pow_pos hD_pos (n + 1)
      have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos
      have hDn_ne : (D : ℝ) ^ n ≠ 0 := ne_of_gt hDn_pos
      have hDn1_ne : (D : ℝ) ^ (n + 1) ≠ 0 := ne_of_gt hDn1_pos
      -- Key decomposition
      have decompose : h (n + 1) / (D : ℝ) ^ (n + 1) - h 0 =
          (h (n + 1) - D * h n) / (D : ℝ) ^ (n + 1) + (h n / (D : ℝ) ^ n - h 0) := by
        field_simp
        ring
      rw [decompose]
      -- Triangle inequality
      have tri := abs_add_le ((h (n + 1) - D * h n) / (D : ℝ) ^ (n + 1)) (h n / (D : ℝ) ^ n - h 0)
      -- Bound on first term
      have bound1 : |((h (n + 1) - D * h n) / (D : ℝ) ^ (n + 1))| ≤ C / (D : ℝ) ^ (n + 1) := by
        rw [abs_div]
        gcongr
        · exact hscale n
        · rw [abs_of_pos hDn1_pos]
      -- Now combine using a calculation
      calc |((h (n + 1) - D * h n) / (D : ℝ) ^ (n + 1)) + (h n / (D : ℝ) ^ n - h 0)|
          ≤ |((h (n + 1) - D * h n) / (D : ℝ) ^ (n + 1))| + |h n / (D : ℝ) ^ n - h 0| := tri
        _ ≤ C / (D : ℝ) ^ (n + 1) + C * (1 - 1 / (D : ℝ) ^ n) / ((D : ℝ) - 1) := by linarith
        _ = C * (1 - 1 / (D : ℝ) ^ (n + 1)) / ((D : ℝ) - 1) := by
            have hD_sub_ne : (D : ℝ) - 1 ≠ 0 := by linarith [show (2 : ℝ) ≤ D by exact_mod_cast hD]
            field_simp
            ring_nf
  intro n
  have := key n
  refine this.trans ?_
  have hD_pos : (0 : ℝ) < D := by linarith [show (2 : ℝ) ≤ D by exact_mod_cast hD]
  have hDn_pos : (0 : ℝ) < D ^ n := pow_pos hD_pos n
  have h_le_one : 1 - 1 / (D : ℝ) ^ n ≤ 1 := sub_le_self _ (by positivity)
  have hD_sub_pos : (0 : ℝ) ≤ D - 1 := by linarith [show (2 : ℝ) ≤ D by exact_mod_cast hD]
  gcongr
  · nlinarith
