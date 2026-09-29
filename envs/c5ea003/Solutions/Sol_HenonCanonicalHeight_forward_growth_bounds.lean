-- Prove2me | solution 1 for HenonCanonicalHeight.forward_growth_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:48:34.376132+00:00
-- url     : https://prove2.me/submissions/ecdb6eae-8ab4-4538-abba-ef5cd53e2fb7

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
theorem solution{D : ℕ} {b x y : ℝ}
    (hP : InForwardRegion D b (x, y)) :
    (1 / 3 : ℝ) * |y| ^ D < |x + y ^ D + b| ∧
      |x + y ^ D + b| < (5 / 3 : ℝ) * |y| ^ D := by
  -- Extract the key inequalities from InForwardRegion
  have h1 : 3 * max (max |x| |b|) 1 < |y| ^ D := hP.1
  have h2 : 3 * |y| < |y| ^ D := hP.2
  -- From h1, we get |x| < |y|^D / 3 and |b| < |y|^D / 3
  have h1' : max (max |x| |b|) 1 < |y| ^ D / 3 := by linarith
  have hx : |x| < |y| ^ D / 3 := by
    calc |x| ≤ max |x| |b| := le_max_left _ _
      _ ≤ max (max |x| |b|) 1 := le_max_left _ _
      _ < |y| ^ D / 3 := h1'
  have hb : |b| < |y| ^ D / 3 := by
    calc |b| ≤ max |x| |b| := le_max_right _ _
      _ ≤ max (max |x| |b|) 1 := le_max_left _ _
      _ < |y| ^ D / 3 := h1'
  -- Bound on |x + b|
  have hxb : |x + b| < 2 * |y| ^ D / 3 := by
    calc |x + b| ≤ |x| + |b| := abs_add_le x b
      _ < |y| ^ D / 3 + |y| ^ D / 3 := by linarith
      _ = 2 * |y| ^ D / 3 := by ring
  -- Note: |y^D| = |y|^D
  have hyD : |y ^ D| = |y| ^ D := abs_pow y D
  -- Rewrite as y^D + (x + b)
  have rew : x + y ^ D + b = y ^ D + (x + b) := by ring
  constructor
  · -- Lower bound: |y^D + (x+b)| ≥ |y^D| - |x+b|
    have h := abs_sub_abs_le_abs_add (y ^ D) (x + b)
    calc 1 / 3 * |y| ^ D = |y| ^ D - 2 * |y| ^ D / 3 := by ring
      _ < |y ^ D| - |x + b| := by rw [hyD]; linarith
      _ ≤ |y ^ D + (x + b)| := h
      _ = |x + y ^ D + b| := by rw [← rew]
  · -- Upper bound: |y^D + (x+b)| ≤ |y^D| + |x+b|
    calc |x + y ^ D + b| = |y ^ D + (x + b)| := by rw [rew]
      _ ≤ |y ^ D| + |x + b| := abs_add_le _ _
      _ = |y| ^ D + |x + b| := by rw [hyD]
      _ < |y| ^ D + 2 * |y| ^ D / 3 := by linarith
      _ = 5 / 3 * |y| ^ D := by ring
