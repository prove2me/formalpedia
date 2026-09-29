-- Prove2me | solution 1 for MarkoffTransfer.markoff_middle_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:18:19.956974+00:00
-- url     : https://prove2.me/submissions/16f4382f-5932-4aae-b6a6-bae0e5e7afbd

-- Sol generated from Cryptography/MarkoffTransfer/UniquenessAndNonlinearity.lean
import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffFreeBinary
import Definitions.Def_Cryptography_MarkoffTransfer_UniquenessAndNonlinearity
import Theorems.Thm_MarkoffTransfer_isMarkoff_iff

/-!
# Cycle 2: What the Transfer *Does* Buy on the Markoff Side

Cycle 1 showed that the Berggren ternary tree and the Markoff binary tree are not
isomorphic, and located the two obstructions (ternary vs binary branching; silver vs
golden growth).  This file harvests the parts of the Berggren methodology — descent,
unique parents, and the "one coordinate determines the rest" style of argument — that
*do* apply to the Markoff tree, and pins down the exact reason the Berggren *linear*
(Lorentz) machinery cannot be imported.

## Main results

* `markoff_middle_unique` — **the smallest and largest entries determine the middle one.**
  Two ordered Markoff triples with the same outer pair are equal.
* `markoff_unique_of_min_one` — consequently, for a fixed top entry there is at most one
  ordered Markoff triple with smallest entry `1`.
* `markoff_uniqueness_iff_min_determined` — a **reduction of the (open) Markoff uniqueness
  conjecture**: uniqueness of the whole triple given the maximum is equivalent to
  uniqueness of the *minimum* given the maximum.  The middle entry is free of charge.
* `MReach.isCoprime` — every tree triple is pairwise coprime (transfer of the Berggren
  primitivity invariant, proved by induction along the tree).
* `vieta_not_linear` — **the linear obstruction.**  The Berggren moves act on triples by
  integer matrices preserving the Lorentz form `a² + b² - c²`
  (`BerggrenSpectral.berg_isometry_*`).  No matrix whatsoever implements the Markoff Vieta
  move on the Markoff surface: the move is genuinely quadratic.  This is the structural
  reason the Lorentz/hyperbolic half of the Berggren machinery cannot be transported.
-/

open MarkoffTransfer

/-! ## The outer pair determines the middle entry -/



/-! ## Reduction of the Markoff uniqueness conjecture -/




/-! ## Pairwise coprimality along the tree -/



/-! ## The linear obstruction -/




open MarkoffTransfer in
theorem solution{x y y' z : ℤ} (h : IsMarkoff x y z) (h' : IsMarkoff x y' z)
    (hx : 0 < x) (hyz : y ≤ z) (hyz' : y' ≤ z) (hy : 0 < y) : y = y' := by
  rw [isMarkoff_iff] at h h'
  by_contra hne
  -- distinct roots of the same quadratic: their sum is `3xz`
  have hsum : y + y' = 3 * x * z := by
    have hfac : (y - y') * (y + y' - 3 * x * z) = 0 := by nlinarith [h, h']
    rcases mul_eq_zero.mp hfac with h₁ | h₁
    · exact absurd (by linarith : y = y') hne
    · linarith
  -- hence their product is `x² + z²`
  have hprod : y * y' = x ^ 2 + z ^ 2 := by nlinarith [h, hsum]
  nlinarith [hprod, hyz, hyz', hy, hx]
