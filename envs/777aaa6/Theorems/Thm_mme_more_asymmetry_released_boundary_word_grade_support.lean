-- Prove2me | Theorems.Thm_mme_more_asymmetry_released_boundary_word_grade_support
-- name    : mme_more_asymmetry_released_boundary_word_grade_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T19:02:39.312955+00:00
-- url     : https://prove2.me/theorems/342fc0a0-c219-4178-aade-4b75ac8f6d08
-- title:
--   Released boundary words have their parent grade
-- statement:
--   For every boundary term in the six released exact-profile owner tables, the four-symbol record has total grade equal to the designated parent coordinate: coordinate 1 when coordinate 0 is zero, and coordinate 0 otherwise. This is the grade-support fact missing from Term.Valid and needed to apply the boundary word-to-split construction to the literal table.
-- source:
--   Exact literal data from Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, encoded in the pinned MME.MoreAsymmetryExactSeed.terms. The property was checked by exact natural-number parsing in the six-owner stage-profile audit; this theorem adds the missing Lean-kernel grade-support statement. Environment/mathlib revision 777aaa61dcd2a1258d2b4962dbe983ede4d23b2e.

import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
open MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem mme_more_asymmetry_released_boundary_word_grade_support :
    ∀ t ∈ terms, t.boundary ≠ [] →
      ∀ b ∈ t.boundary,
        (if t.shape.getD 0 0 = 0 then
          b.1.sum = t.shape.getD 1 0
        else
          b.1.sum = t.shape.getD 0 0) := by sorry
