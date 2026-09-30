-- Prove2me | Theorems.Thm_Hirsch_normalized_two_moment_slice_diameter_two
-- name    : Hirsch.normalized_two_moment_slice_diameter_two
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T13:57:22.68883+00:00
-- url     : https://prove2.me/theorems/e93edd7b-4659-4df5-9eab-fbcce4352c78
-- title:
--   Normalized two-moment slices have graph diameter at most two
-- statement:
--   For arbitrary real moments t_i and target mu, consider the normalized nonnegative slice of the simplex defined by sum_i s_i = 1 and sum_i t_i s_i = mu. Its vertex-edge graph has padded diameter at most two. No distinctness or genericity assumption is made on the moments, so repeated moments, empty slices, singleton slices, and lower-dimensional cases are included.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/e9b89ee3f02fbaed5c379e35ef1c824ab3b85186 ; standalone Lean/Axiom gate Actions run 34605987684

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem normalized_two_moment_slice_diameter_two {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) :
    DiamLE
      {s : EuclideanSpace ℝ (Fin n) |
        (∀ i, 0 ≤ s i) ∧
        (∑ i, s i) = 1 ∧
        (∑ i, t i * s i) = mu} 2 := by sorry
end Hirsch
