-- Prove2me | Theorems.Thm_mme_116_split_marginals_injective
-- name    : mme_116_split_marginals_injective
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T23:48:44.855148+00:00
-- url     : https://prove2.me/theorems/a0d2d40f-f7d1-4070-b13e-7ee5fe261a0c
-- title:
--   Coordinate marginals uniquely determine the 116 split weights
-- statement:
--   For arbitrary real weights on the admissible half-four splits of parent grade (1,1,6), equality of all three coordinate marginals implies equality of the weights. The four splits are 004, 013, 103, and 112.
-- source:
--   Exact simplification of the entropy penalty for the released 116 integer profiles. The four split weights are recovered from their coordinate marginals.

import Theorems.Thm_mme_released_116_regional_split_mass
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open BigOperators MME MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_116_split_marginals_injective (alpha rho : Split 4 ![1, 1, 6] → ℝ)
    (h : ∀ (i : Fin 3) (j : Fin 5),
      mme_modern_marginal (fun c : Split 4 ![1, 1, 6] => c.val i) rho j =
        mme_modern_marginal (fun c : Split 4 ![1, 1, 6] => c.val i) alpha j) :
    rho = alpha := by sorry
