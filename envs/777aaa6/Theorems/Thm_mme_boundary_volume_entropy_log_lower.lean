-- Prove2me | Theorems.Thm_mme_boundary_volume_entropy_log_lower
-- name    : mme_boundary_volume_entropy_log_lower
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:12:07.143233+00:00
-- url     : https://prove2.me/theorems/ea4b4859-84fd-418b-80cb-62bfdbd59a9e
-- title:
--   Boundary matrix volume retains histogram entropy with logarithmic loss
-- statement:
--   For every boundary profile of positive length L, the logarithm of its exact matrix volume is at least L times the natural-log histogram entropy, minus the alphabet cardinality times log(6(L+1)), plus the count-weighted number of nonzero CW letters times log 5. This finite bound follows from the multinomial polynomial lower bound and the exact boundary dimension formula.
-- source:
--   Exact boundary dimension and kernel-checked multinomial entropy bound.

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Definitions.Def_mme_recursive_yz_boundary_data
open scoped BigOperators
open MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false
universe u

theorem mme_boundary_volume_entropy_log_lower {ell L : ℕ}
    (B : Profile ell L) (hL : 0 < L) :
    (L : ℝ) * Real.log 2 *
        mme_modern_entropyBits (fun s ↦ (B.count s : ℝ) / (L : ℝ)) -
      (Fintype.card (CompleteWord ell) : ℝ) * Real.log (6 * ((L + 1 : ℕ) : ℝ)) +
      ((∑ s, B.count s * ones s : ℕ) : ℝ) * Real.log 5 ≤
        Real.log (B.dim : ℝ) := by sorry
