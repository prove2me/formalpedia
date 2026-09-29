-- Prove2me | Theorems.Thm_mme_released_116_integer_parent_mixture
-- name    : mme_released_116_integer_parent_mixture
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:08:07.91103+00:00
-- url     : https://prove2.me/theorems/a1dd1611-907d-4386-9fbc-d261ba2259c6
-- title:
--   The (1,1,6) integer parent mixture equals the regional seed mixture
-- statement:
--   For the released owner-zero $(1,1,6)$ profiles, let $a_{r,c}$ be the split weights and $u_{r,c,i}$ the child marginal counts, all at denominator $d=10^{12}$. The parent mixture computed from the integer sizes, split counts and child profiles obeys $$\operatorname{parentMixture}_{r,i}(w_0,w_1)=\sum_c\frac{a_{r,c}}d\frac{u_{r,c,i}(w_0)}d\frac{u_{r,\bar c,i}(w_1)}d.$$ This identifies the concrete integer-step center with each region’s own seed mixture. It does not assert a physical coordinate partition or an extraction-rate bound.
-- source:
--   Released owner-zero term010 and the integer regional CW extraction interface.

import Definitions.Def_mme_released_116_integer_profiles
open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

theorem mme_released_116_integer_parent_mixture
    (i : Fin 3) (r : Fin 6) (w : Fin 2 → CompleteWord 2) :
    RegionRealization.parentMixture parent_total regionalSize splitCount
      (integerProfile i) r w =
      ∑ c : Split, ((splitWeight r c : ℝ) / denominator) *
        ((childMarginal r c i (w 0) : ℝ) / denominator) *
        ((childMarginal r (complement (parent_total r) c) i (w 1) : ℝ) /
          denominator) := by sorry
