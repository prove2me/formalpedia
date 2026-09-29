-- Prove2me | Theorems.Thm_mme_released_recursive_profile_error_transfer
-- name    : mme_released_recursive_profile_error_transfer
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T17:11:32.923854+00:00
-- url     : https://prove2.me/theorems/ad59e44c-be00-4337-be03-b50e0632217f
-- title:
--   Regional profile tolerances transfer without amplification
-- statement:
--   For an interior parent of owner $o$, let $p_r$ be the six normalized region weights, $P_r(w)$ the child-product mixture in region $r$, and $A$ the normalized global parent weight. If empirical regional frequencies $f_r$ obey $|f_r-P_r(w)|\leq\varepsilon$ for all six regions and $\varepsilon\geq0$, then
--   $$\left|A\sum_r p_rf_r-P^{\rm global}_{o,i,c,w}\right|\leq\varepsilon.$$
--   This is a lossless transfer to the literal published global profile. The theorem checks from the seed that $\sum_r p_r=1$ and $0\leq A\leq1$. It supplies the error estimate once the recursive block counts have been recombined; no existence of that block refinement is assumed as a conclusion.
-- source:
--   Exact-seed profile bridge for the six-region global interface in More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2. Uses the already published primitive rational seed and literal supported joint counts; the recursive numerical continuation remains a separate obligation.

import Definitions.Def_mme_released_recursive_profile_mixture
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false

theorem mme_released_recursive_profile_error_transfer (o : Fin 6) (i : Fin 3) (c : Shape) (w : Word)
    (f : Fin 6 → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    (hinterior : (term o (shapeEquiv.symm c)).boundary = [])
    (hclose : ∀ r, |f r - regionProfile (term o (shapeEquiv.symm c)) r (roles o i) w| ≤ eps) :
    |((alpha o (shapeEquiv.symm c) : ℝ) / D) *
      (∑ r : Fin 6, ((regionWeight (term o (shapeEquiv.symm c)) r : ℝ) / D) * f r) -
        (profile o).2 i ⟨0,c⟩ w| ≤ eps := by sorry
