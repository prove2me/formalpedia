-- Prove2me | Theorems.Thm_mme_released_recursive_global_window_center
-- name    : mme_released_recursive_global_window_center
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T17:15:38.190345+00:00
-- url     : https://prove2.me/theorems/48b7b4d8-5e41-4725-ad0a-d6a2605e3c81
-- title:
--   The physical global windows have the recursive seed centers
-- statement:
--   For every owner, scale, tolerance, physical mode, and candidate word histogram, membership in the existing global frequency window is equivalent to the inequalities
--   $$\left|\frac{\mu(c,w)}{B(k)}-\frac{\alpha_{o,c}}D P_{t(o,c)}(i,w)\right|\leq\varepsilon.$$
--   Here $i$ is in physical coordinates and $P_t$ is the explicit primitive recursive parent mixture. The equivalence applies to every histogram, so it can be used for every admissible reference arrangement in the existing physical joint interface. It changes neither the tolerance nor the scale.
-- source:
--   Exact-seed profile bridge for the six-region global interface in More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2. Uses the already published primitive rational seed and literal supported joint counts; the recursive numerical continuation remains a separate obligation.

import Definitions.Def_mme_released_global_joint_interface
import Definitions.Def_mme_released_recursive_profile_mixture
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false
open MME.RecursiveYZ

theorem mme_released_recursive_global_window_center (o : Fin 6) (k : ℕ) (eps : ℝ) (i : Fin 3)
    (mu : Cell 8 1 (fun _ _ ↦ 8) → Word → ℕ) :
    windowGood o k eps (hashMode o i) mu ↔
      ∀ c w, |(mu c w : ℝ) / (blocks k : ℝ) -
        ((alpha o (shapeEquiv.symm c.2) : ℝ) / D) *
          parentProfile (term o (shapeEquiv.symm c.2)) i w| ≤ eps := by sorry
