-- Prove2me | Theorems.Thm_mme_CW_value_ge_at_q6
-- name    : mme_CW_value_ge_at_q6
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-05-31T19:18:33.616034+00:00
-- url     : https://prove2.me/theorems/080894d4-9058-4ae4-93c5-430373630a34
-- statement:
--   **The CW laser-method value bound at $q = 6$.**
--
--   For any grading $G$ on $\mathrm{CWObj}\,K\,6$ that aligns with the canonical CW support pattern, the laser-method value formula at this grading and support pattern is at least $\tfrac{5}{2}$:
--
--   $$\forall\, G,\;\;\mathrm{LaserAlignedSupport}\,G\,\mathrm{CWSupportPattern} \implies \frac{5}{2} \leq \mathrm{laserValueFormula}\,G\,\mathrm{CWSupportPattern}.$$
--
--   **Status.** Open. The numeric heart of the CW laser analysis at the optimal parameter $q = 6$. Splits in deeper layers into:
--
--   1. **Canonicalisation.** Any $G$ satisfying `LaserAlignedSupport` for `CWSupportPattern` on `CWObj K 6` must have grading-class dimensions $(1, 6, 1)$ per mode (forced by the type-triple structure of CW's rank-one support).
--
--   2. **Closed-form evaluation of `laserValueFormula`.** Substitute the dimension data $(1, 6, 1)$ into the Stirling-style supremum formula and verify $\tfrac{5}{2} \leq \text{closed-form expression at $q = 6$ optimum}$. This is the canonical Coppersmith–Winograd 1990 §7–§8 calculation; the optimization over probability distributions on `CWSupportPattern` admits an explicit closed-form solution.
--
--   3. **Salem–Spencer + 3AP-free indexing.** Already mostly closed via `mme_salem_spencer_eps_form` and `mme_3AP_free_no_collision` — both PROVED on platform.
--
--   **Caveat — placeholder `laserValueFormula`.** This file's statement assumes the full closed-form `laserValueFormula` definition (deferred to Layer 4). With the current Layer-2 placeholder `laserValueFormula G S = 1`, the inequality $5/2 \leq 1$ is false — closing this leaf requires upgrading the placeholder to the actual Stirling-style formula. The structural decomposition above is forward-compatible with that upgrade.
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_support_pattern
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_laser_pattern
open MME
universe u

theorem mme_CW_value_ge_at_q6 {K : Type u} [Field K] (G : (CWObj K 6).TypeGrading 3) (_hAlign : TensorObj.LaserAlignedSupport G CWSupportPattern) : (5 : ℝ) / 2 ≤ laserValueFormula G CWSupportPattern := by sorry
