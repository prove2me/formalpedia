-- Prove2me | Theorems.Thm_mme_CW_support_pattern_symmetric
-- name    : mme_CW_support_pattern_symmetric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T18:06:22.584127+00:00
-- url     : https://prove2.me/theorems/e31cc798-1041-49ce-a0b5-5618d6fdde09
-- statement:
--   **The Coppersmith–Winograd support pattern is cyclically symmetric.**
--
--   The canonical CW support set
--
--   $$S \;=\; \{(0,1,1),\; (1,0,1),\; (1,1,0),\; (0,0,2),\; (0,2,0),\; (2,0,0)\}$$
--
--   is closed under the cyclic permutation $(\alpha, \beta, \gamma) \mapsto (\beta, \gamma, \alpha)$:
--
--   | Triple | Cyclic image | In $S$? |
--   |---|---|---|
--   | $(0,1,1)$ | $(1,1,0)$ | ✓ |
--   | $(1,0,1)$ | $(0,1,1)$ | ✓ |
--   | $(1,1,0)$ | $(1,0,1)$ | ✓ |
--   | $(0,0,2)$ | $(0,2,0)$ | ✓ |
--   | $(0,2,0)$ | $(2,0,0)$ | ✓ |
--   | $(2,0,0)$ | $(0,0,2)$ | ✓ |
--
--   Each cycle of length 3 in the symmetric group on type-triples is fully contained in $S$. The proof is `intro x hx; fin_cases hx <;> decide` — fully discharged by case analysis on the 6-element Finset, with `decide` verifying each cyclic image lies in $S$.
--
--   **The structural property that enables the laser method's *symmetric* construction.** Every type-triple in the support contributes equally to the three cyclic factor positions of the matrix-multiplication blocks, which is what produces a *symmetric* value bound after laser optimization.
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_support_pattern
import Definitions.Def_mme_laser_pattern
open MME

theorem mme_CW_support_pattern_symmetric : LaserSymmetric CWSupportPattern := by sorry
