-- Prove2me | Theorems.Thm_level_product_index
-- name    : level_product_index
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:19:46.018519+00:00
-- url     : https://prove2.me/theorems/11723b90-c9c0-55e3-b324-744f4c1b1305
-- title:
--   level product index: level product index
-- statement:
--   The level product index construction uses the level product index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/LevelProdIdx.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/LevelProdIdx.lean#L8-L10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelProdIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_ZeroMemLatSet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVTmulEqTmulApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVMemTensInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_SingleApply
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LevelProdIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem level_product_index : PI.LevelProdIdx := by sorry
