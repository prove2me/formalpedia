-- Prove2me | Theorems.Thm_hecke_product_rule
-- name    : hecke_product_rule
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:14:51.976697+00:00
-- url     : https://prove2.me/theorems/3f6096ba-ac35-417c-9842-e83f285a3e1e
-- title:
--   hecke product rule: hecke product rule
-- statement:
--   The hecke product rule construction uses the hecke product rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/HeckeProd.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/HeckeProd.lean#L5-L6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HeckeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem hecke_product_rule : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), χ.ProductRule := by sorry
