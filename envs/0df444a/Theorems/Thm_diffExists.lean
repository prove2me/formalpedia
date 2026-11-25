-- Prove2me | Theorems.Thm_diffExists
-- name    : diffExists
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:07.115622+00:00
-- url     : https://prove2.me/theorems/ad36805c-9d6d-4a01-b055-a3adc82de6eb
-- title:
--   diff Exists: diff Exists
-- statement:
--   The diff Exists construction uses the diff Exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/DiffGenLoc.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/DiffGenLoc.lean#L5-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiffGenLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDifferentGenerators_DiffExistsMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DiffGenLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem diffExists {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : PI.DiffGenLoc.DiffExists v := by sorry
