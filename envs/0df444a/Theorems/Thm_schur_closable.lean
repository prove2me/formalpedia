-- Prove2me | Theorems.Thm_schur_closable
-- name    : schur_closable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:17:05.424184+00:00
-- url     : https://prove2.me/theorems/e684e528-6cea-4eda-88cf-86b9f583775a
-- title:
--   schur closable: schur closable
-- statement:
--   The schur closable construction uses the schur closable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/SchurClosable.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/SchurClosable.lean#L5-L6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SchurClosable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurUnitaryInner_UnitaryInner
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SchurClosable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem schur_closable : Formalism.IndefR.Leaf.SchurClosable := by sorry
