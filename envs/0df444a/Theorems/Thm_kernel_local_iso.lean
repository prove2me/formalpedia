-- Prove2me | Theorems.Thm_kernel_local_iso
-- name    : kernel_local_iso
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:08:42.965646+00:00
-- url     : https://prove2.me/theorems/67ed5b9b-8352-4564-8de9-7a4e2c71d7a6
-- title:
--   kernel local iso: kernel local iso
-- statement:
--   The kernel local iso construction uses the kernel local iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KerLocIso.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KerLocIso.lean#L6-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_KerLocIsoOfNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOne
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerLocIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem kernel_local_iso : PI.KerIso.LocIso := by sorry
