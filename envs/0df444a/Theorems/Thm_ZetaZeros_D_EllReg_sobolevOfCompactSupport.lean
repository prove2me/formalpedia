-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_sobolevOfCompactSupport
-- name    : ZetaZeros.D.EllReg.sobolevOfCompactSupport
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:16:36.265106+00:00
-- url     : https://prove2.me/theorems/4eefe6d7-e826-4710-bc3d-bc8ce03f43d1
-- title:
--   Ell Reg: sobolev Of Compact Support
-- statement:
--   The Ell Reg construction uses the sobolev Of Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/BaseLevel.lean#L14-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/BaseLevel.lean#L14-L48

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_BaseLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

theorem ZetaZeros.D.EllReg.sobolevOfCompactSupport : BaseLevel := by sorry
