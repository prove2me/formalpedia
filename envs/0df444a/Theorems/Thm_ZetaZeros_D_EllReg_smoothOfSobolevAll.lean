-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_smoothOfSobolevAll
-- name    : ZetaZeros.D.EllReg.smoothOfSobolevAll
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:16:28.144288+00:00
-- url     : https://prove2.me/theorems/519f189e-e630-5afd-92fa-768b57700eff
-- title:
--   Ell Reg: smooth Of Sobolev All
-- statement:
--   The Ell Reg construction uses the smooth Of Sobolev All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Moments.lean#L62-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Moments.lean#L62-L82

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Moments
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

theorem ZetaZeros.D.EllReg.smoothOfSobolevAll : MomentsSmooth := by sorry
