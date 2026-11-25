-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_weightedNormLimit
-- name    : ZetaZeros.D.EllReg.weightedNormLimit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:15:27.681514+00:00
-- url     : https://prove2.me/theorems/08e90556-410c-45b6-a3d5-258ab9860d5c
-- title:
--   Ell Reg: weighted Norm Limit
-- statement:
--   The Ell Reg construction uses the weighted Norm Limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L31-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L31-L69

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_BaseLevel
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightedNormFinite
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

theorem ZetaZeros.D.EllReg.weightedNormLimit : EpsLimit := by sorry
