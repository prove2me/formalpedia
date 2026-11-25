-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_weightedNormFinite
-- name    : ZetaZeros.D.EllReg.weightedNormFinite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:15:05.019984+00:00
-- url     : https://prove2.me/theorems/4e3168cb-bf08-4713-aa79-59a6ffdceb4f
-- title:
--   Ell Reg: weighted Norm Finite
-- statement:
--   The Ell Reg construction uses the weighted Norm Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L125-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L125-L152

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

theorem ZetaZeros.D.EllReg.weightedNormFinite : FiniteWeighted := by sorry
