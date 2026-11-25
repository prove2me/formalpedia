-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_stepOfParts_of
-- name    : ZetaZeros.D.EllReg.stepOfParts_of
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:16:39.915802+00:00
-- url     : https://prove2.me/theorems/d7df74d2-a1b6-45ee-b9dc-5400376fde7a
-- title:
--   Ell Reg: step Of Parts of
-- statement:
--   The Ell Reg construction uses the step Of Parts of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllRegStep.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllRegStep.lean#L44-L46

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
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
noncomputable section

theorem ZetaZeros.D.EllReg.stepOfParts_of (hD : DecomposeOf) (hF : FiniteWeighted) (hE : EpsLimit) (hS : StepCore) :
    StepOfParts := by sorry
