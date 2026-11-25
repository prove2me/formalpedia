-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_internal_of_all
-- name    : ZetaZeros.D.EllReg.internal_of_all
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:39.113853+00:00
-- url     : https://prove2.me/theorems/816f2b33-2cd3-401e-9a4f-479c6706aa2c
-- title:
--   Ell Reg: internal of all
-- statement:
--   The Ell Reg construction uses the internal of all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllRegCut.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllRegCut.lean#L147-L151

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllReg
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
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
variable {d : ℕ}

theorem ZetaZeros.D.EllReg.internal_of_all (hM : MomentsSmooth) (hBu : Bump) (hC : CutCont) (hL : LocalGlobal)
    (hB : BaseLevel) (hSL : SymbLower) (hW : WeightDiff) (hCB : ConvBound) (hK : KernelSmall)
    (hPF : PairingFourier) (hDE : DwExp) (hFP : FourierPair) (hPL : PairingLocal) (hWF : WeakFourier)
    (hSP : StepOfParts) : Internal := by sorry
