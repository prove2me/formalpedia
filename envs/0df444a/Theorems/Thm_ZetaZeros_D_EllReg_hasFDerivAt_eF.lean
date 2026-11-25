-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_hasFDerivAt_eF
-- name    : ZetaZeros.D.EllReg.hasFDerivAt_eF
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:16.755015+00:00
-- url     : https://prove2.me/theorems/314b07e3-95ec-410c-9d75-2f18cdf8b46d
-- title:
--   Ell Reg: has FDeriv At e F
-- statement:
--   The Ell Reg construction uses the has FDeriv At e F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/IteratedPartialFourierChar.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/IteratedPartialFourierChar.lean#L17-L20

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_IteratedPartialFourierChar
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

theorem ZetaZeros.D.EllReg.hasFDerivAt_eF {d : ℕ} (ξ y : E d) :
    HasFDerivAt (eF ξ) (Complex.exp (eL ξ y) • eL ξ) y := by sorry
