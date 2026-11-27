-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_om_zero
-- name    : ZetaZeros.D.EllReg.om_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:39:53.497578+00:00
-- url     : https://prove2.me/theorems/e350e6a2-20a1-41c1-a8d0-39d84a52a0f0
-- title:
--   Ell Reg: om zero
-- statement:
--   The Ell Reg construction uses the om zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/BaseLevel.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/BaseLevel.lean#L11-L12

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

theorem ZetaZeros.D.EllReg.om_zero {d : ℕ} (s : ℝ) (ξ : E d) : om s 0 0 ξ = (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by sorry
