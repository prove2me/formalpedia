-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_pf_eF_smooth
-- name    : ZetaZeros.D.EllReg.pf_eF_smooth
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:25.067742+00:00
-- url     : https://prove2.me/theorems/bd6a275a-e953-5af9-85c4-1854e023c391
-- title:
--   Ell Reg: pf e F smooth
-- statement:
--   The Ell Reg construction uses the pf e F smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L185-L188

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier
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

theorem ZetaZeros.D.EllReg.pf_eF_smooth (ξ : E d) : ContDiff ℝ ∞ (eF ξ) := by sorry
