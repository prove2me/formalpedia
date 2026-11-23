-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_pf_dw_smooth
-- name    : ZetaZeros.D.EllReg.pf_dw_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:06.539107+00:00
-- url     : https://prove2.me/theorems/e7e6cc59-b92a-4c7d-8a96-aa340a30a1ae
-- title:
--   Ell Reg: pf dw smooth
-- statement:
--   The Ell Reg construction uses the pf dw smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L76-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L76-L92

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

theorem ZetaZeros.D.EllReg.pf_dw_smooth (L : List (Fin d)) (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    ContDiff ℝ ∞ (dw L k) ∧ HasCompactSupport (dw L k) := by sorry
