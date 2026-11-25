-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_moments_integrable_of_nrm
-- name    : ZetaZeros.D.EllReg.moments_integrable_of_nrm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:49.389804+00:00
-- url     : https://prove2.me/theorems/a729c786-44d4-425d-a861-0c88e4b9b73e
-- title:
--   Ell Reg: moments integrable of nrm
-- statement:
--   The Ell Reg construction uses the moments integrable of nrm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Moments.lean#L8-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Moments.lean#L8-L60

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

theorem ZetaZeros.D.EllReg.moments_integrable_of_nrm {d : ℕ} (F : E d → ℂ) (hF : Continuous F)
    (h : ∀ s : ℕ, nrm (s : ℝ) 0 0 F < ⊤) (n : ℕ) :
    Integrable (fun v : E d => ‖v‖ ^ n * ‖F v‖) := by sorry
