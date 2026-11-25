-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_pf_fourier_integrable
-- name    : ZetaZeros.D.EllReg.pf_fourier_integrable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:41.011132+00:00
-- url     : https://prove2.me/theorems/dd2593d1-e0f9-5bc4-8ec5-315e3f071739
-- title:
--   Ell Reg: pf fourier integrable
-- statement:
--   The Ell Reg construction uses the pf fourier integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L170-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L170-L183

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

theorem ZetaZeros.D.EllReg.pf_fourier_integrable (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) :
    Integrable (𝓕 k) := by sorry
