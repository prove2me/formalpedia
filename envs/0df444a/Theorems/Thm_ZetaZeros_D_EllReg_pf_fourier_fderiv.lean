-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_pf_fourier_fderiv
-- name    : ZetaZeros.D.EllReg.pf_fourier_fderiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:42.978551+00:00
-- url     : https://prove2.me/theorems/567de3e6-55fb-447f-851e-b1af11bc7584
-- title:
--   Ell Reg: pf fourier fderiv
-- statement:
--   The Ell Reg construction uses the pf fourier fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L110-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L110-L146

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
set_option maxHeartbeats 800000

theorem ZetaZeros.D.EllReg.pf_fourier_fderiv (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) (v ζ : E d) :
    𝓕 (fun x => fderiv ℝ k x v) ζ = (2 * Real.pi * Complex.I * ((inner ℝ ζ v : ℝ) : ℂ)) * 𝓕 k ζ := by sorry
