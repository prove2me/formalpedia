-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_pf_fourier_dw
-- name    : ZetaZeros.D.EllReg.pf_fourier_dw
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:54.966279+00:00
-- url     : https://prove2.me/theorems/ff8815fe-ec29-4303-ace0-7fcf4287e1e1
-- title:
--   Ell Reg: pf fourier dw
-- statement:
--   The Ell Reg construction uses the pf fourier dw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L148-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L148-L159

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

theorem ZetaZeros.D.EllReg.pf_fourier_dw (L : List (Fin d)) (k : E d → ℂ) (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    (ζ : E d) :
    𝓕 (dw L k) ζ = (L.map fun j => 2 * Real.pi * Complex.I * ((ζ j : ℝ) : ℂ)).prod * 𝓕 k ζ := by sorry
