-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_lintegral_weight_fourier_le
-- name    : ZetaZeros.D.EllReg.lintegral_weight_fourier_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:06.649977+00:00
-- url     : https://prove2.me/theorems/542d0db4-165c-40d6-a074-8f02a65d9a38
-- title:
--   Ell Reg: lintegral weight fourier le
-- statement:
--   The Ell Reg construction uses the lintegral weight fourier le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDecay.lean#L77-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDecay.lean#L77-L106

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem ZetaZeros.D.EllReg.lintegral_weight_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (m : ℕ) :
    (∫⁻ w, ENNReal.ofReal ((1 + ‖w‖) ^ m) * ‖𝓕 f w‖ₑ) ≤
      ENNReal.ofReal (2 ^ (m + (Module.finrank ℝ V + 1)) * (1 + 2 ^ (m + (Module.finrank ℝ V + 1))) *
        derivL1Norm f (m + (Module.finrank ℝ V + 1))) *
      ∫⁻ w : V, ENNReal.ofReal ((1 + ‖w‖) ^ (-((Module.finrank ℝ V + 1 : ℕ) : ℝ))) := by sorry
