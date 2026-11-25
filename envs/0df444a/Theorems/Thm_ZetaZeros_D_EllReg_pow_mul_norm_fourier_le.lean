-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_pow_mul_norm_fourier_le
-- name    : ZetaZeros.D.EllReg.pow_mul_norm_fourier_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:29.757562+00:00
-- url     : https://prove2.me/theorems/fb730531-4057-5e14-b9e4-3ae9113c7989
-- title:
--   Ell Reg: pow mul norm fourier le
-- statement:
--   The Ell Reg construction uses the pow mul norm fourier le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDecay.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDecay.lean#L28-L36

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

theorem ZetaZeros.D.EllReg.pow_mul_norm_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (n : ℕ) (w : V) :
    ‖w‖ ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * derivL1Norm f n := by sorry
