-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_one_add_pow_mul_norm_fourier_le
-- name    : ZetaZeros.D.EllReg.one_add_pow_mul_norm_fourier_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:47.649141+00:00
-- url     : https://prove2.me/theorems/fc3f5b30-adda-4b34-9a6b-ca464f663571
-- title:
--   Ell Reg: one add pow mul norm fourier le
-- statement:
--   The Ell Reg construction uses the one add pow mul norm fourier le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDecay.lean#L50-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDecay.lean#L50-L67

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

theorem ZetaZeros.D.EllReg.one_add_pow_mul_norm_fourier_le {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (n : ℕ) (w : V) :
    (1 + ‖w‖) ^ n * ‖𝓕 f w‖ ≤ 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n := by sorry
