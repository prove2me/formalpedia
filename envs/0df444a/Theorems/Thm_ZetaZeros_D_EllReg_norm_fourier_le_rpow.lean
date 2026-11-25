-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_norm_fourier_le_rpow
-- name    : ZetaZeros.D.EllReg.norm_fourier_le_rpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:47.158834+00:00
-- url     : https://prove2.me/theorems/b3bd92e2-466f-4843-9787-89f26d6fd641
-- title:
--   Ell Reg: norm fourier le rpow
-- statement:
--   The Ell Reg construction uses the norm fourier le rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDecay.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDecay.lean#L69-L75

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

theorem ZetaZeros.D.EllReg.norm_fourier_le_rpow {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (n : ℕ) (w : V) :
    ‖𝓕 f w‖ ≤ 2 ^ n * (1 + 2 ^ n) * derivL1Norm f n * (1 + ‖w‖) ^ (-(n : ℝ)) := by sorry
