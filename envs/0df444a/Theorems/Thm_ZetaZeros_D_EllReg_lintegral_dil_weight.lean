-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_lintegral_dil_weight
-- name    : ZetaZeros.D.EllReg.lintegral_dil_weight
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:39.817128+00:00
-- url     : https://prove2.me/theorems/75016f2e-eae8-59b2-b044-e88f0bdf8ba8
-- title:
--   Ell Reg: lintegral dil weight
-- statement:
--   The Ell Reg construction uses the lintegral dil weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDil.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDil.lean#L39-L53

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
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

theorem ZetaZeros.D.EllReg.lintegral_dil_weight (r : ℝ) (hr : 0 < r) (D : ℝ) (hD : (Module.finrank ℝ V : ℝ) < D) :
    (∫⁻ w : V, ENNReal.ofReal (r ^ Module.finrank ℝ V * (1 + ‖r • w‖) ^ (-D))) =
      ∫⁻ w : V, ENNReal.ofReal ((1 + ‖w‖) ^ (-D)) := by sorry
