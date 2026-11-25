-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_norm_fourier_comp_dil
-- name    : ZetaZeros.D.EllReg.norm_fourier_comp_dil
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:52.192424+00:00
-- url     : https://prove2.me/theorems/1c178522-8c53-5b62-bd60-cc07e9f0a430
-- title:
--   Ell Reg: norm fourier comp dil
-- statement:
--   The Ell Reg construction uses the norm fourier comp dil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDil.lean#L13-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDil.lean#L13-L37

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

theorem ZetaZeros.D.EllReg.norm_fourier_comp_dil (c : V → ℂ) (r : ℝ) (hr : 0 < r) (x0 w : V) :
    ‖𝓕 (fun x => c (r⁻¹ • (x - x0))) w‖ = r ^ Module.finrank ℝ V * ‖𝓕 c (r • w)‖ := by sorry
