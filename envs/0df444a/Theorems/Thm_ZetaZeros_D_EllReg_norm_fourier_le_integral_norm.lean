-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_norm_fourier_le_integral_norm
-- name    : ZetaZeros.D.EllReg.norm_fourier_le_integral_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:14.357329+00:00
-- url     : https://prove2.me/theorems/f4c9aa83-2283-4262-b0a8-510507dce7cb
-- title:
--   Ell Reg: norm fourier le integral norm
-- statement:
--   The Ell Reg construction uses the norm fourier le integral norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/BaseLevel.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/BaseLevel.lean#L8-L9

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_BaseLevel
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

theorem ZetaZeros.D.EllReg.norm_fourier_le_integral_norm {d : ℕ} (g : E d → ℂ) (ξ : E d) : ‖𝓕 g ξ‖ ≤ ∫ x, ‖g x‖ := by sorry
