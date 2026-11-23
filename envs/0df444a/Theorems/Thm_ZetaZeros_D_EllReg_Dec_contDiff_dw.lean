-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_Dec_contDiff_dw
-- name    : ZetaZeros.D.EllReg.Dec.contDiff_dw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:32.481051+00:00
-- url     : https://prove2.me/theorems/e7f8bdde-2210-49ad-9c2a-455b7c83f939
-- title:
--   Dec: cont Diff dw
-- statement:
--   The Dec construction uses the cont Diff dw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L14-L19

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose
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
open ZetaZeros.D.EllReg.Dec
variable {d : ℕ}

theorem ZetaZeros.D.EllReg.Dec.contDiff_dw {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) (w : List (Fin d)) : ContDiff ℝ ∞ (dw w f) := by sorry
