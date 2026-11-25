-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_Dec_dw_const_mul
-- name    : ZetaZeros.D.EllReg.Dec.dw_const_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:16.288264+00:00
-- url     : https://prove2.me/theorems/a6c7b70d-66ca-5e8b-a111-f3eb3f75c003
-- title:
--   Dec: dw const mul
-- statement:
--   The Dec construction uses the dw const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L45-L57

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

theorem ZetaZeros.D.EllReg.Dec.dw_const_mul {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℂ) (w : List (Fin d)) :
    dw w (fun y => c * f y) = fun y => c * dw w f y := by sorry
