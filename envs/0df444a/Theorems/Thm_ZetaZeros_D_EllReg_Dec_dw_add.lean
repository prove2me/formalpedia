-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_Dec_dw_add
-- name    : ZetaZeros.D.EllReg.Dec.dw_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:36.498368+00:00
-- url     : https://prove2.me/theorems/5199d3e3-8d31-4d1f-b57d-904e9246f173
-- title:
--   Dec: dw add
-- statement:
--   The Dec construction uses the dw add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L21-L34

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

theorem ZetaZeros.D.EllReg.Dec.dw_add {f g : E d → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List (Fin d)) :
    dw w (fun y => f y + g y) = fun y => dw w f y + dw w g y := by sorry
