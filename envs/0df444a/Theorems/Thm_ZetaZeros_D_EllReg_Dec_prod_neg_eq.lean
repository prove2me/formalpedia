-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_Dec_prod_neg_eq
-- name    : ZetaZeros.D.EllReg.Dec.prod_neg_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:23.239042+00:00
-- url     : https://prove2.me/theorems/b1f65fa1-a045-5783-9991-581d79daa126
-- title:
--   Dec: prod neg eq
-- statement:
--   The Dec construction uses the prod neg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L161-L166

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

theorem ZetaZeros.D.EllReg.Dec.prod_neg_eq (n : ℕ) (w : Fin n → Fin d) (ξ : E d) :
    ((List.ofFn w).map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod = (-1 : ℂ) ^ n * mono w ξ := by sorry
