-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_Dec_contDiff_mul_of_tsupport
-- name    : ZetaZeros.D.EllReg.Dec.contDiff_mul_of_tsupport
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:24.007729+00:00
-- url     : https://prove2.me/theorems/707d5876-27e7-4eaf-85eb-86ce32012c54
-- title:
--   Dec: cont Diff mul of tsupport
-- statement:
--   The Dec construction uses the cont Diff mul of tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L85-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L85-L97

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

theorem ZetaZeros.D.EllReg.Dec.contDiff_mul_of_tsupport {U : Set (E d)} (hU : IsOpen U) {g f : E d → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgU : tsupport g ⊆ U) (hf : ContDiffOn ℝ ∞ f U) : ContDiff ℝ ∞ (fun x => g x * f x) := by sorry
