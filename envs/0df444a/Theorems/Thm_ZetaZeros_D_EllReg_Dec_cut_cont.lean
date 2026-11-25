-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_Dec_cut_cont
-- name    : ZetaZeros.D.EllReg.Dec.cut_cont
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:27.749476+00:00
-- url     : https://prove2.me/theorems/54c33e0c-b557-415d-9c02-8453be81ab33
-- title:
--   Dec: cut cont
-- statement:
--   The Dec construction uses the cut cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L99-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L99-L116

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

theorem ZetaZeros.D.EllReg.Dec.cut_cont {U : Set (E d)} (hU : IsOpen U) {u : E d → ℂ} (hu : ContinuousOn u U) {χ : E d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    Continuous (cut χ u) ∧ HasCompactSupport (cut χ u) := by sorry
