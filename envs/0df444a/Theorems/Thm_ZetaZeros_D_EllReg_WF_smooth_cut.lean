-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_WF_smooth_cut
-- name    : ZetaZeros.D.EllReg.WF.smooth_cut
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:40.287265+00:00
-- url     : https://prove2.me/theorems/73b4acae-4222-47e3-9729-368235c17647
-- title:
--   WF: smooth cut
-- statement:
--   The WF construction uses the smooth cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L279-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L279-L293

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
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
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}

theorem ZetaZeros.D.EllReg.WF.smooth_cut {U : Set (E d)} (hU : IsOpen U) {a : E d → ℂ} (ha : ContDiffOn ℝ ∞ a U)
    {χ : E d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun y => (χ y : ℂ) * a y) := by sorry
