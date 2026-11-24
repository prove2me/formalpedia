-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_WF_contDiff_ev
-- name    : ZetaZeros.D.EllReg.WF.contDiff_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:02.563656+00:00
-- url     : https://prove2.me/theorems/0b90515a-d74d-4ca1-a529-3a62521c5253
-- title:
--   WF: cont Diff ev
-- statement:
--   The WF construction uses the cont Diff ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L62-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L62-L76

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

theorem ZetaZeros.D.EllReg.WF.contDiff_ev {L : List (List (Fin d) × (E d → ℂ))} (hL : ∀ p ∈ L, ContDiff ℝ ∞ p.2)
    {g : E d → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (ev L g) := by sorry
