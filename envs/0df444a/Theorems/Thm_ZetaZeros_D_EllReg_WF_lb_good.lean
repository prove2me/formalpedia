-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_WF_lb_good
-- name    : ZetaZeros.D.EllReg.WF.lb_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:09.470567+00:00
-- url     : https://prove2.me/theorems/f97a0b20-94cc-4b11-85fe-083114e5d45f
-- title:
--   WF: lb good
-- statement:
--   The WF construction uses the lb good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L128-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L128-L140

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

theorem ZetaZeros.D.EllReg.WF.lb_good {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) {K : Set (E d)} (hK : IsClosed K)
    (hfK : ∀ y ∉ K, f y = 0) : ∀ w : List (Fin d), Good w.length K (lb w f)
  := by sorry
