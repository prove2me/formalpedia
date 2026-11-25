-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_WF_intg
-- name    : ZetaZeros.D.EllReg.WF.intg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:17.38096+00:00
-- url     : https://prove2.me/theorems/51dbaf68-8af9-5fcf-a138-a6c5485fe975
-- title:
--   WF: intg
-- statement:
--   The WF construction uses the intg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L295-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L295-L313

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

theorem ZetaZeros.D.EllReg.WF.intg {U K : Set (E d)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {u F : E d → ℂ}
    (hu : ContinuousOn u U) (hF : Continuous F) (hFK : ∀ y ∉ K, F y = 0) :
    Integrable (fun y => u y * F y) := by sorry
