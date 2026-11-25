-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_WD_base
-- name    : ZetaZeros.D.EllReg.WD.base
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:13:45.403746+00:00
-- url     : https://prove2.me/theorems/29411bdf-afe6-4c53-87ca-896f2584b045
-- title:
--   WD: base
-- statement:
--   The WD construction uses the base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightDiff.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightDiff.lean#L31-L43

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightDiff
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
open ZetaZeros.D.EllReg.WD
variable {d : ℕ}

theorem ZetaZeros.D.EllReg.WD.base (c : ℝ) (x y : E d) :
    1 + c ^ 2 * ‖x‖ ^ 2 ≤ 2 * (1 + c ^ 2 * ‖x - y‖ ^ 2) * (1 + c ^ 2 * ‖y‖ ^ 2) := by sorry
