-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_WD_om_shift
-- name    : ZetaZeros.D.EllReg.WD.om_shift
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:14:00.828562+00:00
-- url     : https://prove2.me/theorems/3ae55aa0-be0c-4ead-818a-9d8f013ef553
-- title:
--   WD: om shift
-- statement:
--   The WD construction uses the om shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightDiff.lean#L59-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightDiff.lean#L59-L83

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

theorem ZetaZeros.D.EllReg.WD.om_shift (s M ε : ℝ) (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ζ η v : E d)
    (hv : ‖ζ - η‖ ≤ ‖v‖) :
    om s M ε ζ ≤ (2 * (1 + ‖v‖ ^ 2)) ^ (|s / 2| + M / 2) * om s M ε η := by sorry
