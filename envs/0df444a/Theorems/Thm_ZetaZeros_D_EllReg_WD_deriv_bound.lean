-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_WD_deriv_bound
-- name    : ZetaZeros.D.EllReg.WD.deriv_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:13:27.753694+00:00
-- url     : https://prove2.me/theorems/6a2d88ac-d981-5b5e-bd42-17ab832f3a90
-- title:
--   WD: deriv bound
-- statement:
--   The WD construction uses the deriv bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightDiff.lean#L129-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightDiff.lean#L129-L167

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

theorem ZetaZeros.D.EllReg.WD.deriv_bound (s M ε : ℝ) (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (γ v : E d) :
    |(2 * inner ℝ γ v) * (s / 2) * (1 + ‖γ‖ ^ 2) ^ (s / 2 - 1) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2)) +
      (1 + ‖γ‖ ^ 2) ^ (s / 2) *
        ((ε ^ 2 * (2 * inner ℝ γ v)) * (-(M / 2)) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2) - 1))|
    ≤ (|s| + M) * ‖v‖ * om (s - 1) M ε γ := by sorry
