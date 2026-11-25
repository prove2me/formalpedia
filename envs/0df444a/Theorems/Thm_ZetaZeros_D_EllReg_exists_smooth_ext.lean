-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_exists_smooth_ext
-- name    : ZetaZeros.D.EllReg.exists_smooth_ext
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:14:05.635494+00:00
-- url     : https://prove2.me/theorems/dd43b72b-0140-42af-923f-8c771ae8da6b
-- title:
--   Ell Reg: exists smooth ext
-- statement:
--   The Ell Reg construction uses the exists smooth ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/ExistsSmoothExt.lean#L12-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/ExistsSmoothExt.lean#L12-L37

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDer
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_ExistsSmoothExt
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

theorem ZetaZeros.D.EllReg.exists_smooth_ext {d : ℕ} {U : Set (E d)} {a : E d → ℂ} {x0 : E d} (hU : IsOpen U) (hx0 : x0 ∈ U)
    (ha : ContDiffOn ℝ ∞ a U) :
    ∃ r0 > 0, ball x0 (2 * r0) ⊆ U ∧ ∃ b : E d → ℂ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      ∀ x ∈ closedBall x0 (2 * r0), b x = a x := by sorry
