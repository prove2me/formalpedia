-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_derivL1Norm_rescaled_difference_le
-- name    : ZetaZeros.D.EllReg.derivL1Norm_rescaled_difference_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:57.083641+00:00
-- url     : https://prove2.me/theorems/e15621a6-0648-58e3-be99-fb9ac9f8b561
-- title:
--   Ell Reg: deriv L1 Norm rescaled difference le
-- statement:
--   The Ell Reg construction uses the deriv L1 Norm rescaled difference le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDer.lean#L14-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernDer.lean#L14-L106

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernGr
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDer
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
set_option maxHeartbeats 800000

theorem ZetaZeros.D.EllReg.derivL1Norm_rescaled_difference_le {d : ℕ} (ψ : E d → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (x0 : E d) (r0 : ℝ) (n : ℕ) :
    ∃ K : ℝ, ∀ r : ℝ, 0 < r → r ≤ r0 →
      derivL1Norm (fun y => ψ y * (b (x0 + r • y) - b x0)) n ≤ K * r := by sorry
