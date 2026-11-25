-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_gr_zero
-- name    : ZetaZeros.D.EllReg.gr_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:17.576256+00:00
-- url     : https://prove2.me/theorems/2da64e23-3c0e-4a2d-900e-7644c08987ae
-- title:
--   Ell Reg: gr zero
-- statement:
--   The Ell Reg construction uses the gr zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernGr.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernGr.lean#L11-L16

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernGr
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

theorem ZetaZeros.D.EllReg.gr_zero {d : ℕ} (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ b x‖ ≤ L)
    (x0 y : E d) (r : ℝ) (hr : 0 < r) : ‖b (x0 + r • y) - b x0‖ ≤ L * (r * ‖y‖) := by sorry
