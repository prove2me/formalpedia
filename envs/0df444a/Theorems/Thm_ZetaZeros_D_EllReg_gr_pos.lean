-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_gr_pos
-- name    : ZetaZeros.D.EllReg.gr_pos
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:14.519248+00:00
-- url     : https://prove2.me/theorems/fadc3747-2098-44b7-af6e-40cdf694c65d
-- title:
--   Ell Reg: gr pos
-- statement:
--   The Ell Reg construction uses the gr pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernGr.lean#L18-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/KernGr.lean#L18-L40

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

theorem ZetaZeros.D.EllReg.gr_pos {d : ℕ} (b : E d → ℂ) (hb : ContDiff ℝ ∞ b) (k : ℕ) (hk0 : 0 < k) (M : ℝ)
    (hM : ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ M) (x0 y : E d) (r : ℝ) (hr : 0 < r) :
    ‖iteratedFDeriv ℝ k (fun y => b (x0 + r • y) - b x0) y‖ ≤ M * r ^ k := by sorry
