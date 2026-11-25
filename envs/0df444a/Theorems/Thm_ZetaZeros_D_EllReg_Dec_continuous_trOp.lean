-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_Dec_continuous_trOp
-- name    : ZetaZeros.D.EllReg.Dec.continuous_trOp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:14:08.661684+00:00
-- url     : https://prove2.me/theorems/1718289d-7cd1-477e-bb86-5c955cd942c2
-- title:
--   Dec: continuous tr Op
-- statement:
--   The Dec construction uses the continuous tr Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L73-L78

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose
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
open ZetaZeros.D.EllReg.Dec
variable {d : ℕ}

theorem ZetaZeros.D.EllReg.Dec.continuous_trOp (m : ℕ) (b : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (φ : E d → ℂ)
    (hb : ∀ n w, ContDiff ℝ ∞ (b n w)) (hφ : ContDiff ℝ ∞ φ) : Continuous (trOp m b φ) := by sorry
