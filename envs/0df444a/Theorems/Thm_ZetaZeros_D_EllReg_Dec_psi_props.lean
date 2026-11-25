-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_Dec_psi_props
-- name    : ZetaZeros.D.EllReg.Dec.psi_props
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:14:08.33187+00:00
-- url     : https://prove2.me/theorems/c7ad1937-2c17-40b5-8d52-96c7a120a64b
-- title:
--   Dec: psi props
-- statement:
--   The Dec construction uses the psi props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L121-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L121-L159

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

theorem ZetaZeros.D.EllReg.Dec.psi_props (x0 : E d) (ψ0 : E d → ℝ) (r : ℝ) (hψ : ContDiff ℝ ∞ ψ0) (hψc : HasCompactSupport ψ0)
    (hψ1 : ∀ y ∈ ball (0 : E d) 1, ψ0 y = 1) (hψs : tsupport ψ0 ⊆ ball 0 2) (hr : 0 < r) :
    ContDiff ℝ ∞ (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ∧
    HasCompactSupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ∧
    tsupport (fun x => ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ)) ⊆ ball x0 (2 * r) ∧
    ∀ x ∈ ball x0 r, ((ψ0 (r⁻¹ • (x - x0)) : ℝ) : ℂ) = 1 := by sorry
