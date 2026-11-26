-- Prove2me | Theorems.Thm_section5_gaussian_amplitude_tail
-- name    : section5_gaussian_amplitude_tail
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:17.865848+00:00
-- url     : https://prove2.me/theorems/a4ddfa04-613d-5eab-b8a1-0ce3fa9fb263
-- title:
--   Gaussian amplitude tail outside the sampling box
-- statement:
--   Let $n\ge0$ and $M>0$ be natural numbers. Set $\Delta_M=\sqrt{4\pi/M}$, $R_M=M\Delta_M/2$, $B_M=(-R_M,R_M]^n$, and $g_n(x)=\prod_{i=1}^n\sqrt{(2\pi)^{-1/2}e^{-x_i^2/2}}$, viewed as a complex-valued amplitude. With product Lebesgue measure,
--
--   $$
--   \left(\int_{B_M^{\mathrm c}}|g_n(x)|^2\,dx\right)^{1/2}\le\sqrt{2n}\,e^{-\pi M/4}.
--   $$
--
--   This estimates the continuous amplitude norm discarded when restricting the Gaussian to the sampling box.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5GaussianTail.lean, section5_gaussian_amplitude_tail, lines 168–191.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Mathlib
import Theorems.Thm_section5_gaussian_grid_tail_230
import Theorems.Thm_section5_gaussian_pi_density
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

theorem section5_gaussian_amplitude_tail (n M : ℕ) (hM : 0 < M) :
    Real.sqrt (∫ x in (section5_grid_box n M)ᶜ, ‖section5_gaussian_amplitude n x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) ≤
        Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by sorry
