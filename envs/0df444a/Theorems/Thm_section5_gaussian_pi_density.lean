-- Prove2me | Theorems.Thm_section5_gaussian_pi_density
-- name    : section5_gaussian_pi_density
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-26T19:49:02.423859+00:00
-- url     : https://prove2.me/theorems/0e892fa2-faf7-46fd-af47-10be8a0616b8
-- title:
--   Density of a product of standard Gaussians
-- statement:
--   For $n\in\mathbb N$, let $\gamma$ be the standard normal probability measure on $\mathbb R$, let $\lambda$ be Lebesgue measure, and put $\varphi_n(x)=\prod_{i=1}^n(2\pi)^{-1/2}e^{-x_i^2/2}$. Then
--
--   $$\gamma^{\otimes n}=\varphi_n\,\lambda^{\otimes n}.$$
--
--   This identifies the product Gaussian measure with its density relative to product Lebesgue measure, providing the measure conversion used in the wavefunction estimates.
-- source:
--   Original measure-theoretic auxiliary result for the Gaussian sampling estimates in Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D. Formalization: Solutions/Section5GaussianTail.lean, lines 57–73.

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
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

theorem section5_gaussian_pi_density (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
        (fun x => ENNReal.ofReal (section5_gaussian_density n x)) := by sorry
