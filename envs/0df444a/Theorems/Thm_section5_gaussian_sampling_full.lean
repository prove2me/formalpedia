-- Prove2me | Theorems.Thm_section5_gaussian_sampling_full
-- name    : section5_gaussian_sampling_full
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:24:04.658254+00:00
-- url     : https://prove2.me/theorems/21eac79c-cf7a-5e9b-965e-0ded77489ea1
-- title:
--   Full-space error of the sampled Gaussian amplitude
-- statement:
--   Let $n,M\in\mathbb N$ with $M\ge1$ and $M\ge128n^2$. Put $\delta=\sqrt{4\pi/M}$, $R=M\delta/2$, and $r_M(x)_i=-R+\delta\lfloor(x_i+R)/\delta\rfloor$. Let $G(x)=\prod_i\sqrt{\varphi(x_i)}$, where $\varphi$ is the standard Gaussian density, and let $G_M(x)=1_{(-R,R]^n}(x)G(r_M(x))$. Then
--
--   $$\|G_M-G\|_{L^2(\mathbb R^n)}\le2n\sqrt{32/M}+\sqrt{2n}\,e^{-\pi M/4}.$$
--
--   This includes both grid sampling and omission of the Gaussian tails before normalization.
-- source:
--   Original combined Gaussian sampling bound for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D. Formalization: Solutions/Section5GaussianSampling.lean, lines 66–108.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Mathlib
import Theorems.Thm_section5_gaussian_amplitude_tail
import Theorems.Thm_section5_l2_norm_sq
import Theorems.Thm_section5_multivariate_sampling_227
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

theorem section5_gaussian_sampling_full (n M : ℕ) (hM : 0 < M)
    (hsize : 128*(n:ℝ)^2 ≤ M) :
    Real.sqrt (∫ x : Fin n → ℝ,
      ‖section5_sampled_gaussian_amplitude n M x-section5_gaussian_amplitude n x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) ≤
        2*n*Real.sqrt (32/M)+Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by sorry
