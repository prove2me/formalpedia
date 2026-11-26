-- Prove2me | Theorems.Thm_section5_gaussian_event_probability_transfer
-- name    : section5_gaussian_event_probability_transfer
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:28:01.216478+00:00
-- url     : https://prove2.me/theorems/24886b24-73a2-542b-a449-35ccbd3ef23d
-- title:
--   Gaussian event probabilities from normalized sampled amplitudes
-- statement:
--   Let $n,M\in\mathbb N$ with $M\ge1$ and $M\ge128n^2$. Put $\delta=\sqrt{4\pi/M}$, $R=M\delta/2$, and let $r_M$ round each coordinate down on the centered lattice. Let $G(x)=\prod_i\sqrt{\varphi(x_i)}$, with $\varphi$ the standard Gaussian density, and let $A_M$ be the $L^2$ normalization of $1_{(-R,R]^n}(x)G(r_M(x))$. For every measurable $S\subseteq\mathbb R^n$,
--
--   $$\left|\int_S|A_M(x)|^2\,dx-\Pr_{X\sim N(0,I_n)}(X\in S)\right|\le8n\sqrt{32/M}+4\sqrt{2n}\,e^{-\pi M/4}.$$
--
--   This gives an eventwise probability comparison between the normalized sampled amplitude and the continuous Gaussian law.
-- source:
--   Original Gaussian probability-transfer result for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Formalization: Solutions/Section5GaussianProbabilityTransfer.lean, lines 38–63.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianProbabilityTransfer
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Mathlib
import Theorems.Thm_section5_continuous_event_stability
import Theorems.Thm_section5_gaussian_pi_density
import Theorems.Thm_section5_gaussian_sampling_full
import Theorems.Thm_section5_l2_norm_sq
import Theorems.Thm_section5_sampled_gaussian_toLp_ne_zero
set_option autoImplicit false
open MeasureTheory

theorem section5_gaussian_event_probability_transfer (n M : ℕ) (hM : 0 < M)
    (hsize : 128*(n:ℝ)^2 ≤ M) (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    |(∫ x in s, ‖section5_normalized_sampled_gaussian n M hM x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))))-
        (Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)).real s| ≤
      8*n*Real.sqrt (32/M)+4*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by sorry
