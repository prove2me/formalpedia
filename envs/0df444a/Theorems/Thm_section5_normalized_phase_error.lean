-- Prove2me | Theorems.Thm_section5_normalized_phase_error
-- name    : section5_normalized_phase_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:29:05.202805+00:00
-- url     : https://prove2.me/theorems/9266fc7d-bdc2-46eb-af13-3c1738adca76
-- title:
--   Error of the normalized sampled threshold phase state
-- statement:
--   Let $w\in\mathbb R^n$ satisfy $\|w\|_2=1$, and let $M\ge1$ be an integer with $M\ge128n^2$. Put $\delta=\sqrt{4\pi/M}$, $R=M\delta/2$, and let $r_M$ round each coordinate down on the lattice $-R+\delta\mathbb Z$. Write $G(x)=\prod_i\sqrt{\varphi(x_i)}$ and $f_w(x)=\operatorname{sgn}\langle w,x\rangle$, with sign $+1$ at zero. Define $\Phi_w=f_wG$ and $\Psi_{w,M}=1_{(-R,R]^n}(f_wG)\circ r_M$. Then
--
--   $$\left\|\frac{\Psi_{w,M}}{\|\Psi_{w,M}\|_2}-\Phi_w\right\|_2\le4n\sqrt{32/M}+2(8n/M)^{1/4}+2\sqrt{2n}\,e^{-\pi M/4}.$$
--
--   This is an analytic approximation of normalized phase states in $L^2$, used before transferring to finite registers.
-- source:
--   Original normalized phase-state estimate for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D. Formalization: Solutions/Section5PhaseStateError.lean, lines 167–216.

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
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_discretization_integral_bound
import Theorems.Thm_section5_discretization_measurable
import Theorems.Thm_section5_gaussian_pi_density
import Theorems.Thm_section5_gaussian_sampling_full
import Theorems.Thm_section5_l2_norm_sq
import Theorems.Thm_section5_sampled_phase_toLp_ne_zero
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example Aux_w_53_hermite

theorem section5_normalized_phase_error {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖=1) (M : ℕ) (hM : 0 < M) (hsize : 128*(n:ℝ)^2 ≤ M) :
    ‖NormedSpace.normalize ((section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M))-
      (section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)‖ ≤
        4*n*Real.sqrt (32/M)+2*(8*n/M)^(1/4:ℝ)+
          2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by sorry
