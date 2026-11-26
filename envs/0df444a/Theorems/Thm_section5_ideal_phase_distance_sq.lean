-- Prove2me | Theorems.Thm_section5_ideal_phase_distance_sq
-- name    : section5_ideal_phase_distance_sq
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:00.707212+00:00
-- url     : https://prove2.me/theorems/2476b42d-6638-586a-aa00-216349469b61
-- title:
--   Ideal threshold-phase distance equals four times Gaussian disagreement
-- statement:
--   For $w\in\mathbb R^n$, let $f_w(x)=\operatorname{sgn}(\langle w,x\rangle)$, with the sign at zero equal to $1$. For arbitrary $w,u\in\mathbb R^n$, let $g_n$ be the square root of the standard Gaussian density and define $\Psi_w(x)=f_w(x)g_n(x)$ in $L^2(\mathbb R^n,dx;\mathbb C)$. Then
--
--   $$
--   \|\Psi_w-\Psi_u\|_{L^2}^2=4\Pr_{X\sim N(0,I_n)}\{f_w(X)\ne f_u(X)\}.
--   $$
--
--   This converts distances between ideal quantum-example phase amplitudes into Gaussian classification disagreement.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5OrientationEnergy.lean, section5_ideal_phase_distance_sq, lines 26–56.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Mathlib
import Theorems.Thm_section5_gaussian_pi_density
import Theorems.Thm_section5_l2_norm_sq
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_ideal_phase_distance_sq {n : ℕ} (w u : EuclideanSpace ℝ (Fin n)) :
    ‖(section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)-
      (section5_ideal_phase_memLp u).toLp (section5_ideal_phase_state u)‖^2 =
        4*disagree (ltf w 0) (ltf u 0) := by sorry
