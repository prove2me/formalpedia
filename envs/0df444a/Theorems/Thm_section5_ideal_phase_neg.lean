-- Prove2me | Theorems.Thm_section5_ideal_phase_neg
-- name    : section5_ideal_phase_neg
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:17.212575+00:00
-- url     : https://prove2.me/theorems/6ff3f7d7-beb4-5dd3-abd7-aaf5544c31ca
-- title:
--   Negating the threshold direction negates its ideal phase state
-- statement:
--   Let $w\in\mathbb R^n$ have norm one. Write $f_w(x)=\operatorname{sgn}(\langle w,x\rangle)$ with sign at zero equal to $1$, and let $g_n$ be the square root of the standard Gaussian density. Regard $\Psi_w(x)=f_w(x)g_n(x)$ as an element of complex $L^2(\mathbb R^n,dx)$. Then
--
--   $$
--   \Psi_{-w}=-\Psi_w\quad\text{in }L^2(\mathbb R^n,dx).
--   $$
--
--   The equality concerns equivalence classes of functions, allowing the exceptional threshold hyperplane.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5SignedOrientationVote.lean, section5_ideal_phase_neg, lines 21–40.

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
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_gaussian_disagreement_proved
import Theorems.Thm_section5_gaussian_pi_density
import Theorems.Thm_section5_ideal_phase_distance_sq
import Theorems.Thm_section5_l2_norm_sq
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_ideal_phase_neg {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    (section5_ideal_phase_memLp (-w)).toLp (section5_ideal_phase_state (-w)) =
      -(section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w) := by sorry
