-- Prove2me | Theorems.Thm_section5_qex_negative_orientation_vote_quarter
-- name    : section5_qex_negative_orientation_vote_quarter
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:35:33.283852+00:00
-- url     : https://prove2.me/theorems/742f2107-1061-50cb-aeb1-bab20749daa2
-- title:
--   Finite-QEX orientation error for an opposite candidate
-- statement:
--   Let $n\ge1$, $q\ge1$, and $2^q\ge2^{30}n^2$. Let $w,u\in\mathbb R^n$ be unit vectors with $\|w+u\|_2\le1/6$. For centered grid points $x_z$ of spacing $\sqrt{4\pi/2^q}$, put $p(z)=e^{-\|x_z\|^2/2}/\sum_y e^{-\|x_y\|^2/2}$. Let $f_v(x)=\operatorname{sgn}\langle v,x\rangle$, with sign $+1$ at zero. Then
--
--   $$\sum_{z:\,f_w(x_z)=f_u(x_z)}p(z)\le\frac14.$$
--
--   When the candidate is close to the opposite direction, agreement is the erroneous orientation vote; this bounds its probability directly in the finite QEX distribution.
-- source:
--   Original negative-orientation subroutine supporting Section 5 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. Formalization: Solutions/Section5SignedOrientationVote.lean, lines 91–125. The Gaussian disagreement foundation credits kmehltretter82, accepted submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), in Solutions/Section5GaussianDisagreementFoundation.lean.

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
import Definitions.Def_Section5Verified_Section5DiscretizationLemma
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Mathlib
import Theorems.Thm_section5_gaussian_disagreement_proved
import Theorems.Thm_section5_ideal_phase_distance_sq
import Theorems.Thm_section5_ideal_phase_neg
import Theorems.Thm_section5_normalized_phase_sum_eq_qex
import Theorems.Thm_section5_orientation_phase_error_small
import Theorems.Thm_section5_qex_phase_agreement
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_qex_negative_orientation_vote_quarter (n q : ℕ) (hn : 1 ≤ n) (hq : 0 < q)
    (hgrid : 1073741824*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1) (hclose : ‖w+u‖ ≤ 1/6) :
    (∑ z : Qubits (n*q),
      if ltf w 0 (gridPoint z) = ltf u 0 (gridPoint z) then
        gridWeight z/(∑ x : Qubits (n*q), gridWeight x) else 0) ≤ 1/4 := by sorry
