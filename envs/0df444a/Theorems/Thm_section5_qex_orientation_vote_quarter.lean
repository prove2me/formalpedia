-- Prove2me | Theorems.Thm_section5_qex_orientation_vote_quarter
-- name    : section5_qex_orientation_vote_quarter
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:35:30.576465+00:00
-- url     : https://prove2.me/theorems/6b59cf10-39c7-5b07-b7c5-8ced04b8f4b8
-- title:
--   A finite-QEX orientation vote has error at most $1/4$
-- statement:
--   Let $n\ge1$, $q\ge1$, and $2^q\ge2^{30}n^2$. Let $w,u\in\mathbb R^n$ be unit vectors with $\|w-u\|_2\le1/6$. For an $nq$-bit string $z$, let $x_z$ be the centered grid point of spacing $\sqrt{4\pi/2^q}$ and let $p(z)=e^{-\|x_z\|^2/2}/\sum_y e^{-\|x_y\|^2/2}$. With $f_v(x)=\operatorname{sgn}\langle v,x\rangle$, using sign $+1$ at zero,
--
--   $$\sum_{z:\,f_w(x_z)\ne f_u(x_z)}p(z)\le\frac14.$$
--
--   Thus a sample from the finite QEX grid distribution gives an orientation vote with the stated error for a sufficiently close candidate.
-- source:
--   Original finite-QEX orientation subroutine supporting Section 5 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. Formalization: Solutions/Section5OrientationVote.lean, lines 42–71. The Gaussian disagreement dependency credits kmehltretter82, accepted submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), in Solutions/Section5GaussianDisagreementFoundation.lean.

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
import Theorems.Thm_section5_normalized_phase_distance_eq_qex
import Theorems.Thm_section5_orientation_phase_error_small
import Theorems.Thm_section5_qex_phase_disagreement
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_qex_orientation_vote_quarter (n q : ℕ) (hn : 1 ≤ n) (hq : 0 < q)
    (hgrid : 1073741824*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1) (hclose : ‖w-u‖ ≤ 1/6) :
    (∑ z : Qubits (n*q),
      if ltf w 0 (gridPoint z) ≠ ltf u 0 (gridPoint z) then
        gridWeight z/(∑ x : Qubits (n*q), gridWeight x) else 0) ≤ 1/4 := by sorry
