-- Prove2me | Theorems.Thm_section5_quantized_orientation_quarter
-- name    : section5_quantized_orientation_quarter
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:48:40.779318+00:00
-- url     : https://prove2.me/theorems/a2c79f40-bc51-487e-ad32-2e2be0f5a436
-- title:
--   One quantized orientation vote has bounded error
-- statement:
--   Let n≥1 and 2^q≥2^40n². Let w,u be real unit vectors and let b be a Boolean sign with ‖(−1)^b u−w‖≤1/6. A label-disagreement vote formed from the bounded-window predictor u and the true homogeneous threshold label w, on a Gaussian grid example, has error probability $$\Pr[\text{vote}\ne b]\le1/4.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5QuantizedOrientation.lean, lines 63–69. The Gaussian-disagreement foundation is credited to kmehltretter82, accepted Prove2Me submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), copied in Solutions/Section5GaussianDisagreementFoundation.lean.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Definitions.Def_Section5Verified_Section5RealWindow
import Mathlib
import Theorems.Thm_section5_large_grid_fits_window
import Theorems.Thm_section5_qex_negative_orientation_vote_margin
import Theorems.Thm_section5_qex_orientation_vote_margin
import Theorems.Thm_section5_uniform_qex_window_error
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_quantized_orientation_quarter (n q : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (flip : Bool) (hclose : ‖(if flip then -u else u)-w‖ ≤ 1/6) :
    open Classical in
    (∑ z : Qubits (n*q), if section5_quantized_orientation_error w u flip z then
      section5_qex_distribution n q z else 0) ≤ 1/4 := by sorry
