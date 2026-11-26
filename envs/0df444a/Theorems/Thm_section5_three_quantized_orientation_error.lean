-- Prove2me | Theorems.Thm_section5_three_quantized_orientation_error
-- name    : section5_three_quantized_orientation_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:54:23.694063+00:00
-- url     : https://prove2.me/theorems/40d78ac2-fd09-59c2-82d0-e96ed972b43e
-- title:
--   Three quantized votes have bounded majority error
-- statement:
--   Let n≥1, 2^q≥2^40n², w,u be real unit vectors and b a Boolean sign with ‖(−1)^b u−w‖≤1/6. For three independent normalized Gaussian grid examples and their bounded-window orientation votes, $$\Pr[\text{at least two votes are incorrect}]\le5/32.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5QuantizedOrientation.lean, lines 98–108. The Gaussian-disagreement foundation is credited to kmehltretter82, accepted Prove2Me submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), copied in Solutions/Section5GaussianDisagreementFoundation.lean.

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
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Mathlib
import Theorems.Thm_section5_quantized_orientation_quarter
import Theorems.Thm_section5_three_independent_errors
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_three_quantized_orientation_error (n q : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (flip : Bool) (hclose : ‖(if flip then -u else u)-w‖ ≤ 1/6) :
    open Classical in
    (∑ a : Qubits (n*q), ∑ b : Qubits (n*q), ∑ c : Qubits (n*q),
      if (section5_quantized_orientation_error w u flip a ∧ section5_quantized_orientation_error w u flip b) ∨
        (section5_quantized_orientation_error w u flip a ∧ section5_quantized_orientation_error w u flip c) ∨
        (section5_quantized_orientation_error w u flip b ∧ section5_quantized_orientation_error w u flip c)
      then section5_qex_distribution n q a*section5_qex_distribution n q b*
        section5_qex_distribution n q c else 0) ≤ 5/32 := by sorry
