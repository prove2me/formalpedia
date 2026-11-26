-- Prove2me | Theorems.Thm_section5_raw_orientation_success
-- name    : section5_raw_orientation_success
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T21:03:45.137066+00:00
-- url     : https://prove2.me/theorems/e7e84334-1c7a-5ffb-b00b-508096ef615c
-- title:
--   Conditional orientation of an unnormalized direction
-- statement:
--   Let n≥1, 2^q≥2^40n², w real unit, r∈R^n nonzero and 0<ε<1. Suppose a sign b satisfies ‖(−1)^b r/‖r‖−w‖≤ε/6. For the majority-oriented output R from three independent Gaussian grid examples, $$\Pr[R\ne0\ \text{and}\ \|R/\|R\|-w\|\le\varepsilon]\ge27/32.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5RawOrientation.lean, lines 41–49. The Gaussian-disagreement foundation is credited to kmehltretter82, accepted Prove2Me submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), copied in Solutions/Section5GaussianDisagreementFoundation.lean.

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
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Mathlib
import Theorems.Thm_section5_quantized_orientation_success
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

open Classical in
theorem section5_raw_orientation_success (n q : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w r : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hr : r ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (flip : Bool) (hclose : ‖(if flip then -NormedSpace.normalize r else NormedSpace.normalize r)-w‖ ≤ ε/6) :
    (∑ z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
      if section5_oriented_direction w r z ≠ 0 ∧
          ‖NormedSpace.normalize (section5_oriented_direction w r z)-w‖ ≤ ε then
        section5_three_qex_weight n q z else 0) ≥ 27/32 := by sorry
