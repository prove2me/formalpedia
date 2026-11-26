-- Prove2me | Theorems.Thm_section5_majority_decision_correct
-- name    : section5_majority_decision_correct
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:52:42.183953+00:00
-- url     : https://prove2.me/theorems/238fa359-9a08-5593-bce0-525b64e2d526
-- title:
--   Correct orientation when the majority error event fails
-- statement:
--   For real vectors w,u, a Boolean sign b and a triple z of grid examples, assume that fewer than two bounded-window orientation votes disagree with b. The majority-oriented direction then satisfies $$\operatorname{oriented}(w,u,z)=(-1)^b u.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5OrientationDecision.lean, lines 27–30.

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
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_majority_decision_correct {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (flip : Bool) (z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q))
    (h : ¬ section5_quantized_majority_error w u flip z) :
    section5_oriented_direction w u z=(if flip then -u else u) := by sorry
