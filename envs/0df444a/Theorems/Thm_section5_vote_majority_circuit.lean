-- Prove2me | Theorems.Thm_section5_vote_majority_circuit
-- name    : section5_vote_majority_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:18.048247+00:00
-- url     : https://prove2.me/theorems/44b3e903-a1b0-426a-bd87-0906e869c958
-- title:
--   Six-gate majority of three label disagreements
-- statement:
--   Let three label wires and three prediction wires be injective and mutually disjoint, and let t lie outside prediction wires. A reversible circuit of exactly six gates, with t initially zero, returns $$t'=\operatorname{majority}(p_0\mathbin{\mathrm{xor}}l_0,p_1\mathbin{\mathrm{xor}}l_1,p_2\mathbin{\mathrm{xor}}l_2).$$ Every wire outside the prediction wires and t is preserved.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5VoteMajorityCircuit.lean, lines 24–31.

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
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5MajorityCircuit
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Definitions.Def_Section5Verified_Section5VoteMajorityCircuit
import Mathlib
import Theorems.Thm_section5_embed_classical_gate_action
import Theorems.Thm_section5_majority_circuit_action
import Theorems.Thm_section5_replace_wires_eq_update
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_vote_majority_circuit {m : ℕ} (labels prediction : Fin 3 ↪ Fin m)
    (t : Fin m) (hdisj : ∀ i j, labels i ≠ prediction j) (ht : t ∉ Set.range prediction) :
    ∃ c : Circuit gatesRev m, c.size=6 ∧
      ∀ z : Qubits m, z t=false →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          z' t=section5_majority_bit (xor (z (prediction 0)) (z (labels 0)))
            (xor (z (prediction 1)) (z (labels 1))) (xor (z (prediction 2)) (z (labels 2))) ∧
          ∀ j, j ∉ Set.range prediction → j ≠ t → z' j=z j := by sorry
