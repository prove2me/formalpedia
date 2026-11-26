-- Prove2me | Theorems.Thm_section5_majority_circuit_action
-- name    : section5_majority_circuit_action
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:02:21.280823+00:00
-- url     : https://prove2.me/theorems/7d144ba6-9a58-5f14-9cde-3eb6edbe5e7e
-- title:
--   Exact action of the three-bit majority circuit
-- statement:
--   Let v_0,v_1,v_2 be distinct wires and let t be outside these wires. For every basis string z, the three-gate majority circuit changes only t and satisfies $$z_t'=z_t\mathbin{\mathrm{xor}}\operatorname{majority}(z_{v_0},z_{v_1},z_{v_2}),\qquad U_C|z\rangle=|z'\rangle.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5MajorityCircuit.lean, lines 26–30.

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
import Mathlib
import Theorems.Thm_section5_embed_classical_gate_action
import Theorems.Thm_section5_replace_wires_eq_update
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_majority_circuit_action {m : ℕ} (v : Fin 3 ↪ Fin m) (t : Fin m)
    (ht : t ∉ Set.range v) (z : Qubits m) :
    act (section5_majority_circuit v t ht).unitary (ket z)=
      ket (Function.update z t
        (xor (z t) (section5_majority_bit (z (v 0)) (z (v 1)) (z (v 2))))) := by sorry
