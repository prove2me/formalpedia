-- Prove2me | Theorems.Thm_section5_majority_sign_circuit
-- name    : section5_majority_sign_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:17:59.508019+00:00
-- url     : https://prove2.me/theorems/eb4dbfa8-33ae-4114-b861-fdbd74fb3575
-- title:
--   Majority-controlled fixed-point vector sign circuit
-- statement:
--   Let three vote wires be injective and a distinct control start at zero. Let n input components have width a+1 and output components width a+2, with the source's disjointness conditions for input, output, control and clean (a+3)-bit workspace. On zero outputs and workspace, a reversible circuit preserves all wires outside control and outputs, and writes $$\operatorname{out}'=(-1)^{\operatorname{majority}(v_0,v_1,v_2)}\operatorname{in},\qquad |C|\le3+19(a+2)n,$$ under fixed-point decoding of precision f.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5MajoritySignCircuit.lean, lines 11–26. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
import Definitions.Def_Section5Verified_Section5MajorityCircuit
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Mathlib
import Theorems.Thm_section5_majority_circuit_action
import Theorems.Thm_section5_vector_sign_output_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_majority_sign_circuit {m n : ℕ} (a f : ℕ)
    (votes : Fin 3 ↪ Fin m) (ctrl : Fin m) (ht : ctrl ∉ Set.range votes)
    (input : Fin n → Fin (a+1) ↪ Fin m) (output : Fin n → Fin (a+2) ↪ Fin m)
    (anc : Fin (a+3) ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e b, output i e ≠ output j b)
    (hio : ∀ i j e b, input i e ≠ output j b)
    (hco : ∀ i e, ctrl ≠ output i e) (hca : ∀ e, ctrl ≠ anc e)
    (hoa : ∀ i e b, output i e ≠ anc b) (hic : ∀ i e, input i e ≠ ctrl) :
    ∃ c : Circuit gatesRev m, c.size ≤ 3+19*(a+2)*n ∧
      ∀ z : Qubits m, z ctrl=false → (∀ e, z (anc e)=false) → (∀ i e, z (output i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ≠ ctrl → (∀ i, j ∉ Set.range (output i)) → z' j=z j) ∧
          (WithLp.toLp 2 fun i => readFp (section5_msb_register (output i)) f z')=
            if section5_majority_bit (z (votes 0)) (z (votes 1)) (z (votes 2)) then
              -(WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z)
            else (WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z) := by sorry
