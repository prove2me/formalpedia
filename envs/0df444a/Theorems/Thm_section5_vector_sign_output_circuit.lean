-- Prove2me | Theorems.Thm_section5_vector_sign_output_circuit
-- name    : section5_vector_sign_output_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:14:23.953798+00:00
-- url     : https://prove2.me/theorems/ea963b18-009f-4391-8e07-e700e57cfe72
-- title:
--   Sign-dependent fixed-point vector output circuit
-- statement:
--   Let n input components have fixed-point width a+1 and output components width a+2. Assume outputs pairwise disjoint, avoid all inputs and control, and avoid a clean (a+3)-bit workspace, which also avoids control. With outputs and workspace initially zero, a reversible circuit preserves all non-output wires and writes $$\operatorname{readFp}_f(\text{output}')=(-1)^{\text{control}}\operatorname{readFp}_f(\text{input}),\qquad|C|\le19(a+2)n.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5VectorSignOutputCircuit.lean, lines 12–25. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Definitions.Def_Section5Verified_Section5VectorSignOutputCircuit
import Mathlib
import Theorems.Thm_section5_clean_batch_all
import Theorems.Thm_section5_fixed_point_output_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_vector_sign_output_circuit {m n : ℕ} (a f : ℕ) (ctrl : Fin m)
    (input : Fin n → Fin (a+1) ↪ Fin m) (output : Fin n → Fin (a+2) ↪ Fin m)
    (anc : Fin (a+3) ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e b, output i e ≠ output j b)
    (hio : ∀ i j e b, input i e ≠ output j b)
    (hco : ∀ i e, ctrl ≠ output i e) (hca : ∀ e, ctrl ≠ anc e)
    (hoa : ∀ i e b, output i e ≠ anc b) :
    ∃ c : Circuit gatesRev m, c.size ≤ 19*(a+2)*n ∧
      ∀ z : Qubits m, (∀ e, z (anc e)=false) → (∀ i e, z (output i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (output i)) → z' j=z j) ∧
          (WithLp.toLp 2 fun i => readFp (section5_msb_register (output i)) f z')=
            if z ctrl then -(WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z)
            else (WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z) := by sorry
