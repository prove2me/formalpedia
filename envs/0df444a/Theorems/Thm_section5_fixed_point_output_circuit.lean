-- Prove2me | Theorems.Thm_section5_fixed_point_output_circuit
-- name    : section5_fixed_point_output_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:04.210203+00:00
-- url     : https://prove2.me/theorems/893483c1-67af-5713-b0c6-0c623c22e2bb
-- title:
--   Circuit for sign-dependent fixed-point output
-- statement:
--   Let input and output registers have widths a+1 and a+2, let the control avoid output and a clean (a+3)-bit workspace, and let output be disjoint from input and workspace. A reversible circuit on zero output and workspace preserves every other wire and writes, for every fractional precision f, $$\operatorname{readFp}_f(\text{output}')=(-1)^{\text{control}}\operatorname{readFp}_f(\text{input}),\qquad |C|\le19(a+2).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5FixedPointOutputCircuit.lean, lines 56–68. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5AffineCopy
import Definitions.Def_Section5Verified_Section5ConditionalNegation
import Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Mathlib
import Theorems.Thm_section5_affine_copy_circuit
import Theorems.Thm_section5_conditional_negation_circuit
import Theorems.Thm_section5_signed_fixed_point_output
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_fixed_point_output_circuit {m : ℕ} (a f : ℕ) (ctrl : Fin m)
    (input : Fin (a+1) ↪ Fin m) (output : Fin (a+2) ↪ Fin m)
    (anc : Fin (a+3) ↪ Fin m)
    (hio : ∀ i j, input i ≠ output j)
    (hco : ∀ i, ctrl ≠ output i) (hca : ∀ i, ctrl ≠ anc i)
    (hoa : ∀ i j, output i ≠ anc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 19*(a+2) ∧
      ∀ z : Qubits m, (∀ i, z (output i)=false) → (∀ i, z (anc i)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range output → z' j=z j) ∧
          readFp (section5_msb_register output) f z'=
            if z ctrl then -readFp (section5_msb_register input) f z
              else readFp (section5_msb_register input) f z := by sorry
