-- Prove2me | Theorems.Thm_section5_classical_controlled_subtractor
-- name    : section5_classical_controlled_subtractor
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:15.840976+00:00
-- url     : https://prove2.me/theorems/41010a9e-71a9-5bc1-aa9c-c7c741e743ee
-- title:
--   Clean controlled variable-register subtraction
-- statement:
--   For every natural width w there is a reversible circuit on 3w+2 wires with a control, two w-bit registers and w+1 clean ancillas, implementing controlled in-place subtraction and restoring the ancillas: $$|c,a,b,0^{w+1}\rangle\mapsto|c,a,b-c a\bmod2^w,0^{w+1}\rangle,\qquad|C|\le24w.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ControlledArithmetic.lean, lines 43–47. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_Aux_w54_arith_ctrlAddInPlaceCircuit_implements
import Theorems.Thm_Aux_w54_arith_ctrlAddInPlaceFn_ctrlSubInPlaceFn
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_classical_controlled_subtractor (w : ℕ) :
    ∃ c : Circuit gatesRev ((1+w+w)+(w+1)), c.size ≤ 24*w ∧
      ∀ x : Qubits (1+w+w),
        act c.unitary (ket (padZero (1+w+w) (w+1) x))=
          ket (padZero (1+w+w) (w+1) (Aux_w54_arith.ctrlSubInPlaceFn w x)) := by sorry
