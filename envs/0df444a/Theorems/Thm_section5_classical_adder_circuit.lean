-- Prove2me | Theorems.Thm_section5_classical_adder_circuit
-- name    : section5_classical_adder_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:51:16.948353+00:00
-- url     : https://prove2.me/theorems/8d602f15-9b55-4a5e-aca3-be9306624c7c
-- title:
--   A clean reversible adder with at most $14w$ gates
-- statement:
--   For every $w\in\mathbb N$, there exists a NOT/CNOT/Toffoli circuit $C$ on $2w+1$ wires such that, for all $w$-bit unsigned integers $A,B$ encoded least significant bit first,
--
--   $$|C|\le14w,\qquad U_C|A,B,0\rangle=|A,(A+B)\bmod2^w,0\rangle.$$
--
--   This provides an exact in-place modular adder with one ancilla returned to zero.
-- source:
--   Original gatesRev realization in Solutions/Section5ReversibleAdder.lean, lines 64–73, supporting Section 5 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. The accepted arithmetic foundation is by Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), credited in Solutions/Section5LcgArithmeticFoundation.lean; its adder uses the Cuccaro MAJ/UMA construction.

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
import Theorems.Thm_Aux_w54_arith_addInPlaceCircuit_implements
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_classical_adder_circuit (w : ℕ) :
    ∃ c : Circuit gatesRev ((w+w)+1), c.size ≤ 14*w ∧
      ∀ x : Qubits (w+w),
        act c.unitary (ket (padZero (w+w) 1 x))=
          ket (padZero (w+w) 1 (Aux_w54_arith.addInPlaceFn w x)) := by sorry
