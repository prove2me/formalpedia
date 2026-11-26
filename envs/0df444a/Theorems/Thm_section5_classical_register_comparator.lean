-- Prove2me | Theorems.Thm_section5_classical_register_comparator
-- name    : section5_classical_register_comparator
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:49:35.40126+00:00
-- url     : https://prove2.me/theorems/5b615054-4aa4-4924-8b72-c4aa9e7cb7a0
-- title:
--   Clean unsigned register comparison
-- statement:
--   For natural w, there is a reversible circuit on 2w+2 wires with two w-bit unsigned registers, a comparison target and one clean ancilla. It toggles the target by the source's strict less-than comparison, preserves the input registers and restores the ancilla: $$|a,b,t,0\rangle\mapsto|a,b,t\mathbin{\mathrm{xor}}[a<b],0\rangle,\qquad|C|\le16w+1.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5RegisterComparison.lean, lines 37–41. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Theorems.Thm_Aux_w54_arith_ltRegCircuit_implements
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router

theorem section5_classical_register_comparator (w : ℕ) :
    ∃ c : Circuit gatesRev ((w+w+1)+1), c.size ≤ 16*w+1 ∧
      ∀ x : Qubits (w+w+1),
        act c.unitary (ket (padZero (w+w+1) 1 x))=
          ket (padZero (w+w+1) 1 (Aux_w54_arith.ltRegFn w x)) := by sorry
