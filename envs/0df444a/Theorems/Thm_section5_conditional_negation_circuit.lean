-- Prove2me | Theorems.Thm_section5_conditional_negation_circuit
-- name    : section5_conditional_negation_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:29.799731+00:00
-- url     : https://prove2.me/theorems/6b6df01e-dd25-4171-acdb-9f61058422ed
-- title:
--   Clean conditional modular negation
-- statement:
--   Let w>0, let p be a w-bit register, let c be a control outside p, and let a disjoint (w+1)-bit workspace avoid c. There is a reversible circuit, acting on basis strings with zero workspace, which conditionally negates p modulo 2^w, preserves other wires and restores the workspace: $$p'=(-1)^c p\pmod{2^w},\qquad |C|\le17w.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ConditionalNegation.lean, lines 88–94. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5ConditionalNegation
import Definitions.Def_Section5Verified_Section5EmbeddedClassicalArithmetic
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_Aux_w54_arith_bitsToNatLSB_add_two_pow_rev
import Theorems.Thm_Aux_w54_arith_ctrlAddConstInPlaceCircuit_implements
import Theorems.Thm_Aux_w54_arith_ctrlConstXorCircuit_implements
import Theorems.Thm_section5_controlled_add_update
import Theorems.Thm_section5_embed_reversible_clean_permutation
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_conditional_negation_circuit {m w : ℕ} (hw : 0 < w) (ctrl : Fin m)
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hcp : ∀ i, ctrl ≠ p i) (hca : ∀ j, ctrl ≠ anc j)
    (hpa : ∀ i j, p i ≠ anc j) :
    ∃ c : Circuit gatesRev m, c.size ≤ 17*w ∧
      ∀ z : Qubits m, (∀ j, z (anc j)=false) →
        act c.unitary (ket z)=ket (section5_conditional_negate ctrl p z) := by sorry
