-- Prove2me | Theorems.Thm_section5_weighted_accumulator_circuit
-- name    : section5_weighted_accumulator_circuit
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:41.15174+00:00
-- url     : https://prove2.me/theorems/b9593506-e3e7-4a9b-9d59-b62ad75bbacb
-- title:
--   Reversible weighted bit accumulator
-- statement:
--   Let p be an injective w-bit accumulator in m wires, let a disjoint (w+1)-bit workspace be given, and let L be a list of control wires and natural weights, with every control outside both registers. A reversible circuit maps every basis string with zero workspace to the weighted-update string, adding each enabled weight to p modulo 2^w and restoring the other wires. Its gate count satisfies $$|C|\le16w|L|.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5WeightedAccumulator.lean, lines 35–41. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

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
import Definitions.Def_Section5Verified_Section5EmbeddedClassicalArithmetic
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Definitions.Def_Section5Verified_Section5WeightedAccumulator
import Mathlib
import Theorems.Thm_Aux_w54_arith_ctrlAddConstInPlaceCircuit_implements
import Theorems.Thm_section5_controlled_add_update
import Theorems.Thm_section5_embed_reversible_clean_permutation
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_weighted_accumulator_circuit {m w : ℕ}
    (p : Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m)
    (hpa : ∀ i j, p i ≠ anc j) (ops : List (Fin m × ℕ))
    (hctrl : ∀ a ∈ ops, (∀ i, a.1 ≠ p i) ∧ (∀ j, a.1 ≠ anc j)) :
    ∃ c : Circuit gatesRev m, c.size ≤ 16*w*ops.length ∧
      ∀ z : Qubits m, (∀ j, z (anc j)=false) →
        act c.unitary (ket z)=ket (section5_weighted_eval p ops z) := by sorry
