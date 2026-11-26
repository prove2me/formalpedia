-- Prove2me | Theorems.Thm_section5_reversible_circuit_permutation
-- name    : section5_reversible_circuit_permutation
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:33.7698+00:00
-- url     : https://prove2.me/theorems/7b4cd2c0-dd44-424e-b61e-76fccb94c70b
-- title:
--   Reversible circuits permute computational basis states
-- statement:
--   For every reversible m-wire circuit C, there exists a permutation F of the m-bit basis strings such that $$\forall x:\quad U_C|x\rangle=|F(x)\rangle.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ReversibleCircuitPermutation.lean, lines 53–54.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Definitions.Def_Section5Verified_Section5ReversibleCircuitPermutation
import Mathlib
import Theorems.Thm_section5_embed_classical_gate_action
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_reversible_circuit_permutation {m : ℕ} (c : Circuit gatesRev m) :
    ∃ f : Equiv.Perm (Qubits m), ∀ x, act c.unitary (ket x)=ket (f x) := by sorry
