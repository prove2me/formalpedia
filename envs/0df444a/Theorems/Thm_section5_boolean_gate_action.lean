-- Prove2me | Theorems.Thm_section5_boolean_gate_action
-- name    : section5_boolean_gate_action
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:01:59.175554+00:00
-- url     : https://prove2.me/theorems/997215a0-7a33-4951-bbea-4d358ad57c9f
-- title:
--   Exact reversible action of a Boolean gate
-- statement:
--   Let $m\in\mathbb N$, let $\mathrm{op}$ be AND, OR, or NOT, and choose source wires $a,b$ and a target wire $t$ in an $m$-qubit register with $a\ne t$ and $b\ne t$; the two sources may coincide. Interpret NOT as acting on its first input. For every basis string $x$, the specified NOT/CNOT/Toffoli circuit $C_{\mathrm{op},a,b,t}$ satisfies
--
--   $$U_C|x\rangle=|x[t\leftarrow x_t\mathbin{\oplus}\mathrm{op}(x_a,x_b)]\rangle.$$
--
--   This establishes the exact XOR-into-target semantics of the elementary reversible Boolean compilation step.
-- source:
--   Original Boolean-gate compilation auxiliary result supporting the Section 5 classical postprocessing of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. Formalization: Solutions/Section5ReversibleBooleanCompiler.lean, lines 215–254.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_embed_classical_gate_action
import Theorems.Thm_section5_replace_wires_eq_update
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_boolean_gate_action {m : ℕ} (op : BoolOp) (a b t : Fin m)
    (hat : a ≠ t) (hbt : b ≠ t) (x : Qubits m) :
    act (section5_boolean_gate_circuit op a b t hat hbt).unitary (ket x)=
      ket (Function.update x t (xor (x t) (section5_bool_value op (x a) (x b)))) := by sorry
