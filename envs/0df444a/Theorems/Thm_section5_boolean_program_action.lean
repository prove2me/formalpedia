-- Prove2me | Theorems.Thm_section5_boolean_program_action
-- name    : section5_boolean_program_action
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:18.147345+00:00
-- url     : https://prove2.me/theorems/fef92684-3c2d-455f-9501-1a8e3ab687e1
-- title:
--   Exact action of a compiled Boolean instruction list
-- statement:
--   Let $m\in\mathbb N$, and let $P$ be a finite list of Boolean instructions on $m$ wires. Each instruction has an AND, OR, or NOT operation, two source wires distinct from its target, and updates the target by XOR with the operation value. Let $\operatorname{eval}(P,x)$ execute these updates in list order, and let $C(P)$ be the concatenation of their specified reversible circuits. For every basis string $x$,
--
--   $$U_{C(P)}|x\rangle=|\operatorname{eval}(P,x)\rangle.$$
--
--   This lifts the elementary gate semantics to complete finite Boolean programs.
-- source:
--   Original Boolean-program compilation auxiliary result supporting Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Formalization: Solutions/Section5ReversibleBooleanCompiler.lean, lines 288–295.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_boolean_gate_action
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_boolean_program_action {m : ℕ} (l : List (Section5BooleanInstruction m)) (x : Qubits m) :
    act (section5_compile_boolean_program l).unitary (ket x)=ket (section5_eval_boolean_program l x) := by sorry
