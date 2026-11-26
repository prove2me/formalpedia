-- Prove2me | Theorems.Thm_section5_swap_gate_action
-- name    : section5_swap_gate_action
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:58.294735+00:00
-- url     : https://prove2.me/theorems/ffbfa99a-24e1-4053-b74e-d46686d5da26
-- title:
--   Basis-state action of an embedded swap gate
-- statement:
--   Let $i,j$ be distinct wire indices in an $m$-wire register and let $x\in\{0,1\}^m$. The swap gate embedded on wires $(i,j)$ satisfies
--
--   $$
--   U_{\mathrm{swap}(i,j)}|x\rangle=|x\circ(i\ j)\rangle,
--   $$
--
--   where $(i\ j)$ is the transposition of the two indices.
--
--   This gives the exact computational basis permutation used in wire-routing circuits.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5Routing.lean, section5_swap_gate_action, lines 67–112.

import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5Routing
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_swap_gate_action {m : ℕ} (i j : Fin m) (h : i ≠ j) (x : Qubits m) :
    act (embedOp (section5_swap_gate i j h).gate.mat (section5_swap_gate i j h).wires) (ket x) =
      ket (x ∘ Equiv.swap i j) := by sorry
