-- Prove2me | Theorems.Thm_section5_replace_wires_eq_update
-- name    : section5_replace_wires_eq_update
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:19.003877+00:00
-- url     : https://prove2.me/theorems/d1d798c3-48f9-40ef-b4f0-fba55ff38de9
-- title:
--   A selected-register replacement reduces to a single-wire update
-- statement:
--   Let $e$ inject $k$ selected wires into an $m$-wire register, let $x\in\{0,1\}^m$, and let $v\in\{0,1\}^k$. Fix $j<k$ and suppose $v_i=x_{e(i)}$ for every $i\ne j$. If $x[e\leftarrow v]$ replaces the selected register while preserving other wires, then
--
--   $$
--   x[e\leftarrow v]=x[e(j)\leftarrow v_j].
--   $$
--
--   This identifies a register replacement that changes at most one coordinate with the corresponding single-wire update.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5ReversibleBooleanCompiler.lean, section5_replace_wires_eq_update, lines 131–146.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_replace_wires_eq_update {k m : ℕ} (e : Fin k ↪ Fin m)
    (x : Qubits m) (v : Qubits k) (j : Fin k)
    (hkeep : ∀ i, i ≠ j → v i=x (e i)) :
    section5_replace_wires e x v=Function.update x (e j) (v j) := by sorry
