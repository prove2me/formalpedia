-- Prove2me | Theorems.Thm_section5_embed_classical_gate_action
-- name    : section5_embed_classical_gate_action
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:46:38.489821+00:00
-- url     : https://prove2.me/theorems/ac143598-a3b2-4643-b94a-23c6824f7a0d
-- title:
--   Basis-state action of an embedded classical gate
-- statement:
--   Let $e$ inject $k$ selected wires into an $m$-wire register. Let $f:\{0,1\}^k\to\{0,1\}^k$ and let $M$ be the matrix with entries $M_{y,z}=\mathbf1_{y=f(z)}$. For any full bit string $x$, let $x[e\leftarrow v]$ replace its selected wire values by $v$ and preserve the other wires. Then
--
--   $$
--   \operatorname{Embed}_e(M)|x\rangle=|x[e\leftarrow f(x\circ e)]\rangle.
--   $$
--
--   This translates the matrix embedding of a classical operation into an explicit update of selected wires.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5ReversibleBooleanCompiler.lean, section5_embed_classical_gate_action, lines 29–59.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_embed_classical_gate_action {k m : ℕ} (e : Fin k ↪ Fin m)
    (M : Matrix (Qubits k) (Qubits k) ℂ) (f : Qubits k → Qubits k)
    (hM : ∀ y z, M y z=if y=f z then 1 else 0) (x : Qubits m) :
    act (embedOp M e) (ket x)=ket (section5_replace_wires e x (f (x ∘ e))) := by sorry
