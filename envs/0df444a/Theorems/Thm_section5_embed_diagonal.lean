-- Prove2me | Theorems.Thm_section5_embed_diagonal
-- name    : section5_embed_diagonal
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:48:30.611681+00:00
-- url     : https://prove2.me/theorems/50a1ecd7-52e0-45e9-9279-15b6bebd46ab
-- title:
--   Embedding a diagonal gate preserves diagonal structure
-- statement:
--   Let k,n be natural numbers, let v assign a complex number to each k-bit basis string, and let w inject the k gate wires into n global wires. The embedded operator is diagonal on the full basis and satisfies $$\operatorname{embed}(\operatorname{diag}(v),w)=\operatorname{diag}_{z\in\{0,1\}^n}(v(z\circ w)).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5QuadraticPhase.lean, lines 41–42.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_embed_diagonal {k n : ℕ} (v : Qubits k → ℂ) (w : Fin k ↪ Fin n) :
    embedOp (Matrix.diagonal v) w = Matrix.diagonal (fun z => v (z ∘ w)) := by sorry
