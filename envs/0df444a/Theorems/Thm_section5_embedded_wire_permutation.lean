-- Prove2me | Theorems.Thm_section5_embedded_wire_permutation
-- name    : section5_embedded_wire_permutation
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:02:40.083799+00:00
-- url     : https://prove2.me/theorems/7780b697-04af-4f65-8940-fcce89a5e36c
-- title:
--   Linear-size permutation of an embedded wire block
-- statement:
--   Let $e:\{0,\ldots,p-1\}\hookrightarrow\{0,\ldots,m-1\}$ embed $p$ wires in an $m$-qubit register, and let $\sigma$ permute those $p$ wires. Extend $\sigma$ to the ambient wires through $e$, fixing every wire outside its image; call the extension $\widetilde\sigma$. There exists a circuit $C$ of one- and two-qubit gates satisfying
--
--   $$|C|\le p,\qquad U_C|x\rangle=|x\circ\widetilde\sigma\rangle\quad\text{for every }x\in\{0,1\}^m.$$
--
--   This implements an embedded wire permutation with a bound independent of the ambient register size.
-- source:
--   Original routing auxiliary result for the compaction step in Theorem 5.4 of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Formalization: Solutions/Section5Routing.lean, lines 166–174.

import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5Routing
import Mathlib
import Theorems.Thm_section5_swap_gate_action
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_embedded_wire_permutation {p m : ℕ} (e : Fin p ↪ Fin m)
    (σ : Equiv.Perm (Fin p)) :
    ∃ c : Circuit gates12 m, c.size ≤ p ∧
      ∀ x : Qubits m, act c.unitary (ket x) = ket (x ∘ σ.viaEmbedding e) := by sorry
