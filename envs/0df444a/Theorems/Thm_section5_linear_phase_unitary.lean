-- Prove2me | Theorems.Thm_section5_linear_phase_unitary
-- name    : section5_linear_phase_unitary
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:38.86084+00:00
-- url     : https://prove2.me/theorems/18b5ae59-f1ec-428f-a2ef-aaaa8e65cbd6
-- title:
--   Diagonal unitary of the linear phase circuit
-- statement:
--   Let $n\ge0$, let $a_0,\ldots,a_{n-1}\in\mathbb R$, and let $t\in\mathbb R$. The constructed $n$-wire linear phase circuit has unitary
--
--   $$
--   U=\operatorname{diag}\left(z\mapsto\exp\!\left(it\sum_{j=0}^{n-1}a_j z_j\right)\right),\qquad z\in\{0,1\}^n.
--   $$
--
--   This identifies the circuit's exact phase on every computational basis string.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5QuadraticPhase.lean, section5_linear_phase_unitary, lines 178–195.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_section5_embed_diagonal
import Theorems.Thm_section5_phase_list_unitary
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_linear_phase_unitary (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    (section5_linear_phase_circuit n a t).unitary =
      Matrix.diagonal (fun z => section5_phase (t*(∑ i : Fin n, if z i then a i else 0))) := by sorry
