-- Prove2me | Theorems.Thm_section5_discrete_position_evolution
-- name    : section5_discrete_position_evolution
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:59.510052+00:00
-- url     : https://prove2.me/theorems/1da7fad0-fa44-4a4e-bf8b-2536d833deec
-- title:
--   Exact discrete position-square phase circuit
-- statement:
--   Let $q\ge1$ be a bit precision and let $t\in\mathbb R$. For a $q$-bit string $z$, write $N(z)$ for its most-significant-bit-first unsigned value and put $x_z=(N(z)-2^{q-1})\sqrt{4\pi/2^q}$. There exists a circuit $C$ of arbitrary one- and two-qubit gates on these $q$ qubits such that
--
--   $$|C|=q^2+q+1,\qquad U_C=\operatorname{diag}_{z}\big(e^{itx_z^2}\big).$$
--
--   The circuit realizes the centered discrete position-square evolution exactly, with a quadratic gate count and no additional wires.
-- source:
--   Original exact circuit specialization of Jain, Iyer, Somma, Bao and Jordan, Efficient Quantum Hermite Transform, arXiv:2510.04929, Section 3.1, as credited in the source; used for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1. Formalization: Solutions/Section5QuadraticPhase.lean, lines 266–284.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
import Theorems.Thm_section5_embed_diagonal
import Theorems.Thm_section5_linear_phase_unitary
import Theorems.Thm_section5_phase_list_unitary
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_discrete_position_evolution (q : ℕ) (hq : 0 < q) (t : ℝ) :
    ∃ circ : Circuit gates12 q, circ.size = q^2+q+1 ∧
      circ.unitary = Matrix.diagonal (fun z =>
        section5_phase (t * QuantumLTF.Example.scalarGrid z ^ 2)) := by sorry
