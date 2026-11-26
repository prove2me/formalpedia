-- Prove2me | Theorems.Thm_section5_phase_list_unitary
-- name    : section5_phase_list_unitary
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:30.57707+00:00
-- url     : https://prove2.me/theorems/04f2a472-9fd7-451f-8531-8e7c9d41c967
-- title:
--   A list of diagonal phase gates accumulates its phases
-- statement:
--   Let L be a finite list of indices, let g_i be one- or two-qubit gate applications on n wires, and let t_i(z) be real phases. Suppose every occurrence i in L has embedded matrix diag_z(exp(it_i(z))). Then the circuit formed by the ordered gate list has unitary $$U_C=\operatorname{diag}_z\exp\!\left(i\sum_{j\in L}t_j(z)\right).$$ The sum counts repeated list entries.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5QuadraticPhase.lean, lines 108–112.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_Section5Verified_Section5QuadraticPhase
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_phase_list_unitary {n : ℕ} {ι : Type*} (l : List ι)
    (g : ι → GateApp gates12 n) (t : ι → Qubits n → ℝ)
    (hg : ∀ i ∈ l, embedOp (g i).gate.mat (g i).wires =
      Matrix.diagonal (fun z => section5_phase (t i z))) :
    Circuit.unitary (l.map g) = Matrix.diagonal (fun z => section5_phase ((l.map (fun i => t i z)).sum)) := by sorry
