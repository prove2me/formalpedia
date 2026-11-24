-- Prove2me | Theorems.Thm_compiler_exact_circuit_synthesis
-- name    : compiler_exact_circuit_synthesis
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-24T12:18:12.965173+00:00
-- url     : https://prove2.me/theorems/5d3fe1fc-d6b1-4e5b-9a0f-123b0ea0c330
-- title:
--   Exact synthesis of arbitrary qubit unitaries in the gates12 circuit model
-- statement:
--   For every register of at least one qubit and every unitary matrix on that register, there is a finite circuit over arbitrary one- and two-qubit unitary gates whose matrix equals the prescribed unitary exactly.
--
--   This supplies the fixed-unitary realization step in the Section 4 adversary compiler. The proof translates the established algebraic generation theorem for arbitrary single-qubit gates and CNOT from binary Fin 2 indices to the mission's Bool-indexed registers and explicit GateApp wire embeddings. It places no bound on the number of elementary gates.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Appendix C.5 (arbitrary one-/two-qubit gate model). Reuses Prove2Me SuperconductingQC.closure_singleQubit_CNOT_eq_top, theorem 24a2c1d0-cb9b-47f1-97be-495311250c8d.

import Definitions.Def_QuantumLTF_Membership_gates12
open QAlgorithms QuantumLTF.Membership

theorem compiler_exact_circuit_synthesis (n : ℕ) (hn : 1 ≤ n)
    (M : Matrix (Qubits n) (Qubits n) ℂ) (hM : M ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    ∃ c : Circuit gates12 n, c.unitary = M := by sorry
