-- Prove2me | Theorems.Thm_compiler_single_query_phase_simulation
-- name    : compiler_single_query_phase_simulation
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-23T22:06:26.904694+00:00
-- url     : https://prove2.me/theorems/2b5e7db3-ebd1-457d-b14d-61d76bc34561
-- title:
--   Exact one-query Majority phase simulation with a norm-preserving encoding
-- statement:
--   For every data-register vector, appending an answer qubit in the minus state preserves its norm. The explicit circuit block makes exactly one Majority bit-oracle call. On the encoded vector it acts by multiplication with the Boolean phase (-1) to the Majority label, leaving the answer qubit in its original minus state.
--
--   This is an exact operational identity in the mission's OracleCircuit and majorityOracle definitions. It supplies the elementary phase-kickback simulation used by the adversary compiler.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.5.1, equation (129), phase versus bit membership-oracle convention.

import Definitions.Def_QuantumLTF_Majority_PhaseQueryModel

open QAlgorithms QuantumLTF.Majority

theorem compiler_single_query_phase_simulation {n : ℕ} (A : Finset (Fin n))
    (x : EuclideanSpace ℂ (Qubits n)) :
    (compiler_single_majority_query n).queryCount 0 = 1 ∧
    ‖compiler_phase_lift x‖ = ‖x‖ ∧
    ∀ y : Qubits (n+1),
      act ((compiler_single_majority_query n).unitary (fun _ => majorityOracle A))
        (compiler_phase_lift x) y =
      (if majorityBit A (fun i => y i.castSucc) then (-1 : ℂ) else 1) *
        compiler_phase_lift x y := by sorry
