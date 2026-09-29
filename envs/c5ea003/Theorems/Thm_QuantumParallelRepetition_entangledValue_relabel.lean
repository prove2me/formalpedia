-- Prove2me | Theorems.Thm_QuantumParallelRepetition_entangledValue_relabel
-- name    : QuantumParallelRepetition.entangledValue_relabel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T02:08:59.101485+00:00
-- url     : https://prove2.me/theorems/4f4a3a06-330d-46dc-a217-1ce590dadc1b
-- title:
--   Relabelled games have equal entangled value
-- statement:
--   Two games related by a relabelling of their question and answer alphabets have the same entangled value,
--
--   $$\omega^*(H) = \omega^*(G).$$
--
--   The entangled value is the supremum of the winning probabilities over all finite-dimensional entangled strategies, so it suffices that the two games realise the *same set* of winning probabilities. Transport along the equivalence and along its inverse exhibits each achievable value of one game as an achievable value of the other.
-- source:
--   Prove2me bridge for openai/ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs — universe transport, not part of the upstream development (which states parallel repetition for alphabets in `Type` only).

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_alphabet_relabelling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators
open QuantumParallelRepetition

variable {X Y A B X' Y' A' B' : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']

theorem QuantumParallelRepetition.entangledValue_relabel
    {G : Game X Y A B} {H : Game X' Y' A' B'}
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B')
    (hw : ∀ x y, H.questionWeight (eX x) (eY y) = G.questionWeight x y)
    (hp : ∀ x y a b, H.predicate (eX x) (eY y) (eA a) (eB b) = G.predicate x y a b) :
    entangledValue H = entangledValue G := by sorry
