-- Prove2me | Theorems.Thm_QuantumParallelRepetition_Strategy_winProbability_relabel
-- name    : QuantumParallelRepetition.Strategy.winProbability_relabel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T02:07:46.6382+00:00
-- url     : https://prove2.me/theorems/b873c5b0-5f8a-4826-b25c-121001a3e659
-- title:
--   Relabelling preserves the winning probability
-- statement:
--   If a relabelling identifies two games — the target game assigns each relabelled question pair the weight the source game gave the original pair, and accepts a relabelled answer pair exactly when the source game accepted the original — then the relabelled strategy wins the target game with exactly the probability the original strategy wins the source game:
--
--   $$\omega(S') = \omega(S).$$
--
--   The hypotheses are stated pointwise, in the direction of the equivalences, so the same lemma serves both inclusions when one compares the two games' strategy sets.
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

theorem QuantumParallelRepetition.Strategy.winProbability_relabel
    {G : Game X Y A B} {H : Game X' Y' A' B'}
    (S : Strategy G) (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B')
    (hw : ∀ x y, H.questionWeight (eX x) (eY y) = G.questionWeight x y)
    (hp : ∀ x y a b, H.predicate (eX x) (eY y) (eA a) (eB b) = G.predicate x y a b) :
    (S.relabel (H := H) eX eY eA eB).winProbability = S.winProbability := by sorry
