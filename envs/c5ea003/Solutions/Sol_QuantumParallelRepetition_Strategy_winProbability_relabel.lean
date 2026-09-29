-- Prove2me | solution 1 for QuantumParallelRepetition.Strategy.winProbability_relabel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-12T02:07:55.629052+00:00
-- url     : https://prove2.me/submissions/729d85b8-5476-4a39-88ed-7d6576c04a94

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_alphabet_relabelling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Theorems.Thm_QuantumParallelRepetition_Strategy_outcomeProbability_relabel

open scoped BigOperators
open QuantumParallelRepetition

variable {X Y A B X' Y' A' B' : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']

theorem solution
    {G : Game X Y A B} {H : Game X' Y' A' B'}
    (S : Strategy G) (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B')
    (hw : ∀ x y, H.questionWeight (eX x) (eY y) = G.questionWeight x y)
    (hp : ∀ x y a b, H.predicate (eX x) (eY y) (eA a) (eB b) = G.predicate x y a b) :
    (S.relabel (H := H) eX eY eA eB).winProbability = S.winProbability := by
  classical
  have inner : ∀ (x : X) (y : Y),
      (∑ a' : A', ∑ b' : B',
        if H.predicate (eX x) (eY y) a' b' = true then
          (S.relabel (H := H) eX eY eA eB).outcomeProbability (eX x) (eY y) a' b' else 0)
        = ∑ a : A, ∑ b : B,
            if G.predicate x y a b = true then S.outcomeProbability x y a b else 0 := by
    intro x y
    refine (Fintype.sum_equiv eA _ _ fun a => ?_).symm
    refine Fintype.sum_equiv eB _ _ fun b => ?_
    rw [Strategy.outcomeProbability_relabel, hp x y a b]
    simp
  unfold Strategy.winProbability
  refine (Fintype.sum_equiv eX _ _ fun x => ?_).symm
  refine Fintype.sum_equiv eY _ _ fun y => ?_
  rw [hw x y, inner x y]
