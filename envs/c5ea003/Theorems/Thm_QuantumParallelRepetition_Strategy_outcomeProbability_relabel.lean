-- Prove2me | Theorems.Thm_QuantumParallelRepetition_Strategy_outcomeProbability_relabel
-- name    : QuantumParallelRepetition.Strategy.outcomeProbability_relabel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T02:06:09.299596+00:00
-- url     : https://prove2.me/theorems/fed01086-ec68-4b13-8b4c-2adee5fc3808
-- title:
--   Relabelling preserves outcome probabilities
-- statement:
--   Transporting a strategy along equivalences of the question and answer alphabets leaves every outcome probability unchanged, up to the induced renaming of the indices.
--
--   If $S$ is a strategy and $e_X, e_Y, e_A, e_B$ are equivalences of the alphabets, the relabelled strategy $S'$ answers question $x'$ by running $S$ on $e_X^{-1}(x')$ and renaming its answer, so
--
--   $$\Pr_{S'}[a',b' \mid x',y'] = \Pr_{S}[e_A^{-1}(a'), e_B^{-1}(b') \mid e_X^{-1}(x'), e_Y^{-1}(y')].$$
--
--   The two sides are definitionally equal: the relabelled strategy shares the state and the local systems of the original, and its measurement operators are the original ones composed with the renaming.
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

theorem QuantumParallelRepetition.Strategy.outcomeProbability_relabel
    {G : Game X Y A B} {H : Game X' Y' A' B'}
    (S : Strategy G) (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B')
    (x' : X') (y' : Y') (a' : A') (b' : B') :
    (S.relabel (H := H) eX eY eA eB).outcomeProbability x' y' a' b' =
      S.outcomeProbability (eX.symm x') (eY.symm y') (eA.symm a') (eB.symm b') := by sorry
