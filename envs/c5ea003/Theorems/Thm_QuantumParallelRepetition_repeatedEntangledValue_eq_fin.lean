-- Prove2me | Theorems.Thm_QuantumParallelRepetition_repeatedEntangledValue_eq_fin
-- name    : QuantumParallelRepetition.repeatedEntangledValue_eq_fin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T02:13:10.191139+00:00
-- url     : https://prove2.me/theorems/ef2f2882-8ff9-4909-b878-8319a24fa6b2
-- title:
--   Repeated entangled value is computed by a game on Fin alphabets
-- statement:
--   The universe-lowering step, for every number of repetitions at once: the repeated entangled values of a finite game agree with those of its standard-finite relabelling,
--
--   $$\omega^*(G^n) = \omega^*\big((G')^n\big) \qquad \text{for all } n,$$
--
--   where $G'$ has alphabets $\mathrm{Fin}\,|X|$, $\mathrm{Fin}\,|Y|$, $\mathrm{Fin}\,|A|$, $\mathrm{Fin}\,|B|$ and therefore lives in `Type`.
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

theorem QuantumParallelRepetition.repeatedEntangledValue_eq_fin
    (G : Game X Y A B) (n : ℕ) :
    repeatedEntangledValue G n
      = repeatedEntangledValue (G.relabel (Fintype.equivFin X) (Fintype.equivFin Y)
          (Fintype.equivFin A) (Fintype.equivFin B)) n := by sorry
