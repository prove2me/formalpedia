-- Prove2me | solution 1 for QuantumParallelRepetition.entangledValue_eq_fin
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-12T02:12:07.635937+00:00
-- url     : https://prove2.me/submissions/794ec1c7-3843-4065-adc5-dde512744306

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_alphabet_relabelling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Theorems.Thm_QuantumParallelRepetition_entangledValue_relabel

open scoped BigOperators
open QuantumParallelRepetition

variable {X Y A B X' Y' A' B' : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']

theorem solution (G : Game X Y A B) :
    entangledValue G
      = entangledValue (G.relabel (Fintype.equivFin X) (Fintype.equivFin Y)
          (Fintype.equivFin A) (Fintype.equivFin B)) := by
  exact (entangledValue_relabel (Fintype.equivFin X) (Fintype.equivFin Y)
    (Fintype.equivFin A) (Fintype.equivFin B)
    (fun _ _ => by simp) (fun _ _ _ _ => by simp)).symm
