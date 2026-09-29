-- Prove2me | solution 1 for Bridges.AlgebraMachineLearning.wordsOfLength_length_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T20:38:33.831885+00:00
-- url     : https://prove2.me/submissions/c5c1a644-8991-4853-802c-36b74ef8edcc

import Mathlib
import Definitions.Def_Bridges_PosetTheory_CoalgebraicNeuralMyhillNerode
open Bridges.AlgebraMachineLearning in
theorem solution {α : Type*} (A : List α) (n : ℕ) : (wordsOfLength A n).length = A.length ^ n := by
  induction n with
  | zero => simp [wordsOfLength]
  | succ n ih =>
    -- each word of length `n` extends by every letter of `A`
    simp only [wordsOfLength, List.length_flatMap, List.length_map]
    rw [List.map_const', List.sum_replicate, ih, smul_eq_mul, pow_succ]
