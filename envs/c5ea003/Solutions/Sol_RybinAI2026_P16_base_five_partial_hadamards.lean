-- Prove2me | solution 1 for RybinAI2026.P16.base_five_partial_hadamards
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-06T16:56:56.090149+00:00
-- url     : https://prove2.me/submissions/f8e6cd64-1ac5-49b8-9989-64ce60a09d6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Theorems.Thm_RybinAI2026_P16_base_four_partial_hadamards
import Theorems.Thm_RybinAI2026_P16_extend_four_to_five_partial_hadamards

open Matrix
open scoped ComplexConjugate Matrix

theorem solution :
    ∃ A : Fin 5 → Matrix (Fin 6) (Fin 5) ℂ,
      (∀ r, (A r)ᴴ * A r = (6 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ)) ∧
      (∀ r, ∀ i j : Fin 5, Complex.normSq (A r i.castSucc j) = 1) ∧
      (∀ r s, r < s → ∀ i j : Fin 5,
        Complex.normSq (((A r)ᴴ * A s) i j) = 6) := by
  obtain ⟨A, hA⟩ := RybinAI2026.P16.base_four_partial_hadamards
  exact RybinAI2026.P16.extend_four_to_five_partial_hadamards A hA
