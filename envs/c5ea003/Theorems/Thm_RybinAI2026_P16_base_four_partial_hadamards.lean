-- Prove2me | Theorems.Thm_RybinAI2026_P16_base_four_partial_hadamards
-- name    : RybinAI2026.P16.base_four_partial_hadamards
-- status  : Open
-- author  : @WillR
-- created : 2026-09-06T16:48:01.936704+00:00
-- url     : https://prove2.me/theorems/f54b65c0-81f8-4f4e-bef6-dc65274fb838
-- title:
--   Four-family base construction for the dimension-six MUB frontier
-- statement:
--   Construct a four-member family of six-by-five complex partial Hadamard matrices satisfying the self-Gram, entry-modulus, and pairwise unbiasedness equations. This is a reusable intermediate family in the dimension-six MUB decomposition.
-- source:
--   Brierley and Weigert, Maximal Sets of Mutually Unbiased Quantum States in Dimension Six, arXiv:0808.1614v1, Section 2.1; decomposition of the Prove2Me P16 frontier.

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
open Matrix
open scoped ComplexConjugate Matrix

theorem RybinAI2026.P16.base_four_partial_hadamards :
    ∃ A : Fin 4 → Matrix (Fin 6) (Fin 5) ℂ,
      (∀ r, (A r)ᴴ * A r = (6 : ℂ) • (1 : Matrix (Fin 5) (Fin 5) ℂ)) ∧
      (∀ r, ∀ i j : Fin 5, Complex.normSq (A r i.castSucc j) = 1) ∧
      (∀ r s, r < s → ∀ i j : Fin 5,
        Complex.normSq (((A r)ᴴ * A s) i j) = 6) := by sorry
