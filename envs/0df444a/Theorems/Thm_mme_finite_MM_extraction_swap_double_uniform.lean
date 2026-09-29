-- Prove2me | Theorems.Thm_mme_finite_MM_extraction_swap_double_uniform
-- name    : mme_finite_MM_extraction_swap_double_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:36:43.447126+00:00
-- url     : https://prove2.me/theorems/c56cf2ca-7c14-4a6b-8291-0ec8c5633664
-- title:
--   Quantitative uniform swap-and-double extraction
-- statement:
--   A uniform finite MM extraction from the cyclic symmetrization, with at least lower summands and common volume V, yields a finite extraction from the six-symmetrization with at least lower² summands and common volume V². It is obtained by tensoring the extraction with its first-two-mode swap and retaining all ordered pairs.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3; quantitative finite form of the six-symmetrization product.

import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_finite_MM_extraction_swap_double_uniform
    {K : Type u} [Field K] {T : TensorObj K 3} {k V : ℕ}
    (a b c : Fin k → ℕ) (lower : ℝ)
    (hlower : 0 ≤ lower) (hcount : lower ≤ (k : ℝ))
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
      (cyclicSymmetrization T))
    (hvolume : ∀ j, a j * b j * c j = V) :
    ∃ (q : ℕ) (A B C : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun r ↦ MMObj K (A r) (B r) (C r)))
        (sixSymmetrization T) ∧
      lower ^ (2 : ℕ) ≤ (q : ℝ) ∧
      (∀ r, A r * B r * C r = V ^ 2) := by
  sorry
