-- Prove2me | Theorems.Thm_mme_Ctensor_one_half_family_to_six_finite_rate_of_capacity
-- name    : mme_Ctensor_one_half_family_to_six_finite_rate_of_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T13:50:53.443122+00:00
-- url     : https://prove2.me/theorems/4dec8144-8632-4dbe-b3f0-552a7923b736
-- title:
--   A pointwise C-tensor capacity bound squares to a six-symmetric finite extraction
-- statement:
--   For any nonnegative real base R, a one-half C-tensor family certificate whose finite capacity dominates R^(2N) up to exp(-C sqrt(N+1)) yields a finite matrix-multiplication extraction from the six-symmetrized source with weight at least R^(4N) exp(-(2C+400) sqrt(N+1)).
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Appendix A finite C-tensor extraction; post-cyclic completion and Cartesian doubling.

import Mathlib
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_Ctensor_one_half_family_to_six_finite_rate_of_capacity
    {K : Type u} [Field K]
    {T : TensorObj K 3}
    (tau C R : ℝ) (N A H volume : ℕ)
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (hR : 0 ≤ R) (hH : 0 < H) (hHbound : H ≤ 4 ^ N)
    (hrate :
      R ^ (2 * N) *
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((volume ^ 3 : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization T) ∧
      R ^ (4 * N) *
          Real.exp (-(2 * C + 400) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  sorry
