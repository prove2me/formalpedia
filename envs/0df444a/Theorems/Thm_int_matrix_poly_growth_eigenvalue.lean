-- Prove2me | Theorems.Thm_int_matrix_poly_growth_eigenvalue
-- name    : int_matrix_poly_growth_eigenvalue
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:08:15.502555+00:00
-- url     : https://prove2.me/theorems/49dc9828-cdf6-4538-ae82-55c13e590778
-- title:
--   int_matrix_poly_growth_eigenvalue: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (with `open scoped Finset`, `open scoped Pointwise`):
--
--   ```lean
--   lemma int_matrix_poly_growth_eigenvalue {d: ℕ} [NeZero d] (A: (Matrix (Fin d) (Fin d) ℤ)ˣ)
--     (h_poly: ∀ k: ℂ, 1 < ‖k‖ → ∀ v: (Fin d) → ℤ, ∃ a b N_2: ℕ, (0 < a) ∧ ((Nat.ceil (Real.logb ‖k‖ 3)) < N_2) ∧ (4 * ↑b + Real.log ↑a < (Real.log 2) * (N_2 - (Nat.ceil (Real.logb ‖k‖ 3)))^((1 : ℝ) / 2)) ∧ #((Finset.image (fun a => a.sum (fun b => ((((A.val)^((Nat.ceil (Real.logb ‖k‖ 3)))))^b.val).mulVec (v))) ((Finset.Ico (Nat.ceil (Real.logb ‖k‖ 3)) N_2)).attach.powerset)) ≤ a * (N_2 - (Nat.ceil (Real.logb ‖k‖ 3)))^(2*b)):
--     ∀ k : Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin', ‖k.val‖ = 1
--   ```
--
--   **Used by.** The proof of `GeneratesNS.theorem_3_1` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open scoped Finset
open scoped Pointwise

lemma int_matrix_poly_growth_eigenvalue {d: ℕ} [NeZero d] (A: (Matrix (Fin d) (Fin d) ℤ)ˣ)
  (h_poly: ∀ k: ℂ, 1 < ‖k‖ → ∀ v: (Fin d) → ℤ, ∃ a b N_2: ℕ, (0 < a) ∧ ((Nat.ceil (Real.logb ‖k‖ 3)) < N_2) ∧ (4 * ↑b + Real.log ↑a < (Real.log 2) * (N_2 - (Nat.ceil (Real.logb ‖k‖ 3)))^((1 : ℝ) / 2)) ∧ #((Finset.image (fun a => a.sum (fun b => ((((A.val)^((Nat.ceil (Real.logb ‖k‖ 3)))))^b.val).mulVec (v))) ((Finset.Ico (Nat.ceil (Real.logb ‖k‖ 3)) N_2)).attach.powerset)) ≤ a * (N_2 - (Nat.ceil (Real.logb ‖k‖ 3)))^(2*b)):
  ∀ k : Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin', ‖k.val‖ = 1 := by
  sorry

open scoped Pointwise Finset
end
