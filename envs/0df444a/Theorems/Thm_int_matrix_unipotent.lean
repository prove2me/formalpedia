-- Prove2me | Theorems.Thm_int_matrix_unipotent
-- name    : int_matrix_unipotent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:29:45.789625+00:00
-- url     : https://prove2.me/theorems/e575da99-f48d-4d63-9dea-451ffb7b6de5
-- title:
--   int_matrix_unipotent: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (with `open scoped Finset`, `open scoped Pointwise`):
--
--   ```lean
--   lemma int_matrix_unipotent {d: ℕ} (hd: 0 < d) (n: ℕ) (hn: 0 < n) (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1): ∃ m, (A.val^(n * KroneckerPow A eigen_one_complex) - 1)^m = 0
--   ```
--
--   **Definitions.** The statement is written with `KroneckerPow` (definitions bundle `OAIQ093D001` of this split).
--
--   **Used by.** The proof of `GeneratesNS.theorem_3_1` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ093D001

section

attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open scoped Finset
open scoped Pointwise

lemma int_matrix_unipotent {d: ℕ} (hd: 0 < d) (n: ℕ) (hn: 0 < n) (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1): ∃ m, (A.val^(n * KroneckerPow A eigen_one_complex) - 1)^m = 0 := by
  sorry

open scoped Pointwise Finset
end
