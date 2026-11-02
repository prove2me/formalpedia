-- Prove2me | Theorems.Thm_eigenspace_orthogonal
-- name    : eigenspace_orthogonal
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:06:54.511228+00:00
-- url     : https://prove2.me/theorems/3dbe8290-9a14-4aff-84f9-79b9f723765f
-- title:
--   eigenspace_orthogonal: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published:
--
--   ```lean
--   lemma eigenspace_orthogonal  {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] (f: Module.End ℂ A) (hf: IsStarNormal f) (j k: ℂ) (hjk: j ≠ k):
--       f.eigenspace k ⟂ f.eigenspace j
--   ```
--
--   **Used by.** The proof of `centralizer_iso` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

lemma eigenspace_orthogonal  {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] (f: Module.End ℂ A) (hf: IsStarNormal f) (j k: ℂ) (hjk: j ≠ k):
    f.eigenspace k ⟂ f.eigenspace j := by
  sorry
end
