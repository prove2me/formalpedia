-- Prove2me | Theorems.Thm_mul_aut_iterate
-- name    : mul_aut_iterate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:08:56.246539+00:00
-- url     : https://prove2.me/theorems/209c5fe8-78fc-42bb-87ce-e6734e603527
-- title:
--   mul_aut_iterate: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (with `open scoped commutatorElement IsMulCommutative Pointwise`):
--
--   ```lean
--   lemma mul_aut_iterate {G: Type*} [Group G] (f: MulAut G) (n: ℕ): f^[n] = ⇑(f ^ n)
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

set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

lemma mul_aut_iterate {G: Type*} [Group G] (f: MulAut G) (n: ℕ): f^[n] = ⇑(f ^ n) := by
  sorry
end
