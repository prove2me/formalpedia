-- Prove2me | Theorems.Thm_compact_lie_virtually_abelian
-- name    : compact_lie_virtually_abelian
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:28:00.451202+00:00
-- url     : https://prove2.me/theorems/6ee238f1-a520-4c01-a813-ba66d1b002c9
-- title:
--   compact_lie_virtually_abelian: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (with `open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace`, `open Subgroup Pointwise Finset`, `open scoped Pointwise Finset`, `open scoped commutatorElement IsMulCommutative`):
--
--   ```lean
--   lemma compact_lie_virtually_abelian (n : ℕ) (hn : n ≠ 0) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (G_FG : G.FG)
--     (S_data: SPolyData G): ∃ N : Subgroup G, IsMulCommutative N ∧ N.FiniteIndex
--   ```
--
--   **Definitions.** The statement is written with `SPolyData` (definitions bundle `OAIQ093D001` of this split).
--
--   **Used by.** The proof of `GeneratesNS.exists_theorem_3_1_input` of this split imports it.
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

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace

set_option linter.style.longLine false
set_option linter.style.commandStart false

open Subgroup Pointwise Finset
open scoped Pointwise Finset
open scoped commutatorElement IsMulCommutative

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 2000000 in
lemma compact_lie_virtually_abelian (n : ℕ) (hn : n ≠ 0) (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (G_FG : G.FG)
  (S_data: SPolyData G): ∃ N : Subgroup G, IsMulCommutative N ∧ N.FiniteIndex := by
  sorry
end
