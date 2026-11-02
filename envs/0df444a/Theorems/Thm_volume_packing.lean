-- Prove2me | Theorems.Thm_volume_packing
-- name    : volume_packing
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:29:28.960024+00:00
-- url     : https://prove2.me/theorems/c31def96-253d-48ff-8a1b-5f3aa1308c18
-- title:
--   volume_packing: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (with `open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace`, `open Subgroup Pointwise Finset`, `open scoped Pointwise Finset`, `open scoped commutatorElement IsMulCommutative`, `open Pointwise in`):
--
--   ```lean
--   lemma volume_packing (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
--       ∃ C : ℝ, ∀ (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)), (G' n ε G).FiniteIndex ∧ (G' n ε G).index ≤ C
--   ```
--
--   **Definitions.** The statement is written with `G'` (definitions bundle `OAIQ093D000` of this split).
--
--   **Used by.** The proof of `compact_lie_virtually_abelian` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ093D000

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant
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
set_option maxHeartbeats 500000 in
open Pointwise in
lemma volume_packing (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (G : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)), (G' n ε G).FiniteIndex ∧ (G' n ε G).index ≤ C := by
  sorry

attribute [-simp] MeasureTheory.Measure.inv_eq_self

attribute [local implicit_reducible] FreshInnerProduct
end
