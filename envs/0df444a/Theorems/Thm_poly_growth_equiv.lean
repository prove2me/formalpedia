-- Prove2me | Theorems.Thm_poly_growth_equiv
-- name    : poly_growth_equiv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:09:42.75259+00:00
-- url     : https://prove2.me/theorems/14019573-34c3-46f9-9ea7-1f798e7ea11c
-- title:
--   poly_growth_equiv: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (with `open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace`, `open Subgroup Pointwise Finset`, `open scoped Pointwise Finset`, `open scoped commutatorElement IsMulCommutative`):
--
--   ```lean
--   lemma poly_growth_equiv {G: Type*} [DecidableEq G] [Group G] (a d: ℕ)
--     (a_pos: 0 < a)
--     (S S': Finset G)
--     (S_symm: S = S⁻¹)
--     (S_one: 1 ∈ S)
--     (S_generates: Subgroup.closure (S : Set G) = ⊤)
--     (s_poly: ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d):
--     ∃ b: ℕ, 1 ≤ b ∧ ∀ n ≥ 1, #(S' ^ n) ≤ b * n^d
--   ```
--
--   **Used by.** The proofs of `GeneratesNS.theorem_3_1`, `GeneratesNS.three_two_kernel_poly_growth`, `HnEpsData.central_trivial_virtually_abelian` and `compact_lie_virtually_abelian` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

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

lemma poly_growth_equiv {G: Type*} [DecidableEq G] [Group G] (a d: ℕ)
  (a_pos: 0 < a)
  (S S': Finset G)
  (S_symm: S = S⁻¹)
  (S_one: 1 ∈ S)
  (S_generates: Subgroup.closure (S : Set G) = ⊤)
  (s_poly: ∀ n ≥ 1, #(S ^ n) ≤ a * n ^ d):
  ∃ b: ℕ, 1 ≤ b ∧ ∀ n ≥ 1, #(S' ^ n) ≤ b * n^d := by
  sorry

end
