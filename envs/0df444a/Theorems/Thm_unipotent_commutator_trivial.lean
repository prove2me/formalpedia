-- Prove2me | Theorems.Thm_unipotent_commutator_trivial
-- name    : unipotent_commutator_trivial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T17:58:50.17012+00:00
-- url     : https://prove2.me/theorems/cf9a2be1-deb1-4594-b19a-f4d54da846a0
-- title:
--   unipotent_commutator_trivial: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (with `open scoped commutatorElement IsMulCommutative Pointwise`):
--
--   ```lean
--   lemma unipotent_commutator_trivial {G: Type*} [DecidableEq G] [Group G] (H: Subgroup G) {N': Subgroup H} [H_normal: H.Normal] [N'_char: N'.Characteristic] [N'_nilpotent: Group.IsNilpotent N'] (gamma_alpha: G) (gamma_not_n: ¬(gamma_alpha ∈ (Subgroup.map (Subgroup.subtype _) N'))) (m: ℕ)
--     (h_gamma_alpha: ∀ g ∈ N', iteratedCommutator g.val gamma_alpha m = 1)
--     (S: Finset H) (hS: Subgroup.closure S = N'):
--     Group.IsNilpotent (Subgroup.closure ((Finset.image (Subgroup.subtype _) S) ∪ {gamma_alpha}))
--   ```
--
--   **Definitions.** The statement is written with `iteratedCommutator` (definitions bundle `OAIQ093D005` of this split).
--
--   **Used by.** The proof of `GeneratesNS.theorem_3_1` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ093D005

section

attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

attribute [-simp] Subgroup.map_toSubmonoid Subgroup.coe_subtype in
lemma unipotent_commutator_trivial {G: Type*} [DecidableEq G] [Group G] (H: Subgroup G) {N': Subgroup H} [H_normal: H.Normal] [N'_char: N'.Characteristic] [N'_nilpotent: Group.IsNilpotent N'] (gamma_alpha: G) (gamma_not_n: ¬(gamma_alpha ∈ (Subgroup.map (Subgroup.subtype _) N'))) (m: ℕ)
  (h_gamma_alpha: ∀ g ∈ N', iteratedCommutator g.val gamma_alpha m = 1)
  (S: Finset H) (hS: Subgroup.closure S = N'):
  Group.IsNilpotent (Subgroup.closure ((Finset.image (Subgroup.subtype _) S) ∪ {gamma_alpha})) := by
  sorry
end
