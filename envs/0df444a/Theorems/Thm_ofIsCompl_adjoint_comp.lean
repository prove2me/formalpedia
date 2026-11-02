-- Prove2me | Theorems.Thm_ofIsCompl_adjoint_comp
-- name    : ofIsCompl_adjoint_comp
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:09:23.448201+00:00
-- url     : https://prove2.me/theorems/41253d92-fd64-49ed-a64d-d41437ee7414
-- title:
--   ofIsCompl_adjoint_comp: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published:
--
--   ```lean
--   lemma ofIsCompl_adjoint_comp {P: Type*} [NormedAddCommGroup P] [CompleteSpace P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]  {p q : Submodule ℂ P} (h : IsCompl p q) (hpq: p ⟂ q) (φ : p →ₗ[ℂ] P) (ψ : q →ₗ[ℂ] P) (hφ: (LinearMap.adjoint φ) ∘ₗ φ = 1) (hφ_map: ∀ x: p, φ x ∈ p) (hψ: (LinearMap.adjoint ψ) ∘ₗ ψ = 1) (hψ_map: ∀ x: q, ψ x ∈ q):
--     (LinearMap.ofIsCompl h (φ) (ψ)).adjoint ∘ₗ(LinearMap.ofIsCompl h φ ψ) = 1
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

lemma ofIsCompl_adjoint_comp {P: Type*} [NormedAddCommGroup P] [CompleteSpace P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]  {p q : Submodule ℂ P} (h : IsCompl p q) (hpq: p ⟂ q) (φ : p →ₗ[ℂ] P) (ψ : q →ₗ[ℂ] P) (hφ: (LinearMap.adjoint φ) ∘ₗ φ = 1) (hφ_map: ∀ x: p, φ x ∈ p) (hψ: (LinearMap.adjoint ψ) ∘ₗ ψ = 1) (hψ_map: ∀ x: q, ψ x ∈ q):
  (LinearMap.ofIsCompl h (φ) (ψ)).adjoint ∘ₗ(LinearMap.ofIsCompl h φ ψ) = 1  := by
  sorry
end
