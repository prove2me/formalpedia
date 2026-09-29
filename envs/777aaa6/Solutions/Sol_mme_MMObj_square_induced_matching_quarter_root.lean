-- Prove2me | solution 1 for mme_MMObj_square_induced_matching_quarter_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:29:51.548293+00:00
-- url     : https://prove2.me/submissions/80c22e9e-10f9-4332-918d-bbc3115c7761

import Theorems.Thm_mme_MM_support_behrend_induced_matching
import Theorems.Thm_mme_MMObj_restrict_scalar_bigAdd_of_induced_matching
import Theorems.Thm_mme_MM_induced_matching_quarter_root_absorption

open MME BigOperators Filter Topology

universe u

theorem solution
    {K : Type u} [Field K] :
    ∀ᶠ N : ℕ in atTop,
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      ∀ H : ℕ, 0 < H → H ≤ 4 ^ N →
        ∃ k : ℕ,
          TensorObj.Restrict
            (TensorObj.bigAdd (fun _ : Fin k => MMObj K 1 1 1))
            (MMObj K H H H) ∧
          ((H : ℝ) ^ 2) * Real.exp (-((N : ℝ) * loss)) ≤ (k : ℝ) := by
  filter_upwards [mme_MM_induced_matching_quarter_root_absorption] with N hN
  dsimp only at hN ⊢
  intro H hH hHbound
  obtain ⟨E, hx, hy, hz, hinduced, hcard⟩ :=
    mme_MM_support_behrend_induced_matching H hH
  refine ⟨E.card, ?_, ?_⟩
  · exact mme_MMObj_restrict_scalar_bigAdd_of_induced_matching
      H E hx hy hz hinduced
  · exact (hN H hH hHbound).trans hcard
