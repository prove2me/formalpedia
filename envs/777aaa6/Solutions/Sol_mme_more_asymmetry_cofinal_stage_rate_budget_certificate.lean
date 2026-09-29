-- Prove2me | solution 1 for mme_more_asymmetry_cofinal_stage_rate_budget_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T18:15:54.935867+00:00
-- url     : https://prove2.me/submissions/dc552a91-2378-43ea-9168-e6be7611b500
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3

open MME MME.HashExtraction MME.RecursiveYZ.Certificate Filter

set_option autoImplicit false

theorem solution :
    ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j)) (V : ℝ) (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ j, (A n j).Budget) ∧
        (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
          (D n).rate ((3952233 : ℝ) / 5000000) := by
  obtain ⟨D, A, V, error, hV, hpower, herror, hfinite⟩ :=
    mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3 (K := ℚ)
  refine ⟨D, A, V, error, hV, hpower, herror, ?_⟩
  filter_upwards [hfinite] with n hn
  rcases hn with
    ⟨hraw, localA, localB, localC, hfactor_template,
      hprod_a, hprod_b, hprod_c, hcopy, hbudget, hrate⟩
  exact ⟨hbudget, hrate⟩
