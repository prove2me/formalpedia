-- Prove2me | solution 1 for mme_more_asymmetry_cofinal_repaired_template_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T16:22:52.838516+00:00
-- url     : https://prove2.me/submissions/a9a8f385-2b8d-4044-9a4f-c0efe0739cbd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_cofinal_stage_rate_budget_certificate
import Theorems.Thm_mme_more_asymmetry_finite_recursive_assembly
import Mathlib.Topology.Instances.Real.Lemmas

open MME MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] :
    ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j)) (V : ℝ) (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ j, (A n j).Budget) ∧
        RecursiveAssembly (D n) (A n) K ∧
        (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
          (D n).rate ((3952233 : ℝ) / 5000000) := by
  obtain ⟨D, A, V, error, hV, hpower, herror, hfinite⟩ :=
    mme_more_asymmetry_cofinal_stage_rate_budget_certificate
  refine ⟨D, A, V, error, hV, hpower, herror, ?_⟩
  filter_upwards [hfinite] with n hn
  obtain ⟨hbudget, hrate⟩ := hn
  refine ⟨hbudget, ?_, hrate⟩
  exact mme_more_asymmetry_finite_recursive_assembly (K := K) (D n) (A n) hbudget
