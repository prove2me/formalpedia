-- Prove2me | solution 1 for mme_more_asymmetry_cofinal_cellwise_child_matrix_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T13:34:57.038836+00:00
-- url     : https://prove2.me/submissions/49406ce9-055f-4bdf-a83d-07c70579aeeb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Theorems.Thm_mme_more_asymmetry_cofinal_boundary_and_interior_certificate
import Theorems.Thm_mme_recursive_yz_child_matrix_data_of_boundary_and_interior
import Mathlib.Topology.Instances.Real.Lemmas
open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] :
    ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j))
      (V : ℝ) (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ hraw : MoreAsymmetryRawSourceCompatibility (D n) (A n) K,
          ∃ M : ∀ j, (A n j).ChildMM K,
            (∏ j, (M j).dimA) = (D n).a ∧
            (∏ j, (M j).dimB) = (D n).b ∧
            (∏ j, (M j).dimC) = (D n).c ∧
            (∀ j, ((8 ^ (A n j).repairExponent : ℕ) : ℝ) ≤ ((D n).hash j).lower) ∧
            (∏ j, 2 * 8 ^ (A n j).repairExponent) ≤ (D n).repairCopies ∧
            (∀ j, (A n j).Budget) ∧
            (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
              (D n).rate ((3952233 : ℝ) / 5000000) := by
  obtain ⟨D,A,V,error,hV,hpow,herr,h⟩ :=
    mme_more_asymmetry_cofinal_boundary_and_interior_certificate (K := K)
  refine ⟨D,A,V,error,hV,hpow,herr,?_⟩
  filter_upwards [h] with n hn
  rcases hn with ⟨hraw,P,ha,hb,hc,hlower,hrepair,hbudget,hrate⟩
  choose M hA hB hC using
    (fun j ↦ mme_recursive_yz_child_matrix_data_of_boundary_and_interior (A n j) (P j))
  refine ⟨hraw,M,?_,?_,?_,hlower,hrepair,hbudget,hrate⟩
  · simpa only [hA] using ha
  · simpa only [hB] using hb
  · simpa only [hC] using hc
