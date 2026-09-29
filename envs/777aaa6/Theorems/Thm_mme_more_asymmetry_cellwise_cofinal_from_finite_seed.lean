-- Prove2me | Theorems.Thm_mme_more_asymmetry_cellwise_cofinal_from_finite_seed
-- name    : mme_more_asymmetry_cellwise_cofinal_from_finite_seed
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T23:07:15.917002+00:00
-- url     : https://prove2.me/theorems/97edb115-17bf-4606-9277-57c627a36101
-- title:
--   More Asymmetry: cofinal cellwise construction from one finite seed
-- statement:
--   A single source-compatible finite seed with concrete recursive child restrictions, exact dimensions and repair budgets, stage budgets, positive power, and strict rate surplus can be repeated to produce the full cofinal cellwise certificate: diverging powers, vanishing relative error, and the same exact finite extraction conditions at every sufficiently large scale. The proof must rebuild the global repair assembly from all repeated stages so the integer copy floors are preserved.
-- source:
--   Finite replication reduction for mme_more_asymmetry_cofinal_cellwise_child_matrix_certificate (5a144ae3-b39c-4828-85a0-ab177d14e972), using the source's recursive stages and exact repair-copy assembly; Alman et al., arXiv:2404.16349v2, Sections 5-7.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_child_matrix_data
import Mathlib.Topology.Instances.Real.Lemmas

open BigOperators MME MME.TensorObj MME.HashExtraction
  MME.RecursiveYZ.Certificate Filter

set_option autoImplicit false
universe u

theorem mme_more_asymmetry_cellwise_cofinal_from_finite_seed
    {K : Type u} [Field K]
    (hseed :
      ∃ (D : Data) (A : ∀ j, Stage ((D.hash j)))
    (hraw : MoreAsymmetryRawSourceCompatibility D A K)
    (M : ∀ j, (A j).ChildMM K),
    (∏ j, (M j).dimA) = D.a ∧
    (∏ j, (M j).dimB) = D.b ∧
    (∏ j, (M j).dimC) = D.c ∧
    (∀ j, ((8 ^ (A j).repairExponent : ℕ) : ℝ) ≤ (D.hash j).lower) ∧
    (∏ j, 2 * 8 ^ (A j).repairExponent) ≤ D.repairCopies ∧
    (∀ j, (A j).Budget) ∧
    0 < D.power ∧
    (2401 : ℝ) ^ (6 * D.power) <
      D.rate ((3952233 : ℝ) / 5000000)) :
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
          (∀ j, ((8 ^ (A n j).repairExponent : ℕ) : ℝ) ≤
            ((D n).hash j).lower) ∧
          (∏ j, 2 * 8 ^ (A n j).repairExponent) ≤ (D n).repairCopies ∧
          (∀ j, (A n j).Budget) ∧
          (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
            (D n).rate ((3952233 : ℝ) / 5000000) := by sorry
