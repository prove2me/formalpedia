-- Prove2me | Theorems.Thm_mme_more_asymmetry_finite_log_recipe_half_loss_from_cofinal_explicit_child_witness
-- name    : mme_more_asymmetry_finite_log_recipe_half_loss_from_cofinal_explicit_child_witness
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-23T19:38:03.836234+00:00
-- url     : https://prove2.me/theorems/b9731e53-a0fd-4fc4-870c-a49e17cd09ed
-- title:
--   Finite half-loss recipe from cofinal source-compatible witnesses
-- statement:
--   Assume that, over a field, there is a cofinal family of recursive More Asymmetry profiles and stages whose powers diverge and whose error tends to zero. Assume also that all sufficiently large stages have source-compatible child realizations satisfying the stated repair budgets and certified rate bound at tau = 3952233/5000000. Then some finite logarithmic recipe realizes the requested output and volume bounds with half the stated loss budgets. This isolates the finite-scale extraction and conversion from the cofinal construction data to an inductive LogRecipe.
-- source:
--   Derived from the cofinal explicit child-witness statement in Prove2Me (https://prove2.me/theorems/fd26c1fe-7510-422d-8c75-054270ba9ce8), as the finite half-loss extraction step for More Asymmetry, arXiv:2404.16349v2.

import Definitions.Def_mme_logarithmic_regional_CW_recipe
import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_boundary_child_plan
import Mathlib.Topology.Instances.Real.Lemmas

open BigOperators MME MME.ProfiledCW MME.RegionRealization MME.TensorObj
  MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

theorem mme_more_asymmetry_finite_log_recipe_half_loss_from_cofinal_explicit_child_witness
    {K : Type u} [Field K]
    (hcofinal :
      ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j))
        (V : ℝ) (error : ℕ → ℝ),
        (2401 : ℝ) < V ∧
        Tendsto (fun n ↦ (D n).power) atTop atTop ∧
        Tendsto error atTop (nhds 0) ∧
        ∀ᶠ n : ℕ in atTop,
          ∃ hraw : MoreAsymmetryRawSourceCompatibility (D n) (A n) K,
            ∃ (a b c : ∀ j, Fin (A n j).childCells → ℕ),
              (∏ j, ∏ k, a j k) = (D n).a ∧
              (∏ j, ∏ k, b j k) = (D n).b ∧
              (∏ j, ∏ k, c j k) = (D n).c ∧
              (∀ j k,
                (A n j).BoundaryChild k (a j k) (b j k) (c j k) ∨
                ((∀ i, 0 < (((A n j).childCell k).2.val i).val) ∧
                  TensorObj.Restrict
                    (MMObj K (a j k) (b j k) (c j k))
                    ((A n j).childTensor K k))) ∧
              (∀ j, ((8 ^ (A n j).repairExponent : ℕ) : ℝ) ≤
                ((D n).hash j).lower) ∧
              (∏ j, 2 * 8 ^ (A n j).repairExponent) ≤ (D n).repairCopies ∧
              (∀ j, (A n j).Budget) ∧
              (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
                (D n).rate ((3952233 : ℝ) / 5000000)) :
    ∃ (n ell : ℕ) (P : Predicate (4 * n))
      (D : LogRecipe (4 * n) ell P),
      0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
      (n : ℝ) * ((281302098456 : ℝ) / 100000000000 - 1 / 2000000) +
          Real.log (D.inputs : ℝ) ≤ D.logOutputs ∧
      (n : ℝ) * (3 * ((209612367517 : ℝ) / 100000000000) - 1 / 20000000) ≤
          Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by sorry
