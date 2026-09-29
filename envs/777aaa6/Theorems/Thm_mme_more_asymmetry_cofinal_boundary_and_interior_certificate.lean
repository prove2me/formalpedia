-- Prove2me | Theorems.Thm_mme_more_asymmetry_cofinal_boundary_and_interior_certificate
-- name    : mme_more_asymmetry_cofinal_boundary_and_interior_certificate
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-09-13T12:55:37.986734+00:00
-- url     : https://prove2.me/theorems/2843efdc-e625-411d-b3e8-c54d19bffc8d
-- title:
--   More Asymmetry: cofinal witness with explicit boundary dimensions and interior extractions
-- statement:
--   Construct one cofinal family of physical hash data and recursive stages with diverging source powers, vanishing error, and the fixed-tau rate inequality at tau=3952233/5000000 with V>2401. For the very same family, provide raw-source compatibility, stage budgets, finite repair thresholds and the required products of matrix dimensions. Each boundary child is specified solely by scalar exact-profile and grade equalities and the proved factorial/power-of-five matrix dimension. Only children with all three grades positive supply actual extraction maps. The boundary maps and the remaining assembly are separately proved.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6, Theorem 6.2 and recursive constituent stage; Section 7 for the remaining numerical witness.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_boundary_child_plan
import Mathlib.Topology.Instances.Real.Lemmas
open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

theorem mme_more_asymmetry_cofinal_boundary_and_interior_certificate {K : Type u} [Field K] :
    ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j))
      (V : ℝ) (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ hraw : MoreAsymmetryRawSourceCompatibility (D n) (A n) K,
          ∃ M : ∀ j, (A n j).ChildPlan K,
            (∏ j, (M j).dimA) = (D n).a ∧
            (∏ j, (M j).dimB) = (D n).b ∧
            (∏ j, (M j).dimC) = (D n).c ∧
            (∀ j, ((8 ^ (A n j).repairExponent : ℕ) : ℝ) ≤ ((D n).hash j).lower) ∧
            (∏ j, 2 * 8 ^ (A n j).repairExponent) ≤ (D n).repairCopies ∧
            (∀ j, (A n j).Budget) ∧
            (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
              (D n).rate ((3952233 : ℝ) / 5000000) := by sorry
