-- Prove2me | solution 1 for mme_recursive_assembly_of_numerical_repair_budgets
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T09:39:19.934666+00:00
-- url     : https://prove2.me/submissions/c3dc3252-0718-4c4c-90d4-df95dac8a877

import Theorems.Thm_mme_more_asymmetry_recursive_assembly_from_forward_fields
import Theorems.Thm_mme_finite_repaired_MM_product_from_copy_budgets
import Theorems.Thm_mme_recursive_yz_certificate_finite_assembly

open BigOperators MME MME.RecursiveYZ.Certificate
universe u

/-- A numerical copy budget suffices to assemble the locally extracted matrix tensors. -/
theorem solution {K : Type u} [Field K]
    (D : HashExtraction.Data) (A : ∀ j, Stage (D.hash j))
    (hraw : MoreAsymmetryRawSourceCompatibility D A K)
    (a b c : Fin D.factors → ℕ)
    (htemplate : ∀ j, TensorObj.Restrict (MMObj K (a j) (b j) (c j)) ((A j).template K))
    (ha : (∏ j, a j) = D.a) (hb : (∏ j, b j) = D.b) (hc : (∏ j, c j) = D.c)
    (hlower : ∀ j, ((8 ^ (A j).repairExponent : ℕ) : ℝ) ≤ (D.hash j).lower)
    (hrepair : (∏ j, 2 * 8 ^ (A j).repairExponent) ≤ D.repairCopies) :
    RecursiveAssembly D A K := by
  apply mme_more_asymmetry_recursive_assembly_from_forward_fields D A hraw a b c
    htemplate ha hb hc
  intro counts hcounts
  have henough : ∀ j, 8 ^ (A j).repairExponent ≤ counts j := by
    intro j
    exact_mod_cast (hlower j).trans (hcounts j)
  have hr := mme_finite_repaired_MM_product_from_copy_budgets (K := K)
    a b c counts (fun j => 8 ^ (A j).repairExponent)
    (fun _ => pow_pos (by decide) _) henough hrepair
  simpa only [ha, hb, hc] using hr
