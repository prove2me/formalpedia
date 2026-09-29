-- Prove2me | Theorems.Thm_mme_complete_split_112_canonical_power_restricts_from_intact
-- name    : mme_complete_split_112_canonical_power_restricts_from_intact
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:50:58.680483+00:00
-- url     : https://prove2.me/theorems/068f19c0-bb12-4457-bc49-3ce6b6bd582f
-- title:
--   Exact canonical 112 powers restrict from literal intact CW blocks
-- statement:
--   Let $K$ be a field, let $q,N\ge0$ be integers, and let $\beta_i$ be probability distributions on the length-two fine-grade words, for $i=0,1,2$. Suppose integer histograms $\mu_i$ satisfy
--   $$\mu_i(\sigma)=N\beta_i(\sigma)\qquad\text{for every }i,\sigma.$$
--   Let $C_{112}$ denote the canonical $(1,1,2)$ constituent of $\mathrm{CW}_q\otimes\mathrm{CW}_q$. Filter $C_{112}^{\otimes N}$ in all three modes by the exact complete-word profiles $\beta_i$. Let $U$ be the literal intact block of $\mathrm{CW}_q^{\otimes 2N}$ with one coarse cell, grade $(1,1,2)$ at every pair of positions, and complete-word histograms $\mu_i$. Then
--   $$C_{112}^{\otimes N}[\beta_0,\beta_1,\beta_2]\preceq U.$$
--   This is a restriction by actual modewise linear maps. It preserves the whole filtered canonical tensor, so any subsequent restriction of that tensor can be transferred to the intact block. It does not merely extract one supported grade assignment. The theorem includes $N=0$ under the exact-profile convention and makes no global asymptotic rate assertion.
-- source:
--   Canonical 112 complete-profile source and literal recursive intact CW block: coordinate expansion and exact tensor coefficient transport.

import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
open MME MME.TensorObj MME.CompleteSplit MME.CompleteSplit112
  MME.DWZComponentRestriction MME.RecursiveYZ MME.RecursiveYZ.CWCells
  Module PiTensorProduct TensorProduct
universe u
set_option autoImplicit false

theorem mme_complete_split_112_canonical_power_restricts_from_intact
    (K : Type u) [Field K] (q N : ℕ) (beta : Fin 3 → CompleteSplit.Profile 2)
    (mu : Fin 3 → CompleteSplit.CompleteWord 2 → ℕ)
    (hmu : ∀ i sigma, (mu i sigma : ℝ) = (N : ℝ) * (beta i).probability sigma) :
    TensorObj.Restrict (CompleteSplit112.restrictedCanonicalPower K q beta 0 N)
      (RecursiveYZ.CWCells.unbroken K q 2 N (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ ![1, 1, 2]) (fun i _ ↦ mu i)) := by sorry
