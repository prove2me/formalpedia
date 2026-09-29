-- Prove2me | Theorems.Thm_mme_dwz_step2_nonholes_direct_sum_restrict
-- name    : mme_dwz_step2_nonholes_direct_sum_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:20:25.839773+00:00
-- url     : https://prove2.me/theorems/47f13a73-00a5-407a-97ad-363e7939ad58
-- title:
--   DWZ Step 2 nonholes form a genuine direct-sum tensor restriction
-- statement:
--   Let a 3-tensor T have a finite grading, and let each of k selected copies be specified by a length-N word of fine grading addresses. Mark its Z-address as a Step-2 nonhole: it is useful for that copy, compatible with it, and compatible with no other selected copy. Assume literal nonzero mixed fine blocks force the usual X/Y ownership and Z-compatibility conditions. Then the direct sum of all selected graded address blocks is a genuine restriction of the tensor power:
--
--   $$\bigoplus_{j<k} T[\operatorname{fineAddress}(j)]\;\preceq\;T^{\otimes N}.$$
--
--   Thus the combinatorial Step-2 deletion rule is not merely a cardinality certificate: its surviving nonholes supply the uniqueness needed to construct actual coordinatewise tensor projections and a direct-sum restriction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Additional Zeroing-Out Steps 1 and 2 in Section 4.5 and Section 6.1; tensor restriction orientation follows the paper's degeneration convention.

import Definitions.Def_mme_dwz_step2_broken_copy
import Theorems.Thm_mme_dwz_fine_z_compatibility_direct_sum_restrict

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_step2_nonholes_direct_sum_restrict
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (fineAddress : Fin k → Fin 3 → Fin N → Fin t)
    (compatible useful : (Fin N → Fin t) → Fin k → Prop)
    [DecidableRel compatible] [DecidableRel useful]
    (hNonhole : ∀ j : Fin k,
      fineAddress j 2 ∈
        (MME.DWZStep2.brokenCopy compatible useful j).nonholes)
    (hXYOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      js 0 = js 1)
    (hSupportedCompatible : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      compatible (fineAddress (js 2) 2) (js 0)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (fineAddress j)))
      (T.kronPow N) := by
  sorry
