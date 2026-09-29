-- Prove2me | Theorems.Thm_mme_dwz_table2_completed_hashed_nonholes_direct_sum_restrict
-- name    : mme_dwz_table2_completed_hashed_nonholes_direct_sum_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:21:56.651649+00:00
-- url     : https://prove2.me/theorems/89c1f7a5-e2bf-440f-b277-ede30145ae09
-- title:
--   Hashed completed Table-2 nonholes give the faithful direct-sum restriction
-- statement:
--   Let $k$ retained Table-2 component words of length $N$ share one coarse $Z$ word and have isolated coarse $Y$ words. Choose and canonically complete one useful fine-$Z$ word in each copy. Let $H(z,j)$ be the realized source hash-survival predicate. Assume each completed $Z$ address is a literal nonhole for the faithful conjunction of Table-2 compatibility and hash survival. Also assume the source zeroing semantics: whenever every fine component of a mixed address is nonzero, its selected $Z$ word and $X/Y$ owner satisfy $H$. Then
--
--   $$
--   \bigoplus_{j<k}T[A_j]
--   \preceq
--   (CW_q\otimes CW_q)^{\otimes N}.
--   $$
--
--   The hash predicate is retained in both the broken-copy relation and the supported-block premise. Thus the theorem does not replace Claim 6.8's same-hash uniqueness by the stronger and generally unjustified uniqueness among all compatible copies. The only source-specific residual is the stated implication from literal nonvanishing after hash zeroing to $H$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Steps 1 and 2 and Claim 6.8, printed pp. 51-57 (PDF pp. 52-58), specialized to Table 2; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_step2_nonholes_direct_sum_restrict
import Theorems.Thm_mme_dwz_table2_completed_useful_family_step1_premises
import Theorems.Thm_mme_dwz_table2_completed_useful_family_supported_compatible

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u

set_option autoImplicit false

theorem mme_dwz_table2_completed_hashed_nonholes_direct_sum_restrict
    (K : Type u) [Field K] (q m N k : ℕ)
    (outer : Fin k → Fin N → Fin 15)
    [DecidableRel (retainedFineCompatible m outer)]
    (small : ∀ j : Fin k,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j))
    (hashAllowed useful : (Fin N → Fin (3 * 3)) → Fin k → Prop)
    [DecidableRel hashAllowed] [DecidableRel useful]
    (hCommonZ : ∀ j j' r,
      DWZSquare.shapeZ (outer j r) = DWZSquare.shapeZ (outer j' r))
    (hYIsolated : ∀ j j',
      (fun r ↦ DWZSquare.shapeY (outer j r)) =
          (fun r ↦ DWZSquare.shapeY (outer j' r)) → j = j')
    (hNonhole :
      let left : Fin k → Fin 3 → Fin N → Fin 3 := fun j ↦
        completedFineLeft (outer j) (small j).1 (small j).2.1
      let right : Fin k → Fin 3 → Fin N → Fin 3 := fun j ↦
        completedFineRight (outer j) (small j).1 (small j).2.1
      ∀ j : Fin k,
        retainedFineAddress left right j 2 ∈
          (MME.DWZStep2.brokenCopy
            (fun z j' ↦
              retainedFineCompatible m outer z j' ∧ hashAllowed z j')
            useful j).nonholes)
    (hHashSupported :
      let left : Fin k → Fin 3 → Fin N → Fin 3 := fun j ↦
        completedFineLeft (outer j) (small j).1 (small j).2.1
      let right : Fin k → Fin 3 → Fin N → Fin 3 := fun j ↦
        completedFineRight (outer j) (small j).1 (small j).2.1
      ∀ js : Fin 3 → Fin k,
        (∀ r : Fin N,
          (cwSquareFineSplitGrading K q).blockTensor
            (fun i ↦ retainedFineAddress left right (js i) i r) ≠ 0) →
        hashAllowed (retainedFineAddress left right (js 2) 2) (js 0)) :
    let left : Fin k → Fin 3 → Fin N → Fin 3 := fun j ↦
      completedFineLeft (outer j) (small j).1 (small j).2.1
    let right : Fin k → Fin 3 → Fin N → Fin 3 := fun j ↦
      completedFineRight (outer j) (small j).1 (small j).2.1
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock
        (cwSquareFineSplitGrading K q)
        (retainedFineAddress left right j)))
      ((TensorObj.kron (CWObj K q) (CWObj K q)).kronPow N) := by
  sorry
