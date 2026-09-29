-- Prove2me | Theorems.Thm_mme_dwz_table2_completed_useful_nonholes_direct_sum_restrict
-- name    : mme_dwz_table2_completed_useful_nonholes_direct_sum_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:17:26.892573+00:00
-- url     : https://prove2.me/theorems/0e3aed6e-42bb-42fc-b057-2df9713a1140
-- title:
--   Completed Table-2 nonholes form a genuine fine-address direct-sum restriction
-- statement:
--   Let $k$ retained Table-2 component words of length $N$ share the same coarse $Z$ word and have pairwise isolated coarse $Y$ words. Choose one literal useful fine-$Z$ pair word in each retained copy, and complete it with the canonical fine $X/Y$ grades. Assume that every completed mode-$2$ address belongs to the nonhole set of its own Step-2 broken copy. Then the direct sum of the $k$ completed fine-address blocks is a genuine restriction of the $N$th tensor power of $CW_q\otimes CW_q$:
--
--   $$
--   \bigoplus_{j<k} T[A_j]
--   \preceq
--   (CW_q\otimes CW_q)^{\otimes N}.
--   $$
--
--   The hypothesis uses literal broken-copy membership, so it asserts both that each selected fine-$Z$ word is compatible with its distinguished copy and that no competing retained copy is compatible with it. The theorem derives the required $X/Y$ owner and supported fine-$Z$ compatibility statements from the completed useful-block equations and exact Step-1 histograms; no additional tensor-support or nonvanishing assumption remains in the interface.
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

theorem mme_dwz_table2_completed_useful_nonholes_direct_sum_restrict
    (K : Type u) [Field K] (q m N k : ℕ)
    (outer : Fin k → Fin N → Fin 15)
    [DecidableRel (retainedFineCompatible m outer)]
    (small : ∀ j : Fin k,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j))
    (useful : (Fin N → Fin (3 * 3)) → Fin k → Prop)
    [DecidableRel useful]
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
            (retainedFineCompatible m outer) useful j).nonholes) :
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
