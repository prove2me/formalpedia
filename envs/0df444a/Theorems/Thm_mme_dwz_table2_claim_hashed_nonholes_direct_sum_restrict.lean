-- Prove2me | Theorems.Thm_mme_dwz_table2_claim_hashed_nonholes_direct_sum_restrict
-- name    : mme_dwz_table2_claim_hashed_nonholes_direct_sum_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:19:20.648152+00:00
-- url     : https://prove2.me/theorems/fd2735a7-7218-473a-bd80-e366845e302b
-- title:
--   Claim 6.8 hashed nonholes restrict after the first-bucket hash is derived
-- statement:
--   Suppose each retained Table-2 copy has a literal Claim 6.8 nonhole for the conjunction of source compatibility and its owner-conditioned retained hash. If source compatibility on the selected useful block is equivalent to completed fine-address compatibility, and the first-bucket argument proves the retained-hash predicate for every ordered pair of copies, then the direct sum of all completed fine-address blocks is a genuine restriction of the Nth power of CW_q⊗CW_q. The theorem removes the hash conjunct by a proved equivalence; it assumes no separate tensor nonvanishing-to-hash axiom.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.8 and Additional Zeroing-Out Step 2, PDF pp. 56-58; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_useful_block_nonhole_to_completed_fine_address_nonhole
import Theorems.Thm_mme_dwz_table2_completed_useful_nonholes_direct_sum_restrict

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u

set_option autoImplicit false

theorem mme_dwz_table2_claim_hashed_nonholes_direct_sum_restrict
    (K : Type u) [Field K] (q m N k : ℕ)
    (outer : Fin k → Fin N → Fin 15)
    [DecidableRel (retainedFineCompatible m outer)]
    (small : ∀ j : Fin k,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j))
    (claimCompatible : ∀ j : Fin k,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j) → Fin k → Prop)
    [∀ j, DecidableRel (claimCompatible j)]
    (hashRetained : Fin k → Fin k → Prop)
    [DecidableRel hashRetained]
    (hCommonZ : ∀ j j' r,
      DWZSquare.shapeZ (outer j r) = DWZSquare.shapeZ (outer j' r))
    (hYIsolated : ∀ j j',
      (fun r ↦ DWZSquare.shapeY (outer j r)) =
          (fun r ↦ DWZSquare.shapeY (outer j' r)) → j = j')
    (hSourceNonhole : ∀ j : Fin k,
      small j ∈ (MME.DWZStep2.brokenCopy
        (fun z j' ↦ claimCompatible j z j' ∧ hashRetained j j')
        (fun _ _ ↦ True) j).nonholes)
    (hCompatibleIff : ∀ j j' : Fin k,
      claimCompatible j (small j) j' ↔
        retainedFineCompatible m outer
          (fun t ↦
            fineSplitGrade ((small j).1 t).1 ((small j).1 t).2) j')
    (hHashRetained : ∀ j j' : Fin k, hashRetained j j') :
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
