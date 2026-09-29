-- Prove2me | solution 1 for mme_dwz_table2_claim_hashed_nonholes_direct_sum_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:24:26.96219+00:00
-- url     : https://prove2.me/submissions/db7c979e-3294-4f6d-846e-91412f3c8b72

import Theorems.Thm_mme_dwz_useful_block_nonhole_to_completed_fine_address_nonhole
import Theorems.Thm_mme_dwz_table2_completed_useful_nonholes_direct_sum_restrict

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u

set_option autoImplicit false
set_option warningAsError true

/-!
# Claim 6.8 nonholes with a derived retained hash

Once every retained first-bucket word satisfies the owner-conditioned hash,
the hash conjunct in Claim 6.8 is automatic.  It can therefore be removed
while transporting the literal source nonholes to completed fine addresses,
after which the accepted direct-sum restriction applies.
-/

theorem solution
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
  classical
  apply mme_dwz_table2_completed_useful_nonholes_direct_sum_restrict
    K q m N k outer small (fun _ _ ↦ True) hCommonZ hYIsolated
  dsimp only
  intro j
  apply mme_dwz_useful_block_nonhole_to_completed_fine_address_nonhole
    m outer small j
      (fun z j' ↦ claimCompatible j z j' ∧ hashRetained j j')
      (hSourceNonhole j)
  intro j'
  constructor
  · rintro ⟨hCompatible, _⟩
    exact (hCompatibleIff j j').mp hCompatible
  · intro hCompatible
    exact ⟨(hCompatibleIff j j').mpr hCompatible,
      hHashRetained j j'⟩
