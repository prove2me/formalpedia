-- Prove2me | solution 1 for mme_dwz_fourth_canonical_support_square_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T15:22:08.562122+00:00
-- url     : https://prove2.me/submissions/48750ccb-f842-4770-9fed-7a2da590a8a8

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_CW_fourth_canonical_support_exact

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

/-- Finite shape enumeration checked by the Lean kernel. -/
private theorem every_total_eight_address_splits :
    ∀ x y z : Fin 9, x.val + y.val + z.val = 8 →
      ∃ p : Fin 15 × Fin 15,
        (DWZSquare.shapeX p.1).val + (DWZSquare.shapeX p.2).val = x.val ∧
        (DWZSquare.shapeY p.1).val + (DWZSquare.shapeY p.2).val = y.val ∧
        (DWZSquare.shapeZ p.1).val + (DWZSquare.shapeZ p.2).val = z.val := by
  decide

theorem solution
    {K : Type u} [Field K] (q : ℕ) (i : Fin q)
    (sigma : Fin 3 → Fin 9) :
    (MME.StothersFourth.cwFourthCanonicalGrading K q).blockTensor sigma ≠ 0 ↔
      ∃ p : Fin 15 × Fin 15,
        (DWZSquare.shapeX p.1).val + (DWZSquare.shapeX p.2).val =
          (sigma 0).val ∧
        (DWZSquare.shapeY p.1).val + (DWZSquare.shapeY p.2).val =
          (sigma 1).val ∧
        (DWZSquare.shapeZ p.1).val + (DWZSquare.shapeZ p.2).val =
          (sigma 2).val := by
  have hsupport :
      (MME.StothersFourth.cwFourthCanonicalGrading K q).blockTensor sigma ≠ 0 ↔
        (∑ k, (sigma k).val) = 8 := by
    simpa only [not_not] using
      not_congr (mme_CW_fourth_canonical_support_exact (K := K) q i sigma)
  rw [hsupport]
  constructor
  · intro hsum
    apply every_total_eight_address_splits (sigma 0) (sigma 1) (sigma 2)
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsum
  · rintro ⟨p, hx, hy, hz⟩
    have hleft := DWZSquare.shape_sum p.1
    have hright := DWZSquare.shape_sum p.2
    have hsum : (sigma 0).val + (sigma 1).val + (sigma 2).val = 8 := by
      omega
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsum
