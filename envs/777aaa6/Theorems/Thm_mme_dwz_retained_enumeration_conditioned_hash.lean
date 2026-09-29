-- Prove2me | Theorems.Thm_mme_dwz_retained_enumeration_conditioned_hash
-- name    : mme_dwz_retained_enumeration_conditioned_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:26:11.56626+00:00
-- url     : https://prove2.me/theorems/e0c38cf8-b0d5-427c-b302-1e55376fc724
-- title:
--   Canonical-bucket enumeration gives every Claim 6.8 retained hash
-- statement:
--   Let a retained finite family I lie in one canonical Table-2 affine bucket and let outer be a lossless reindexed enumeration of I. If all enumerated words share their coarse Z address, then every ordered pair of copies satisfies the exact owner-conditioned Claim 6.8 equation: the candidate X hash equals the owner Z hash at the offset conditioned by the owner X word. This transports canonical bucket semantics through the actual retained-family enumeration and discharges the all-pairs hash premise of the completed nonhole restriction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Algorithm 2, Claim 6.8, and Additional Zeroing-Out Step 2, PDF pp. 52-58; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_canonical_bucket_conditioned_hash

open BigOperators
open MME

set_option autoImplicit false

theorem mme_dwz_retained_enumeration_conditioned_hash
    {p N L k : ℕ} (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A I : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (reindex : Fin (N + 1) ≃ Fin L)
    (outer : Fin k → Fin L → Fin 15)
    (hEnumerates : ∀ j : Fin k, ∃ a ∈ I,
      outer j = fun r ↦ a (reindex.symm r))
    (hBucket : I ⊆ dwzTable2AffineHashBucket S A q)
    (hCommonZ : ∀ j j' r,
      DWZSquare.shapeZ (outer j r) = DWZSquare.shapeZ (outer j' r)) :
    let weight : Fin (N + 1) → ZMod p := fun t ↦ q.1 t.castSucc
    let b0 : ZMod p := q.1 (Fin.last (N + 1))
    let addressX : Fin k → Fin (N + 1) → ZMod p := fun j t ↦
      (DWZSquare.shapeX (outer j (reindex t))).val
    let addressZ : Fin k → Fin (N + 1) → ZMod p := fun j t ↦
      (DWZSquare.shapeZ (outer j (reindex t))).val
    let hX : (Fin (N + 1) → ZMod p) →
        (Fin (N + 1) → ZMod p) → ZMod p := fun w X ↦
      b0 + ∑ t, X t * w t
    let hZ : ZMod p → (Fin (N + 1) → ZMod p) →
        (Fin (N + 1) → ZMod p) → ZMod p := fun w0 w Z ↦
      b0 + (2 : ZMod p)⁻¹ *
        (w0 + ∑ t, ((4 : ZMod p) - Z t) * w t)
    let conditionedW0 : Fin k →
        (Fin (N + 1) → ZMod p) → ZMod p := fun j w ↦
      2 * (∑ t, addressX j t * w t) -
        ∑ t, ((4 : ZMod p) - addressZ j t) * w t
    ∀ j j' : Fin k,
      hX weight (addressX j') =
        hZ (conditionedW0 j weight) weight (addressZ j) := by
  sorry
