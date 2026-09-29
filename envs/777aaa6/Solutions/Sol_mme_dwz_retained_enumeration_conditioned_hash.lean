-- Prove2me | solution 1 for mme_dwz_retained_enumeration_conditioned_hash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:28:01.418818+00:00
-- url     : https://prove2.me/submissions/6044881c-d442-4a58-90cf-a4803c8bd89a

import Theorems.Thm_mme_dwz_table2_canonical_bucket_conditioned_hash

open BigOperators
open MME

set_option autoImplicit false
set_option warningAsError true

/-- Reindexing a canonical-bucket family into the retained outer enumeration
preserves Claim 6.8's conditioned hash equation for every ordered pair of
enumerated copies. -/
theorem solution
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
  classical
  dsimp only
  intro j j'
  obtain ⟨a, haI, ha⟩ := hEnumerates j
  obtain ⟨a', ha'I, ha'⟩ := hEnumerates j'
  have hSameZ : ∀ t,
      DWZSquare.shapeZ (a' t) = DWZSquare.shapeZ (a t) := by
    intro t
    have hz := hCommonZ j' j (reindex t)
    simpa only [ha, ha', Equiv.symm_apply_apply] using hz
  have hhash := mme_dwz_table2_canonical_bucket_conditioned_hash
    hpodd S hSrange hSfree A q a a' (hBucket haI) (hBucket ha'I) hSameZ
  simpa only [ha, ha', Equiv.symm_apply_apply, dwzTable2CastX,
    dwzTable2CastZ] using hhash
