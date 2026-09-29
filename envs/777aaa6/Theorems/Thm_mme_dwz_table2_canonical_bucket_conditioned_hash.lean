-- Prove2me | Theorems.Thm_mme_dwz_table2_canonical_bucket_conditioned_hash
-- name    : mme_dwz_table2_canonical_bucket_conditioned_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:14:52.353133+00:00
-- url     : https://prove2.me/theorems/8db0d4ea-006a-4a5e-ae99-f3f38291a0fe
-- title:
--   A canonical Table-2 bucket supplies Claim 6.8 conditioned hashing
-- statement:
--   Let two Table-2 component words lie in the same canonical first-hash bucket and have the same coarse Z word. For an odd modulus, the candidate X hash equals the Z hash evaluated with the offset conditioned on the central X word. Explicitly, h_X(I′)=h_Z(2Σ I_t w_t−Σ(4−K_t)w_t,K). This is precisely Claim 6.8’s retained-hash predicate, now derived from canonical bucket membership rather than assumed as a separate nonvanishing condition.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, asymmetric hashing in Section 3.10 and Claim 6.8 / Additional Zeroing-Out Step 2, PDF pp. 25-27 and 56-58; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_affine_hash_bucket
import Theorems.Thm_mme_dwz_same_affine_bucket_conditioned_XZ

open BigOperators
open MME

set_option autoImplicit false

theorem mme_dwz_table2_canonical_bucket_conditioned_hash
    {p N : ℕ} (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (central candidate : Fin (N + 1) → Fin 15)
    (hcentral : central ∈ dwzTable2AffineHashBucket S A q)
    (hcandidate : candidate ∈ dwzTable2AffineHashBucket S A q)
    (hSameZ : ∀ t,
      DWZSquare.shapeZ (candidate t) = DWZSquare.shapeZ (central t)) :
    let weight : Fin (N + 1) → ZMod p := fun t ↦ q.1 t.castSucc
    let b0 : ZMod p := q.1 (Fin.last (N + 1))
    let hX : (Fin (N + 1) → ZMod p) →
        (Fin (N + 1) → ZMod p) → ZMod p := fun w I ↦
      b0 + ∑ t, I t * w t
    let hZ : ZMod p → (Fin (N + 1) → ZMod p) →
        (Fin (N + 1) → ZMod p) → ZMod p := fun w0 w K ↦
      b0 + (2 : ZMod p)⁻¹ *
        (w0 + ∑ t, ((4 : ZMod p) - K t) * w t)
    let conditionedW0 : (Fin (N + 1) → ZMod p) → ZMod p := fun w ↦
      2 * (∑ t, dwzTable2CastX central t * w t) -
        ∑ t, ((4 : ZMod p) - dwzTable2CastZ central t) * w t
    hX weight (dwzTable2CastX candidate) =
      hZ (conditionedW0 weight) weight (dwzTable2CastZ central) := by
  sorry
