-- Prove2me | Theorems.Thm_mme_dwz_table2_global_canonical_bucket_supported_mix_xy_owner
-- name    : mme_dwz_table2_global_canonical_bucket_supported_mix_xy_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T14:20:53.979832+00:00
-- url     : https://prove2.me/theorems/1939efc0-366e-4f46-9153-3f90621982ff
-- title:
--   A global canonical first-hash bucket has a unique X/Y owner
-- statement:
--   Let I be a retained subfamily of the full exact-marginal Table-2 family inside one canonical affine bucket. Assume the usual first-hash isolation: a retained word is the only word in that bucket with its complete X word, and likewise with its complete Y word. If three retained owners are mixed coordinatewise and every resulting coarse block is supported, then the X owner and Y owner are equal. Indeed, exact marginal counts place the mixed word back in the ambient family, while the three affine bucket equations are inherited separately from its X, Y, and Z owners. Isolation then identifies the mixed word with each of the X and Y owners.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 1 and the first-hash bucket argument in Sections 5-6; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_affine_hash_bucket

open MME

set_option autoImplicit false

theorem mme_dwz_table2_global_canonical_bucket_supported_mix_xy_owner
    {p N k : ℕ} [Fact p.Prime]
    (S : Finset ℕ)
    (A I : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (alphaX alphaY alphaZ : Fin 5 → ℕ)
    (hA : ∀ e, e ∈ A ↔
      (∀ x, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeX (e t) = x} = alphaX x) ∧
      (∀ y, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeY (e t) = y} = alphaY y) ∧
      (∀ z, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeZ (e t) = z} = alphaZ z))
    (outer : Fin k → Fin (N + 1) → Fin 15)
    (houter_injective : Function.Injective outer)
    (houter : ∀ j, outer j ∈ I)
    (hbucket : I ⊆ MME.dwzTable2AffineHashBucket S A q)
    (hisolated : ∀ e ∈ I,
      ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
        (fun t ↦ MME.DWZSquare.shapeX (e t)) =
            (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
          (fun t ↦ MME.DWZSquare.shapeY (e t)) =
            (fun t ↦ MME.DWZSquare.shapeY (e' t)) →
        e = e')
    (js : Fin 3 → Fin k)
    (hsupported : ∀ t : Fin (N + 1),
      (MME.DWZSquare.shapeX (outer (js 0) t)).val +
        (MME.DWZSquare.shapeY (outer (js 1) t)).val +
        (MME.DWZSquare.shapeZ (outer (js 2) t)).val = 4) :
    js 0 = js 1 := by sorry
