-- Prove2me | Theorems.Thm_mme_dwz_table2_global_exact_canonical_bucket_source_enumeration
-- name    : mme_dwz_table2_global_exact_canonical_bucket_source_enumeration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T22:58:08.250806+00:00
-- url     : https://prove2.me/theorems/ac065bfd-146b-4708-846d-dcd83f73796d
-- title:
--   Enumerate the exact-profile canonical bucket in literal source order
-- statement:
--   Let I be an exact-profile family of Table-2 words retained in one canonical affine hash bucket, with |I|=k. There is an injective enumeration by Fin(k) in the original source-coordinate order. Every enumerated word has the prescribed exact fifteen-component histogram, reindexing it recovers a literal member of I, and every coordinatewise supported mixed triple has the same X-owner and Y-owner. No retained owner or cardinality is lost.
-- source:
--   Duan--Wu--Zhou, arXiv:2210.10173, first-hash retention and the owner isolation used in Additional Zeroing-Out Step 1.

import Theorems.Thm_mme_dwz_table2_global_canonical_bucket_supported_mix_xy_owner

open MME

set_option autoImplicit false

/-- Enumerate every retained exact-profile word in source coordinate order.
No owner is lost: reindexing the result gives the literal member of `I`.
The global first-hash isolation consequently identifies the X and Y owners
of every coordinatewise supported mixed triple. -/

theorem mme_dwz_table2_global_exact_canonical_bucket_source_enumeration
    {p N L k : ℕ} [Fact p.Prime]
    (reindex : Fin (N + 1) ≃ Fin L)
    (S : Finset ℕ)
    (A I : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (counts : Fin 15 → ℕ)
    (alphaX alphaY alphaZ : Fin 5 → ℕ)
    (hcard : I.card = k)
    (hA : ∀ e, e ∈ A ↔
      (∀ x, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeX (e t) = x} = alphaX x) ∧
      (∀ y, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeY (e t) = y} = alphaY y) ∧
      (∀ z, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeZ (e t) = z} = alphaZ z))
    (hexact : I ⊆ A.filter fun e ↦
      ∀ s, Fintype.card {t : Fin (N + 1) // e t = s} = counts s)
    (hbucket : I ⊆ MME.dwzTable2AffineHashBucket S A q)
    (hisolated : ∀ e ∈ I,
      ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
        (fun t ↦ MME.DWZSquare.shapeX (e t)) =
            (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
          (fun t ↦ MME.DWZSquare.shapeY (e t)) =
            (fun t ↦ MME.DWZSquare.shapeY (e' t)) →
        e = e') :
    ∃ outer : Fin k → Fin L → Fin 15,
      Function.Injective outer ∧
      (∀ j, (fun t ↦ outer j (reindex t)) ∈ I) ∧
      (∀ j s, Fintype.card {t : Fin L // outer j t = s} = counts s) ∧
      ∀ js : Fin 3 → Fin k,
        (∀ t : Fin L,
          (MME.DWZSquare.shapeX (outer (js 0) t)).val +
            (MME.DWZSquare.shapeY (outer (js 1) t)).val +
            (MME.DWZSquare.shapeZ (outer (js 2) t)).val = 4) →
        js 0 = js 1 := by
  sorry
