-- Prove2me | Theorems.Thm_mme_dwz_table2_first_hash_retention_in_canonical_bucket
-- name    : mme_dwz_table2_first_hash_retention_in_canonical_bucket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:08:47.915828+00:00
-- url     : https://prove2.me/theorems/adfa3909-9d1a-44b5-a064-b91a86092cc0
-- title:
--   First-hash retention inside the canonical affine bucket
-- statement:
--   Under the usual uniform X- and Y-star degree bound d and modulus condition 4d ≤ p, there is one affine state q and a retained target family I contained in the literal canonical Table-2 hash bucket at q. Its size is at least |T||S|/(2p²), and any member of I is isolated within that bucket against every word sharing its full X or Y address. Since the bucket remains canonical rather than existentially opaque, membership in I preserves the three common-state hash predicates needed by Claim 6.8.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, asymmetric hashing in Section 3.10 and Additional Zeroing-Out Step 1, PDF pp. 25-27 and 52-54; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_asymmetric_hash_retention_from_exact_fibers
import Theorems.Thm_mme_dwz_table2_affine_hash_bucket_incidence_factory

open MME

set_option autoImplicit false

theorem mme_dwz_table2_first_hash_retention_in_canonical_bucket
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A)
    (d : ℕ) (hmod : 4 * d ≤ p)
    (hx : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ DWZSquare.shapeX (b t)) =
          (fun t ↦ DWZSquare.shapeX (a t)))).card ≤ d)
    (hy : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ DWZSquare.shapeY (b t)) =
          (fun t ↦ DWZSquare.shapeY (a t)))).card ≤ d) :
    let Edge := Fin (N + 1) → Fin 15
    let XWord := Fin (N + 1) → Fin 5
    let x : Edge → XWord := fun w t ↦ DWZSquare.shapeX (w t)
    let y : Edge → XWord := fun w t ↦ DWZSquare.shapeY (w t)
    let Ω := (Fin (N + 2) → ZMod p) × ZMod p
    ∃ q : Ω, ∃ I : Finset Edge,
      I ⊆ T ∧
      I ⊆ dwzTable2AffineHashBucket S A q ∧
      (∀ e ∈ I, ∀ e' ∈ dwzTable2AffineHashBucket S A q,
        x e = x e' ∨ y e = y e' → e = e') ∧
      ((T.card : ℝ) * (S.card : ℝ)) /
          (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  sorry
