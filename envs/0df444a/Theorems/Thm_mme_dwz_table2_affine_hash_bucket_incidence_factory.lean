-- Prove2me | Theorems.Thm_mme_dwz_table2_affine_hash_bucket_incidence_factory
-- name    : mme_dwz_table2_affine_hash_bucket_incidence_factory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:46:47.581012+00:00
-- url     : https://prove2.me/theorems/2d31d6a6-1f53-411b-b25d-92e00d8282ad
-- title:
--   Exact incidences of the canonical Table-2 affine bucket
-- statement:
--   Let A be an ambient family of Table-2 component words and T a target subfamily. For an odd prime p, let the canonical first-hash bucket at an affine state q consist exactly of the words in A whose three asymmetric hashes lie in the cast progression-free set S. Then the affine state space has cardinality p^(N+3); each target word lies in exactly |S| p^(N+1) buckets; and any distinct target/ambient pair sharing its X or Y word lies together in at most |S| p^N buckets. Every canonical bucket is a subset of A. Unlike an existential incidence factory, this theorem preserves the literal bucket semantics used later in Claim 6.8.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, asymmetric hashing in Section 3.10 and Additional Zeroing-Out Step 1, PDF pp. 25-27 and 52-54; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_affine_hash_bucket
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

open MME

set_option autoImplicit false

theorem mme_dwz_table2_affine_hash_bucket_incidence_factory
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A) :
    let Edge := Fin (N + 1) → Fin 15
    let XWord := Fin (N + 1) → Fin 5
    let x : Edge → XWord := fun w t ↦ DWZSquare.shapeX (w t)
    let y : Edge → XWord := fun w t ↦ DWZSquare.shapeY (w t)
    let Ω := (Fin (N + 2) → ZMod p) × ZMod p
    Fintype.card Ω = p ^ (N + 3) ∧
      (∀ q : Ω, dwzTable2AffineHashBucket S A q ⊆ A) ∧
      (∀ a ∈ T,
        (Finset.univ.filter (fun q : Ω ↦
          a ∈ dwzTable2AffineHashBucket S A q)).card =
            S.card * p ^ (N + 1)) ∧
      ∀ ab ∈ (T.product A).filter (fun ab ↦
          ab.1 ≠ ab.2 ∧ (x ab.1 = x ab.2 ∨ y ab.1 = y ab.2)),
        (Finset.univ.filter (fun q : Ω ↦
          ab.1 ∈ dwzTable2AffineHashBucket S A q ∧
            ab.2 ∈ dwzTable2AffineHashBucket S A q)).card ≤
              S.card * p ^ N := by
  sorry
