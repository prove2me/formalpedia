-- Prove2me | Theorems.Thm_mme_dwz_step2_pointwise_competitor_iff_hash_fiber_gt_one
-- name    : mme_dwz_step2_pointwise_competitor_iff_hash_fiber_gt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T21:16:11.837608+00:00
-- url     : https://prove2.me/theorems/b932b2aa-1c4e-4dff-8f10-11ce4beea5a1
-- title:
--   DWZ Step 2: pointwise competitor and hash-fiber equivalence
-- statement:
--   Fix one realized hash parameter w, a finite outer family, a compatibility predicate for the fixed small Z block, and a predicate saying that an outer word is retained by the realized hash. Assume the distinguished retained outer word is both compatible and hash-retained at w. Then the compatible hash fiber at w has more than one member if and only if there exists a different outer word which is compatible and hash-retained at that same w. This is the exact pointwise incidence bridge used after Additional Zeroing-Out Step 2. It neither defines a tensor hole nor proves that an actual zeroed tensor block supplies the distinct competitor.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.1 Additional Zeroing-Out Step 2 and Section 6.2 Claim 6.8.

import Mathlib.Data.Finset.Card

set_option autoImplicit false

theorem mme_dwz_step2_pointwise_competitor_iff_hash_fiber_gt_one
    {Outer Weight : Type*}
    [Fintype Outer] [DecidableEq Outer]
    (compatible : Outer → Prop) [DecidablePred compatible]
    (hashRetained : Outer → Weight → Prop)
    [DecidableRel hashRetained]
    (retained : Outer) (w : Weight)
    (hRetainedCompatible : compatible retained)
    (hRetainedHash : hashRetained retained w) :
    1 < (Finset.univ.filter
        (fun A : Outer ↦ compatible A ∧ hashRetained A w)).card ↔
      ∃ A : Outer,
        A ≠ retained ∧ compatible A ∧ hashRetained A w := by
  sorry
