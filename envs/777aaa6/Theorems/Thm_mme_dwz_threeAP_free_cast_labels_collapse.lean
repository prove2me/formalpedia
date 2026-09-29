-- Prove2me | Theorems.Thm_mme_dwz_threeAP_free_cast_labels_collapse
-- name    : mme_dwz_threeAP_free_cast_labels_collapse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:58:39.721022+00:00
-- url     : https://prove2.me/theorems/acafeba9-4ed2-4395-b888-242d8be1ebb2
-- title:
--   Lower-half Salem–Spencer labels collapse in DWZ hash order
-- statement:
--   Let $S$ be a three-term-progression-free subset of $[0,p/2)$. If $x,y,z\in S$ satisfy the DWZ modular hash relation
--
--   $$x+y=2z\pmod p,$$
--
--   then $x=z=y$. This is the exact lower-half Salem–Spencer no-wraparound bridge used to turn three surviving hash labels into one common label.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 3.10, Salem–Spencer pruning; lower-half no-wraparound specialization.

import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

set_option autoImplicit false

theorem mme_dwz_threeAP_free_cast_labels_collapse
    (p : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (x y z : ℕ) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S)
    (hAP : (x : ZMod p) + (y : ZMod p) = 2 * (z : ZMod p)) :
    x = z ∧ z = y := by
  sorry
