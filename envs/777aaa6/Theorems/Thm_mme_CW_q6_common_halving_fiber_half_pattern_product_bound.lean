-- Prove2me | Theorems.Thm_mme_CW_q6_common_halving_fiber_half_pattern_product_bound
-- name    : mme_CW_q6_common_halving_fiber_half_pattern_product_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:17:19.680559+00:00
-- url     : https://prove2.me/theorems/96da749f-34cc-4375-8a86-715906de6c41
-- title:
--   The two half-pattern sets jointly contain at least one label pair per fiber entry
-- statement:
--   Let a primary hash family of fiber size $H$ admit a common balanced XY halving, and fix a color $a$. Let $P_{X,a}$ be the set of first-half X patterns of its entries and let $P_{Y,a}$ be the set of second-half Y patterns. Then
--   $$H\le |P_{X,a}|\,|P_{Y,a}|.$$
--   Within the color, the pair consisting of these two halves uniquely determines the entry. The product bound therefore remains valid even if either individual half-pattern repeats.
-- source:
--   The fixed third-coordinate word and the second Y half determine the second X half; full X injectivity then gives joint injectivity of the half-pattern pair.

import Definitions.Def_mme_CW_q6_common_paired_halving
import Mathlib.Data.Fintype.Card

open MME
set_option autoImplicit false

theorem mme_CW_q6_common_halving_fiber_half_pattern_product_bound
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (a : Fin A) :
    let PX := Finset.univ.image (fun h : Fin H ↦
      fun r : Fin N ↦ (family.entry (a,h)).val 0 (halving.position (Sum.inl r)))
    let PY := Finset.univ.image (fun h : Fin H ↦
      fun r : Fin N ↦ (family.entry (a,h)).val 1 (halving.position (Sum.inr r)))
    H ≤ PX.card * PY.card := by sorry
