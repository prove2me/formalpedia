-- Prove2me | Theorems.Thm_Mpfx_two_le_p_or_trivial_of_extend_one_withBound_subset
-- name    : Mpfx.two_le_p_or_trivial_of_extend_one_withBound_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:45:00.59796+00:00
-- url     : https://prove2.me/theorems/8367e150-d9a8-42b1-b344-75f96253a5f5
-- title:
--   Mpfx: two le p or trivial of extend one with Bound subset
-- statement:
--   From the paper-aligned containment
--   `(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂`, either `F₂.p ≥ 2` (the
--   auxiliary needed for the RTO-padding lemma) or `F₁` contains only `0`. A positive
--   `d ∈ F₁` gives the precision-2 witness `3 · 2^(cexp d − 1)`: it is a value of
--   `F₁.extend 1`, and at most `next d ≤ next b`, so `F₂` must hold it
--   (`two_le_p_of_precision_two_witness`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L588-L639
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L588-L639

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.two_le_p_or_trivial_of_extend_one_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    ((2 : ℕ) : Prec) ≤ F₂.p ∨ ∀ d : _root_.Mpfx.Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by sorry
