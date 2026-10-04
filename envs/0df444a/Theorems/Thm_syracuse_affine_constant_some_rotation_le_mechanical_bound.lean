-- Prove2me | Theorems.Thm_syracuse_affine_constant_some_rotation_le_mechanical_bound
-- name    : syracuse_affine_constant_some_rotation_le_mechanical_bound
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-02T19:17:58.990808+00:00
-- url     : https://prove2.me/theorems/695ac23a-1e9a-48a2-a6b8-70a72d754213
-- title:
--   Some rotation of an affine valuation word is bounded by its mechanical weighted sum
-- statement:
--   Let w be any finite list of natural numbers with positive length p, and let K be its sum. Then there is one natural rotation index d<p such that the canonical affine constant C(w.rotate d) is at most the sum over j=0,...,p-1 of3^(p-1-j)*2^floor(K*j/p). Entries may be zero; there is no entry-positivity, power-gap, primitivity, cycle, minimum-state, baseline or period-cap assumption. This generic arithmetic majorization is not a claim of primitive-word nondivisibility, larger cycle exclusion or Collatz convergence.
-- source:
--   Public-packet packaging of the independently source-reviewed Task103 generic affine mechanical-majorization draft, C:/Users/jason/prove2me/cycle_affine_mechanical_majorization_draft_01.lean, SHA97b46c96e2515fbc52f69f9b3c96dee1aa2430f5602726848612ebfb1689652f. All seven mathematical declaration bodies are copied exactly inside a fresh namespace; final solution preserves the exact generic type and calls the retained theorem. Uses Mathlib and canonical Offset Definition UUID864533ea-15c3-4810-a04c-d66a460333b7 ONLY, never redefining C or importing public/Open/prospective theorem supports. Actual prior MATHEMATICAL_SOURCE_ONLY_PASS is bound as a source-review milestone, not new-packet or kernel/public acceptance. The canonical local Offset module is absent; no stub is created. New whole-packet review and separately authorized canonical-import/kernel checking remain required. No public UUID, reservation, transport or runtime authority is implied.

import Mathlib
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

open scoped BigOperators

theorem syracuse_affine_constant_some_rotation_le_mechanical_bound (w : List ℕ) (hp : 0 < w.length) :
    ∃ d : ℕ, d < w.length ∧
      syracuseAffineConstant (w.rotate d) ≤
        ∑ j ∈ Finset.range w.length,
          (3 ^ (w.length - 1 - j) * 2 ^ ((w.sum * j) / w.length)) := by sorry
