-- Prove2me | Theorems.Thm_signed_affine_clamp_lipschitz
-- name    : signed_affine_clamp_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:07:31.838537+00:00
-- url     : https://prove2.me/theorems/47c22d30-6dc6-4c8c-8405-11516dcb56d7
-- title:
--   signed_affine_clamp_lipschitz
-- statement:
--   Automatically extracted helper theorem signed_affine_clamp_lipschitz from oversized parent candidate 029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

theorem signed_affine_clamp_lipschitz
    (g c u : ℝ → ℝ) (fare L : ℝ)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|)
    (hfare : |fare| ≤ L)
    (hc : ∀ s t, s ≤ t → 0 ≤ c t - c s)
    (hu : ∀ s t, s ≤ t → 0 ≤ u t - u s)
    (hu0 : ∀ s, 0 ≤ s → 0 ≤ u s)
    (hsum : ∀ s, c s + u s = s) :
    ∀ s t, 0 ≤ s → s ≤ t →
      |(fare * c t + g (u t)) - (fare * c s + g (u s))| ≤ L * (t - s) := by sorry
