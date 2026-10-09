-- Prove2me | Theorems.Thm_eq30NextPayoff_lipschitz
-- name    : eq30NextPayoff_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:23:24.323186+00:00
-- url     : https://prove2.me/theorems/3239a957-b977-4530-b9fe-aaf4b8e7fea3
-- title:
--   eq30NextPayoff_lipschitz
-- statement:
--   Automatically extracted helper theorem eq30NextPayoff_lipschitz from oversized parent candidate 00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:00648688a2884e641df25684f46b6ba24b8b98fb76e987446502026ac9ead0ba

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30NextPayoff
import Definitions.Def_eq30ClippedSeats
import Theorems.Thm_eq30ClippedSeats_increment_bounds
import Theorems.Thm_eq30ResidualSeats_mono
import Theorems.Thm_eq30NextPayoff_eq_clipped
import Theorems.Thm_eq30_affine_clamp_lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30NextPayoff_lipschitz
    (g : ℝ → ℝ) (p x fare L : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|)
    (hfare0 : 0 ≤ fare) (hfareL : fare ≤ L) :
    ∀ s t, 0 ≤ s → s ≤ t →
      |eq30NextPayoff g p x fare t - eq30NextPayoff g p x fare s| ≤
        L * (t - s) := by sorry
