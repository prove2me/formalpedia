-- Prove2me | Theorems.Thm_eq30_affine_clamp_lipschitz
-- name    : eq30_affine_clamp_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T01:08:12.509997+00:00
-- url     : https://prove2.me/theorems/14deeef7-6233-4f42-9e8a-ea983b9cd250
-- title:
--   eq30_affine_clamp_lipschitz
-- statement:
--   Automatically extracted helper theorem eq30_affine_clamp_lipschitz from oversized parent candidate aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a.
-- source:
--   candidate-decomposition:9852d19d-dcdf-4154-92bd-c1b0e9510afb:aebbcdb992724a2571794764d2ff4f8f47ccdbe37aab58add1ef294e3698f95a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy

theorem eq30_affine_clamp_lipschitz
    (g c u : ℝ → ℝ) (fare L : ℝ)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|)
    (hfare0 : 0 ≤ fare) (hfareL : fare ≤ L)
    (hc : ∀ s t, s ≤ t → 0 ≤ c t - c s)
    (hu : ∀ s t, s ≤ t → 0 ≤ u t - u s)
    (hu0 : ∀ s, 0 ≤ s → 0 ≤ u s)
    (hsum : ∀ s, c s + u s = s) :
    ∀ s t, 0 ≤ s → s ≤ t →
      |(fare * c t + g (u t)) - (fare * c s + g (u s))| ≤ L * (t - s) := by sorry
