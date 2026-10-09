-- Prove2me | Theorems.Thm_d9NextRevenue_lipschitz_signed
-- name    : d9NextRevenue_lipschitz_signed
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T15:00:30.899523+00:00
-- url     : https://prove2.me/theorems/48ed2ec4-253c-4327-a782-35f34ee85e46
-- title:
--   d9NextRevenue_lipschitz_signed
-- statement:
--   Automatically extracted helper theorem d9NextRevenue_lipschitz_signed from oversized parent candidate d5a4c1698e5bdc35ce9a4470b87d5993f12d3610d40417f1ddcb94e8747e1f97.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:d5a4c1698e5bdc35ce9a4470b87d5993f12d3610d40417f1ddcb94e8747e1f97

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_d9ClippedSeats
import Theorems.Thm_d9ClippedSeats_increment_bounds
import Theorems.Thm_d9ResidualSeats_mono
import Theorems.Thm_d9ResidualSeats_nonneg
import Definitions.Def_d9NextRevenue
import Theorems.Thm_d9NextRevenue_eq_clipped
import Theorems.Thm_signed_affine_clamp_lipschitz
open NestedSeatAlloc.IntPolicy

theorem d9NextRevenue_lipschitz_signed
    (g : ℝ → ℝ) (p x fare L : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hg : ∀ a b, 0 ≤ a → 0 ≤ b → |g b - g a| ≤ L * |b - a|)
    (hL : |fare| ≤ L) :
    ∀ s t, 0 ≤ s → s ≤ t →
      |d9NextRevenue g p x fare t - d9NextRevenue g p x fare s| ≤
        L * (t - s) := by sorry
