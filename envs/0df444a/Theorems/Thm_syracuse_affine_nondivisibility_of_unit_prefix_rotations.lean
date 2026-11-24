-- Prove2me | Theorems.Thm_syracuse_affine_nondivisibility_of_unit_prefix_rotations
-- name    : syracuse_affine_nondivisibility_of_unit_prefix_rotations
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T11:11:23.013983+00:00
-- url     : https://prove2.me/theorems/5c7a6f26-4a61-46d0-9944-e4ffcb949b70
-- title:
--   A unit gap between all proper prefix sums obstructs a Syracuse cycle
-- statement:
--   Let $w$ be a positive valuation word of length $p\ge2$ and sum $K$, with $D=2^K-3^p>0$. Suppose that for two rotations of $w$, every nonempty proper prefix of the second has valuation sum exactly one larger than the corresponding prefix of the first. Then $D$ cannot divide the Syracuse affine constant of $w$.
-- source:
--   Uses the earlier affine prefix expansion https://prove2.me/theorems/695ac23a-1e9a-48a2-a6b8-70a72d754213 and rotation transport from the proof of https://prove2.me/theorems/c2919b55-8bd5-4f2d-a208-a825fb0029a9.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_affine_nondivisibility_of_unit_prefix_rotations (w : List ℕ) (hp : 2 ≤ w.length) (hpos : ∀ a ∈ w, 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hprefix : ∃ i j : ℕ, ∀ n : ℕ, 0 < n → n < w.length →
      ((w.rotate j).take n).sum = ((w.rotate i).take n).sum + 1) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
