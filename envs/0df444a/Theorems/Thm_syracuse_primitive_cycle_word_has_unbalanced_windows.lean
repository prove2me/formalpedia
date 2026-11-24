-- Prove2me | Theorems.Thm_syracuse_primitive_cycle_word_has_unbalanced_windows
-- name    : syracuse_primitive_cycle_word_has_unbalanced_windows
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T11:11:25.509208+00:00
-- url     : https://prove2.me/theorems/4e967a73-b659-43cf-bdbc-63121d5c061e
-- title:
--   Primitive Syracuse cycle words have two equal-length windows differing by at least two
-- statement:
--   Let $w$ be a primitive positive valuation word of length $p\ge2$, let $K$ be its sum and suppose $2^K-3^p>0$ divides its Syracuse affine constant. Then two cyclic windows of a common length $1\le n<p$ have valuation sums differing by at least two. The starting indices of both windows are less than $p$. Thus no cyclically balanced primitive word can satisfy the affine cycle divisibility.
-- source:
--   A structural refinement of https://prove2.me/theorems/4c78e8bc-6a5e-4296-856d-b824327aebc3. Combines the extremal-rotation argument for balanced words with syracuse_affine_nondivisibility_of_unit_prefix_rotations.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_cycle_word_has_unbalanced_windows (w : List ℕ) (hp : 2 ≤ w.length) (hpos : ∀ a ∈ w, 0 < a)
    (hprimitive : ∀ n : ℕ, 0 < n → n < w.length → w.rotate n ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    ∃ i j n : ℕ, i < w.length ∧ j < w.length ∧ 0 < n ∧ n < w.length ∧
      ((w.rotate i).take n).sum + 2 ≤ ((w.rotate j).take n).sum := by sorry
