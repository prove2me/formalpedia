-- Prove2me | solution 1 for MarkoffTransfer.markoff_descent_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:18:18.913155+00:00
-- url     : https://prove2.me/submissions/38af6901-9fc1-4a1f-9771-690764773654

-- Sol generated from Cryptography/MarkoffTransfer/MarkoffCore.lean
import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
import Theorems.Thm_MarkoffTransfer_isMarkoff_iff

/-!
# The Markoff Tree: Vieta Involutions, Descent, and the Tree Theorem

This file formalizes the Markoff surface `x² + y² + z² = 3xyz` over `ℤ`, the Vieta
involutions acting on it, and proves the **Markoff tree theorem**: every triple of
positive integers on the Markoff surface is obtained from the root `(1,1,1)` by a
finite sequence of Vieta involutions and coordinate transpositions.

This is the Markoff-side counterpart of the Berggren machinery in
`Cryptography/BerggrenTrees/BerggrenFreeMonoid.lean` (a free monoid of rank 3 acting on
the Pythagorean null cone).  The comparison of the two structures is carried out in
`Cryptography/MarkoffTransfer/BerggrenMarkoffTransfer.lean`.

## Main results

* `markoff_vieta` — the Vieta move `z ↦ 3xy - z` preserves the Markoff surface.
* `vieta_involutive` — it is an involution.
* `markoff_vieta_pos` — it preserves positivity.
* `markoff_eq_one_of_top_eq_mid` — the only positive Markoff triple with `x ≤ y = z`
  is `(1,1,1)`; hence every other ordered triple has a strict top.
* `markoff_descent_le` — for an ordered positive triple with `y < z`, the Vieta
  descendant `3xy - z` lies in `[1, y]`, so descent strictly decreases the sum.
* `markoff_reach` — **Markoff tree theorem**: every positive integer solution is
  reachable from `(1,1,1)`.
-/

open MarkoffTransfer

/-! ## The Markoff form and the Vieta involutions -/













/-! ## Positivity -/


/-! ## Rigidity of the top of an ordered triple -/



/-! ## Descent -/



/-! ## The Markoff tree -/








open MarkoffTransfer in
theorem solution{x y z : ℤ} (h : IsMarkoff x y z) (hx : 0 < x) (hxy : x ≤ y)
    (hyz : y < z) : vieta x y z ≤ y := by
  rw [isMarkoff_iff] at h
  have key : (y - z) * (y - vieta x y z) = x ^ 2 + 2 * y ^ 2 - 3 * x * y ^ 2 := by
    unfold vieta; nlinarith [h]
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hneg : x ^ 2 + 2 * y ^ 2 - 3 * x * y ^ 2 ≤ 0 := by nlinarith [hx, hxy, hy]
  nlinarith [key, hneg]
