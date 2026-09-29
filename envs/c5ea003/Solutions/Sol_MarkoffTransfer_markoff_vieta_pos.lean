-- Prove2me | solution 1 for MarkoffTransfer.markoff_vieta_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:18:20.939058+00:00
-- url     : https://prove2.me/submissions/420e9c03-a6cd-4ba4-8b03-77e7ae114821

-- Sol generated from Cryptography/MarkoffTransfer/MarkoffCore.lean
import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore

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












/-- Vieta's product relation: the two roots multiply to `x² + y²`. -/
theorem vieta_mul {x y z : ℤ} (h : IsMarkoff x y z) : z * vieta x y z = x ^ 2 + y ^ 2 := by
  unfold IsMarkoff markoffForm vieta at *; nlinarith [h]

/-! ## Positivity -/


/-! ## Rigidity of the top of an ordered triple -/



/-! ## Descent -/



/-! ## The Markoff tree -/








open MarkoffTransfer in
theorem solution{x y z : ℤ} (h : IsMarkoff x y z) (hx : 0 < x) (hz : 0 < z) :
    0 < vieta x y z := by
  have hm := vieta_mul h
  nlinarith [sq_nonneg y, hx, hz]
