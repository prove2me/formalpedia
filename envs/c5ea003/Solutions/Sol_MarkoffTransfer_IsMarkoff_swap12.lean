-- Prove2me | solution 1 for MarkoffTransfer.IsMarkoff.swap12
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T23:57:28.843652+00:00
-- url     : https://prove2.me/submissions/868f4c33-cf54-47ab-9fa7-aeb6d37da100

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




/-- The Markoff form is symmetric: swapping the first two coordinates. -/
theorem markoffForm_swap₁₂ (x y z : ℤ) : markoffForm x y z = markoffForm y x z := by
  unfold markoffForm; ring









/-! ## Positivity -/


/-! ## Rigidity of the top of an ordered triple -/



/-! ## Descent -/



/-! ## The Markoff tree -/








open MarkoffTransfer in
theorem solution{x y z : ℤ} (h : IsMarkoff x y z) : IsMarkoff y x z := by
  unfold IsMarkoff at *; rw [← markoffForm_swap₁₂]; exact h
