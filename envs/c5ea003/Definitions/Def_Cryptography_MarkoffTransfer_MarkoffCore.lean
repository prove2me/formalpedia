-- Prove2me | Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
-- name    : Cryptography_MarkoffTransfer_MarkoffCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:19:44.691466+00:00
-- url     : https://prove2.me/theorems/55f7c8fe-0f7b-464b-ac20-9a2f4d8d1248
-- title:
--   Aether Catalog definitions — Cryptography_MarkoffTransfer_MarkoffCore
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.MarkoffTransfer.MarkoffCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/MarkoffTransfer/MarkoffCore.lean by skeleton subtraction
import Mathlib

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

namespace MarkoffTransfer

/-! ## The Markoff form and the Vieta involutions -/

/-- The Markoff cubic form `x² + y² + z² - 3xyz`. -/
def markoffForm (x y z : ℤ) : ℤ := x ^ 2 + y ^ 2 + z ^ 2 - 3 * x * y * z

/-- A triple lies on the Markoff surface. -/
def IsMarkoff (x y z : ℤ) : Prop := markoffForm x y z = 0







/-- The Vieta involution in the last coordinate. -/
def vieta (x y z : ℤ) : ℤ := 3 * x * y - z




/-! ## Positivity -/


/-! ## Rigidity of the top of an ordered triple -/



/-! ## Descent -/



/-! ## The Markoff tree -/

/-- Reachability from the root `(1,1,1)` under Vieta involutions and transpositions. -/
inductive MReach : ℤ → ℤ → ℤ → Prop
  | root : MReach 1 1 1
  | vieta {x y z : ℤ} : MReach x y z → MReach x y (vieta x y z)
  | swap₁₂ {x y z : ℤ} : MReach x y z → MReach y x z
  | swap₂₃ {x y z : ℤ} : MReach x y z → MReach x z y






end MarkoffTransfer


