-- Prove2me | Theorems.Thm_MarkoffTransfer_markoff_reach_ordered
-- name    : MarkoffTransfer.markoff_reach_ordered
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:54:52.052242+00:00
-- url     : https://prove2.me/theorems/e2a6339b-4903-469a-aef4-87a3f19dbfbe
-- title:
--   Reachability for ordered triples, by strong induction on a bound for the sum.
-- statement:
--   Reachability for **ordered** triples, by strong induction on a bound for the sum.
--
--   ```lean
--   theorem MarkoffTransfer.markoff_reach_ordered:
--       ∀ N : ℕ, ∀ x y z : ℤ, x + y + z ≤ (N : ℤ) → 0 < x → x ≤ y → y ≤ z → IsMarkoff x y z →
--         MReach x y z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MarkoffTransfer/MarkoffCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MarkoffTransfer/MarkoffCore.lean#L150

-- Thm stub generated from Cryptography/MarkoffTransfer/MarkoffCore.lean
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













/-! ## Positivity -/


/-! ## Rigidity of the top of an ordered triple -/



/-! ## Descent -/



/-! ## The Markoff tree -/

theorem MarkoffTransfer.markoff_reach_ordered:
    ∀ N : ℕ, ∀ x y z : ℤ, x + y + z ≤ (N : ℤ) → 0 < x → x ≤ y → y ≤ z → IsMarkoff x y z →
      MReach x y z := by sorry
