-- Prove2me | Theorems.Thm_CRTSplitNoGo_majority_collision_free
-- name    : CRTSplitNoGo.majority_collision_free
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:35:17.507532+00:00
-- url     : https://prove2.me/theorems/17edd353-aea9-4aa6-bfee-3683abc8bb75
-- title:
--   Generic maps need `√n` steps.
-- statement:
--   **Generic maps need `√n` steps.**  Once `T (T+1) ≤ n` — i.e. `T ≲ √n` — at least half of
--   all maps of an `n`-element set still have a collision-free orbit prefix of length `T + 1`.
--   With `n = p ≈ √N` this is the `N^{1/4}` birthday barrier of Pollard rho, exponential in
--   `log N`.
--
--   ```lean
--   theorem CRTSplitNoGo.majority_collision_free(a : α) (T : ℕ) (hT : T < Fintype.card α)
--       (h : T * (T + 1) ≤ Fintype.card α) :
--       ((Fintype.card α : ℝ) ^ (Fintype.card α)) / 2 ≤ ((injPrefixFinset a T).card : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGoBirthday.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGoBirthday.lean#L371

-- Thm stub generated from Bridges/CRTSplitNoGoBirthday.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoBirthday

/-!
# The CRT-Split No-Go, Part VI: the birthday law for orbit prefixes

Parts I–V reduce the factor-revealing event of any `N`-explicit iteration to a cycle closure
of the reduced orbit mod `p`.  This file supplies the missing *quantitative* half for the
generic regime (a): an exact count of how many maps of a finite set have a collision-free
orbit prefix.

**Main theorem** (`card_injPrefix`).  Let `α` be a finite type with `n = card α` elements and
let `a : α`.  For `T < n`, the number of maps `f : α → α` whose orbit prefix
`a, f a, …, f^[T] a` is injective is exactly

  `(n - 1).descFactorial T * n ^ (n - T)`.

Equivalently, the fraction of maps with a collision-free prefix of length `T + 1` is
`∏_{i=1}^{T} (1 - i/n)`, the classical birthday product: it drops below `1/2` only once
`T ≍ √n`.  With `n = p ≈ √N` this is the `N^{1/4}` of Pollard rho, and it is exponential in
`log N`.

The proof is a fibration argument: the "reset" operation, which overwrites the value of `f`
at the last prefix point `f^[T] a`, has fibers of size exactly `n` inside the collision-free
set at level `T`, of which exactly `n - (T+1)` survive to level `T + 1`.  The key structural
input is `orb_eq_of_agree`: an orbit prefix depends only on the values of `f` at the earlier
prefix points, which is the finite-set shadow of Fact 2 (locality of iteration).

Small cases are cross-checked by exhaustive enumeration (`card_injPrefix_fin4_two`).
-/

open CRTSplitNoGo

variable {α : Type*} [Fintype α] [DecidableEq α]




















/-! ## The birthday bound: most maps are still collision-free at time `√n` -/

theorem CRTSplitNoGo.majority_collision_free(a : α) (T : ℕ) (hT : T < Fintype.card α)
    (h : T * (T + 1) ≤ Fintype.card α) :
    ((Fintype.card α : ℝ) ^ (Fintype.card α)) / 2 ≤ ((injPrefixFinset a T).card : ℝ) := by sorry
