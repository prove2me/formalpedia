-- Prove2me | Theorems.Thm_CRTSplitNoGo_card_injPrefix
-- name    : CRTSplitNoGo.card_injPrefix
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:35:10.113282+00:00
-- url     : https://prove2.me/theorems/ee7567b7-cb68-46f6-b157-02be1f572c7b
-- title:
--   The birthday law for orbit prefixes.
-- statement:
--   **The birthday law for orbit prefixes.**  For `T < n = card α`, the number of maps
--   `f : α → α` whose orbit prefix `a, f a, …, f^[T] a` is collision-free equals
--   `(n - 1).descFactorial T * n ^ (n - T)`.  Dividing by `n ^ n`, the collision-free fraction is
--   `∏_{i=1}^{T} (1 - i/n)`: collisions become likely only at `T ≍ √n`.
--
--   ```lean
--   theorem CRTSplitNoGo.card_injPrefix(a : α) (T : ℕ) (hT : T < Fintype.card α) :
--       (injPrefixFinset a T).card
--         = (Fintype.card α - 1).descFactorial T * (Fintype.card α) ^ (Fintype.card α - T) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGoBirthday.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGoBirthday.lean#L229

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

theorem CRTSplitNoGo.card_injPrefix(a : α) (T : ℕ) (hT : T < Fintype.card α) :
    (injPrefixFinset a T).card
      = (Fintype.card α - 1).descFactorial T * (Fintype.card α) ^ (Fintype.card α - T) := by sorry
