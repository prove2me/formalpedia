-- Prove2me | Definitions.Def_Bridges_CRTSplitNoGoBirthday
-- name    : Bridges_CRTSplitNoGoBirthday
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:35.535232+00:00
-- url     : https://prove2.me/theorems/07731430-2b72-423a-927d-70c963e8329a
-- title:
--   Aether Catalog definitions — Bridges_CRTSplitNoGoBirthday
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CRTSplitNoGoBirthday`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CRTSplitNoGoBirthday.lean by skeleton subtraction
import Mathlib

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

namespace CRTSplitNoGo

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The orbit of the base point `a` under `f`. -/
def orb (f : α → α) (a : α) (i : ℕ) : α := f^[i] a



/-- The orbit prefix `a, f a, …, f^[T] a` is collision-free. -/
def InjPrefix (f : α → α) (a : α) (T : ℕ) : Prop :=
  ∀ i ≤ T, ∀ j ≤ T, orb f a i = orb f a j → i = j

instance (f : α → α) (a : α) (T : ℕ) : Decidable (InjPrefix f a T) := by
  unfold InjPrefix; infer_instance



/-- The set of maps with a collision-free orbit prefix of length `T + 1`. -/
def injPrefixFinset (a : α) (T : ℕ) : Finset (α → α) :=
  Finset.univ.filter (fun f : α → α => InjPrefix f a T)

/-- Overwrite the value of `f` at the last prefix point by the base point. -/
def reset (a : α) (T : ℕ) (f : α → α) : α → α := Function.update f (orb f a T) a











/-! ## The birthday bound: most maps are still collision-free at time `√n` -/






/-! ## Exhaustive cross-check of the birthday law on a small case

For `α = Fin 4`, `a = 0`, `T = 2` the law predicts `3 · 2 · 4² = 96` collision-free maps out of
`4⁴ = 256`.  The following is verified by kernel enumeration of all `256` maps. -/


end CRTSplitNoGo


