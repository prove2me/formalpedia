-- Prove2me | Definitions.Def_Bridges_TwoTreeClosure_CollisionCounts
-- name    : Bridges_TwoTreeClosure_CollisionCounts
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:41.663491+00:00
-- url     : https://prove2.me/theorems/ec7acbf1-d8a7-45c0-9e9b-de1dc1d457b7
-- title:
--   Aether Catalog definitions — Bridges_TwoTreeClosure_CollisionCounts
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TwoTreeClosure.CollisionCounts`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TwoTreeClosure/CollisionCounts.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_TwoTreeClosure_RepresentationOrbit
import Definitions.Def_Bridges_TwoTreeClosure_TreeCore

/-!
# Both collision behaviours are power-law frequent

`RepresentationOrbit.collision_letter_dichotomy` shows that letter-*splitting* and
letter-*preserving* hypotenuse collisions both occur above every bound.  That is a
support statement; the open direction asked for frequencies.  This file proves the
first quantitative half of it: both behaviours occur at least a **power of the
magnitude** often, so neither is a sparse accident.

* `SplitCollision N` / `SameCollision N` : `N` carries two distinct primitive nodes
  with different (resp. equal) ascent letters.
* `many_split_collisions` : for every `T` there are at least `T` distinct numbers
  `N ≤ 500 T² + 5` with `SplitCollision N`.  Since `X = 500T² + 5`, the counting
  function of splitting collisions is `≫ X^{1/2}`.
* `many_same_letter_collisions` : for every `T` there are at least `T` distinct
  numbers `N ≤ sgN T` with `SameCollision N`, and `sgN T ≍ T⁴`, so the counting
  function of non-splitting collisions is `≫ X^{1/4}`.
* `collision_counts_both_unbounded` : both counting functions tend to infinity.

The two exponents `1/2` and `1/4` are lower bounds coming from one explicit family
each (the Brahmagupta family `500t² + 5` and the Sophie Germain family `u⁴ + 4`);
they already show that the *ratio* of the two behaviours cannot be decided by a
finite computation, which is what the density direction asks about.
-/

namespace TwoTreeClosure

/-- `N` has two distinct primitive representations whose nodes carry different
ascent letters. -/
def SplitCollision (N : ℕ) : Prop :=
  ∃ m n m' n' : ℕ, IsNode m n ∧ IsNode m' n' ∧ hyp m n = N ∧ hyp m' n' = N ∧
    (m, n) ≠ (m', n') ∧ letterOf m n ≠ letterOf m' n'

/-- `N` has two distinct primitive representations whose nodes carry the *same*
ascent letter. -/
def SameCollision (N : ℕ) : Prop :=
  ∃ m n m' n' : ℕ, IsNode m n ∧ IsNode m' n' ∧ hyp m n = N ∧ hyp m' n' = N ∧
    (m, n) ≠ (m', n') ∧ letterOf m n = letterOf m' n'

/-! ### The splitting family `500 t² + 5` -/




/-! ### The non-splitting Sophie Germain family -/



/-! ### Counting -/




end TwoTreeClosure


