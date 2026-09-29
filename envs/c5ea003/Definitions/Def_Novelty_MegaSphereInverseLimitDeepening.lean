-- Prove2me | Definitions.Def_Novelty_MegaSphereInverseLimitDeepening
-- name    : Novelty_MegaSphereInverseLimitDeepening
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:27.595626+00:00
-- url     : https://prove2.me/theorems/dfb1f7f3-25ea-429a-b43b-2722f2d933c6
-- title:
--   Aether Catalog definitions — Novelty_MegaSphereInverseLimitDeepening
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MegaSphereInverseLimitDeepening`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MegaSphereInverseLimitDeepening.lean by skeleton subtraction
import Mathlib

/-!
# The Mega-Sphere I (Deepening): collapse, surjectivity, and a contrarian disproof

This file deepens `MegaSphereInverseLimit.lean`.  We reuse the by-hand inverse
limit of a tower of additive groups (redeveloped here so the file is
self-contained) and prove three genuinely new results, in the "contrarian"
spirit of formulating bold statements and either proving or disproving them.

* **General multiplication tower collapses.**
  `MegaSphereDeep.mulTower_invLimit_eq_bot` — for *any* integer `d` with
  `2 ≤ |d|`, the tower `ℤ ←×d— ℤ ←×d— ⋯` has trivial inverse limit.  This
  strictly generalises the doubling collapse (`d = 2`).

* **Contrarian disproof.**  A tempting bold conjecture is: *the inverse limit of
  a tower of nontrivial groups is nontrivial.*  This is **false**:
  `MegaSphereDeep.exists_nontrivial_stages_trivial_invLimit` exhibits a tower
  with every stage `ZMod 2` (nontrivial) but whose connecting maps are all zero,
  giving a trivial inverse limit.  The "mega-object" can be trivial even when
  every finite stage is not.

* **Function.Surjective towers do not collapse.**  Positively,
  `MegaSphereDeep.proj_zero_surjective_of_surjective` proves the Mittag-Leffler
  phenomenon for `ℕ`-indexed towers: if every connecting map is surjective, the
  projection from the inverse limit onto the bottom stage is surjective (so the
  mega-object surjects onto stage `0`).
-/

namespace MegaSphereDeep

universe u

variable {X : ℕ → Type u}

/-! ## Inverse limit of a tower of additive groups (self-contained) -/

/-- The inverse limit of a tower of additive groups. -/
def invLimit [∀ n, AddGroup (X n)] (π : ∀ n, X (n + 1) →+ X n) :
    AddSubgroup (∀ n, X n) where
  carrier := {x | ∀ n, π n (x (n + 1)) = x n}
  zero_mem' := by intro n; simp
  add_mem' := by intro a b ha hb n; simp [map_add, ha n, hb n]
  neg_mem' := by intro a ha n; simp [map_neg, ha n]


/-- The projection of the inverse limit onto stage `n`. -/
def proj [∀ n, AddGroup (X n)] (π : ∀ n, X (n + 1) →+ X n) (n : ℕ) :
    invLimit π →+ X n :=
  (Pi.evalAddMonoidHom X n).comp (invLimit π).subtype


/-! ## General multiplication tower collapses -/


/-- The multiplication connecting map `×d : ℤ →+ ℤ`. -/
def mulTower (d : ℤ) : ∀ _n : ℕ, ℤ →+ ℤ := fun _ => AddMonoidHom.mulLeft d



/-! ## Contrarian disproof: nontrivial stages, trivial limit -/

/-- The all-zero connecting maps on the constant tower `ZMod 2`. -/
def zeroTower : ∀ _n : ℕ, ZMod 2 →+ ZMod 2 := fun _ => 0



/-! ## Function.Surjective towers do not collapse -/

/-
**Mittag-Leffler for `ℕ`-towers.**  If every connecting map is surjective,
then the projection of the inverse limit onto the bottom stage is surjective:
the mega-object surjects onto stage `0`.
-/

end MegaSphereDeep


