-- Prove2me | Definitions.Def_Novelty_MegaSphereInverseLimit
-- name    : Novelty_MegaSphereInverseLimit
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:30.147909+00:00
-- url     : https://prove2.me/theorems/4aef4279-c59d-4eaf-8a6b-4a221a5e8ed3
-- title:
--   Aether Catalog definitions — Novelty_MegaSphereInverseLimit
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MegaSphereInverseLimit`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MegaSphereInverseLimit.lean by skeleton subtraction
import Mathlib

/-!
# The Mega-Sphere I: Inverse limits of towers

The guiding fantasy of this project is a *single algebraic object* whose
projections recover every finite stage of an infinite tower at once — the
"all dimensions at once" object.  The rigorous heart of that fantasy is the
**inverse limit** of a tower

  `⋯ → X (n+1) --π n--> X n → ⋯ → X 1 → X 0`,

the universal object equipped with compatible projections to every stage.

This file builds the inverse limit of a tower of (additive) groups and of rings
completely by hand, as a sub-object of the product, and proves:

* `MegaSphere.invLimit` / `MegaSphere.invLimitRing` — the inverse limit exists
  as a concrete subgroup / subring of `∀ n, X n`.
* `MegaSphere.proj`, `MegaSphere.proj_comp` — the projections to every stage,
  and their compatibility with the connecting maps `π`.
* `MegaSphere.univMap`, `MegaSphere.proj_univMap`, `MegaSphere.univMap_unique`
  — the **universal property**: any cone over the tower factors uniquely through
  the inverse limit.  This is the precise sense in which the mega-object "is" the
  inverse limit.

Two concrete towers illustrate the two extremes:

* `MegaSphere.constTower_invLimit_eq` — the constant tower `X n = G` (identity
  connecting maps) has inverse limit the diagonal copy of `G`.
* `MegaSphere.doublingTower_invLimit_eq_bot` — the doubling tower
  `ℤ ←×2— ℤ ←×2— ⋯` **collapses**: its inverse limit is trivial, because an
  integer divisible by every power of `2` must vanish.
* `MegaSphere.padicTower_nontrivial` — by contrast the `2`-adic tower
  `ZMod (2^(n+1))` with reduction maps has a genuinely nontrivial inverse limit
  (the `2`-adic integers), a *bona fide* mega-object.
-/

namespace MegaSphere

universe u v

variable {X : ℕ → Type u} {Y : Type v}

/-! ## Inverse limit of a tower of additive groups -/

/-- The inverse limit of a tower of additive groups `X` with connecting
homomorphisms `π n : X (n+1) →+ X n`, realised as the subgroup of coherent
sequences inside the product `∀ n, X n`. -/
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



/-- **Universal property (existence).**  Given any additive group `Y` with a
compatible cone `g n : Y →+ X n` (`π n ∘ g (n+1) = g n`), there is an induced
homomorphism into the inverse limit. -/
def univMap [∀ n, AddGroup (X n)] [AddGroup Y] (π : ∀ n, X (n + 1) →+ X n)
    (g : ∀ n, Y →+ X n) (hg : ∀ n, (π n).comp (g (n + 1)) = g n) :
    Y →+ invLimit π where
  toFun y := ⟨fun n => g n y, by
    intro n
    have := hg n
    rw [AddMonoidHom.ext_iff] at this
    simpa using this y⟩
  map_zero' := by ext n; simp
  map_add' := by intro a b; ext n; simp



/-! ## Example: the constant tower recovers its base -/

/-- The constant tower `X n = G` with identity connecting maps. -/
def constTower (G : Type u) [AddGroup G] : ∀ _n : ℕ, G →+ G := fun _ => AddMonoidHom.id G


/-! ## Example: the doubling tower collapses -/

/-- The doubling connecting map `×2 : ℤ →+ ℤ`. -/
def dbl : ∀ _n : ℕ, ℤ →+ ℤ := fun _ => AddMonoidHom.mulLeft (2 : ℤ)




/-! ## Inverse limit of a tower of rings, and a nontrivial mega-object -/

/-- The inverse limit of a tower of rings, as a subring of the product. -/
def invLimitRing [∀ n, Ring (X n)] (π : ∀ n, X (n + 1) →+* X n) :
    Subring (∀ n, X n) where
  carrier := {x | ∀ n, π n (x (n + 1)) = x n}
  one_mem' := by intro n; simp
  mul_mem' := by intro a b ha hb n; simp [map_mul, ha n, hb n]
  zero_mem' := by intro n; simp
  add_mem' := by intro a b ha hb n; simp [map_add, ha n, hb n]
  neg_mem' := by intro a ha n; simp [map_neg, ha n]

/-- Projection of the ring inverse limit onto stage `n`. -/
def projRing [∀ n, Ring (X n)] (π : ∀ n, X (n + 1) →+* X n) (n : ℕ) :
    invLimitRing π →+* X n :=
  (Pi.evalRingHom X n).comp (invLimitRing π).subtype



/-- The `2`-adic tower `ZMod (2^(n+1))` with the reduction ring homomorphisms. -/
noncomputable def padicRed : ∀ n : ℕ, (ZMod (2 ^ (n + 2))) →+* (ZMod (2 ^ (n + 1))) :=
  fun n => ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ _)) (ZMod (2 ^ (n + 1)))


end MegaSphere


