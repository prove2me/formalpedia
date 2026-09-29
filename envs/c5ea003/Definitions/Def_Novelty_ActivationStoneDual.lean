-- Prove2me | Definitions.Def_Novelty_ActivationStoneDual
-- name    : Novelty_ActivationStoneDual
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T13:59:04.483162+00:00
-- url     : https://prove2.me/theorems/cee7b2c7-96de-4898-9f85-22a813abb2c4
-- title:
--   Aether Catalog definitions — Novelty_ActivationStoneDual
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ActivationStoneDual`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ActivationStoneDual.lean by skeleton subtraction
import Mathlib

/-!
# A finite Stone model for neural activation patterns

This file isolates the rigorous finite theorem behind the proposed Stone-duality
picture.  A network with `k` Boolean gates has an activation map
`a : X → (Fin k → Bool)`.  Its feasible Stone space is the range of `a`, not in
general the whole Boolean cube.  Hence it has at most `2^k` points, with equality
exactly when every activation pattern is feasible.

Classifiers constant on activation fibres factor uniquely through this finite
space.  Subsets of the feasible space form a Boolean algebra; their pullbacks are
exactly activation-invariant decision regions.  Finally, the full powerset concept
class on this space has VC dimension equal to its number of points.  This last
statement concerns the *full algebra of regions*, not a single fixed classifier.
-/

open Function Set
open scoped BigOperators

namespace ActivationStoneDual

/-- The Boolean activation cube of `k` gates. -/
abbrev Pattern (k : ℕ) := Fin k → Bool

/-- Feasible activation patterns of a concrete activation map. -/
def Feasible {X : Type*} {k : ℕ} (a : X → Pattern k) := Set.range a

/-- The canonical projection from inputs to feasible patterns. -/
def toFeasible {X : Type*} {k : ℕ} (a : X → Pattern k) (x : X) : Feasible a :=
  ⟨a x, x, rfl⟩

/-
The feasible-pattern projection is onto.
-/

/-
There are exactly `2^k` formal activation patterns.
-/

/-
The finite Stone space has at most `2^k` points.
-/

/-
The commonly claimed `2^k` count is valid precisely under feasibility of
all formal activation patterns.
-/

/-- A classifier is activation-invariant when equal patterns force equal labels. -/
def ActivationInvariant {X Y : Type*} {k : ℕ}
    (a : X → Pattern k) (f : X → Y) : Prop :=
  ∀ ⦃x y⦄, a x = a y → f x = f y

/-- An activation-invariant classifier descends to the feasible Stone space. -/
noncomputable def descend {X Y : Type*} {k : ℕ} (a : X → Pattern k) (f : X → Y) :
    Feasible a → Y := fun p => f p.property.choose

/-
Descending and then projecting recovers the original classifier.
-/

/-
The descended classifier is unique.
-/

/-- Pullback of a feasible-pattern region to input space. -/
def realize {X : Type*} {k : ℕ} (a : X → Pattern k) (U : Set (Feasible a)) : Set X :=
  (toFeasible a) ⁻¹' U

/-
Realization preserves complements: Boolean negation of syntax becomes
complement of the geometric decision region.
-/

/-
Realization preserves intersections.
-/

/-
Realization is injective because every feasible pattern has an input witness.
-/

/-
Every activation-invariant binary decision region is the realization of a
unique subset of feasible patterns.
-/

/-- A family of concepts shatters `S` if every subset of `S` is its trace. -/
def Shatters {α : Type*} (C : Set (Set α)) (S : Set α) : Prop :=
  ∀ T, T ⊆ S → ∃ c ∈ C, c ∩ S = T

/-
The full Boolean algebra of subsets shatters every set.
-/

/-
Consequently, on a finite Stone space the full clopen/powerset concept class
has VC dimension exactly the number of Stone points (expressed as the sharp
cardinality bound on shattered finite sets).
-/

/-
A single fixed decision region cannot shatter any nonempty set.  Thus VC
dimension belongs to a *family* of classifiers; assigning it to one fixed network
without specifying a parameterized hypothesis class is a category error.
-/

/-- In the powerset Boolean algebra, the atoms are exactly singleton regions.
We state atomicity directly to avoid conflating it with the number of all clopens. -/
def RegionAtom {α : Type*} (A : Set α) : Prop :=
  A.Nonempty ∧ ∀ B, B ⊆ A → B.Nonempty → B = A

theorem regionAtom_iff_singleton {α : Type*} (A : Set α) :
    RegionAtom A ↔ ∃ x, A = {x} := by
  constructor;
  · intro hA;
    rcases hA with ⟨ ⟨ x, hx ⟩, hA ⟩;
    exact ⟨x, hA {x} (Set.singleton_subset_iff.mpr hx) (by simp) ▸ rfl⟩
  · rintro ⟨ x, rfl ⟩ ; exact ⟨ by simp +decide, fun B hB hB' => by obtain ⟨ y, hy ⟩ := hB'; have := hB hy; aesop ⟩ ;

/-
Thus atoms of the feasible-region algebra correspond bijectively to feasible
activation patterns.
-/
noncomputable def atomEquiv {α : Type*} : α ≃ {A : Set α // RegionAtom A} where
  toFun x := ⟨{x}, (regionAtom_iff_singleton {x}).2 ⟨x, rfl⟩⟩
  invFun A := (regionAtom_iff_singleton A.1).1 A.2 |>.choose
  left_inv x := by
    convert Set.ext_iff.mp ?_ x ; aesop;
    convert rfl
  right_inv A := by
    grind

/-
The number of atoms therefore equals the number of feasible patterns, and is
at most `2^k` for a `k`-gate network.
-/

end ActivationStoneDual


