-- Prove2me | Definitions.Def_Bridges_PosetTheory_GaloisConnectionFixedPoints
-- name    : Bridges_PosetTheory_GaloisConnectionFixedPoints
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:37.704553+00:00
-- url     : https://prove2.me/theorems/2f9da99e-f74a-454c-bfac-26f28cc27810
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_GaloisConnectionFixedPoints
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.GaloisConnectionFixedPoints`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/GaloisConnectionFixedPoints.lean by skeleton subtraction
import Mathlib

/-!
# The order-theoretic half of the Galois-connection bridge

This file develops, **independently of Knaster–Tarski**, the fixed-point theory
attached to a Galois connection between two complete lattices.

Given complete lattices `α`, `β` and maps `l : α → β`, `u : β → α` forming a
Galois connection (`l a ≤ b ↔ a ≤ u b`), we:

* define the closure operator `cl a = u (l a)` on `α` and the kernel/interior
  operator `ker b = l (u b)` on `β`;
* prove the standard consequences of the adjunction *directly* from the
  defining bi-implication (`l`, `u` monotone; `a ≤ u (l a)`; `l (u b) ≤ b`;
  `u (l (u b)) = u b`; `l (u (l a)) = l a`);
* introduce the closed elements `{a // u (l a) = a}` and coclosed elements
  `{b // l (u b) = b}`;
* establish the fundamental fixed-point correspondence as an `OrderIso`
  (`fixedPointOrderIso`);
* prove that the closed elements form a complete lattice and the coclosed
  elements form a complete lattice, *without invoking Knaster–Tarski*,
  using only the closure-system structure (arbitrary infima of closed elements
  are closed; arbitrary suprema are obtained by closing the ambient supremum,
  and dually for coclosed elements);
* record the equivalent explicit least-upper-bound / greatest-lower-bound
  theorems with their closed-form witnesses.

**Anti-circularity.**  Nothing here references `Bridges.KnasterTarskiBridge`.
The bridge to Knaster–Tarski (least fixed point of `cl` is `u (l ⊥)`, greatest
fixed point of `ker` is `l (u ⊤)`) lives in the separate file
`Bridges.GaloisConnectionKnasterTarskiBridge`.
-/

namespace GaloisConnectionFixedPoints

universe u v

variable {α : Type u} {β : Type v}

/-! ## Section 1: the closure and kernel operators -/

section Operators

/-- The closure operator on `α` attached to a candidate adjunction `(l, u)`. -/
def cl (l : α → β) (u : β → α) (a : α) : α := u (l a)

/-- The kernel (interior) operator on `β` attached to a candidate adjunction
`(l, u)`. -/
def ker (l : α → β) (u : β → α) (b : β) : β := l (u b)


end Operators

/-! ## Section 2: consequences of the adjunction, proved directly -/

section GaloisConnection

variable [CompleteLattice α] [CompleteLattice β] {l : α → β} {u : β → α}

/-- The unit of the adjunction: `a ≤ u (l a)`.  Proved directly from
`l a ≤ l a ↔ a ≤ u (l a)`. -/
theorem le_u_l (gc : GaloisConnection l u) (a : α) : a ≤ u (l a) :=
  (gc a (l a)).1 le_rfl

/-- The counit of the adjunction: `l (u b) ≤ b`.  Proved directly from
`l (u b) ≤ b ↔ u b ≤ u b`. -/
theorem l_u_le (gc : GaloisConnection l u) (b : β) : l (u b) ≤ b :=
  (gc (u b) b).2 le_rfl

/-- The left adjoint is monotone (direct proof). -/
theorem monotone_l (gc : GaloisConnection l u) : Monotone l :=
  fun _ a' h => (gc _ (l a')).2 (h.trans (le_u_l gc a'))

/-- The right adjoint is monotone (direct proof). -/
theorem monotone_u (gc : GaloisConnection l u) : Monotone u :=
  fun b _ h => (gc (u b) _).1 ((l_u_le gc b).trans h)

/-- Triangle identity on the right: `u (l (u b)) = u b`. -/
theorem u_l_u (gc : GaloisConnection l u) (b : β) : u (l (u b)) = u b :=
  le_antisymm (monotone_u gc (l_u_le gc b)) (le_u_l gc (u b))

/-- Triangle identity on the left: `l (u (l a)) = l a`. -/
theorem l_u_l (gc : GaloisConnection l u) (a : α) : l (u (l a)) = l a :=
  le_antisymm (l_u_le gc (l a)) (monotone_l gc (le_u_l gc a))

/-! ### The closure / kernel operators are genuine closure / interior operators -/







/-! ## Section 3 & 4: closed / coclosed elements and the fixed-point `OrderIso` -/

/-- The closed elements of `α`: those fixed by the closure operator `u ∘ l`. -/
abbrev Closed (l : α → β) (u : β → α) : Type u := {a : α // u (l a) = a}

/-- The coclosed elements of `β`: those fixed by the kernel operator `l ∘ u`. -/
abbrev Coclosed (l : α → β) (u : β → α) : Type v := {b : β // l (u b) = b}

/-- **Fundamental fixed-point correspondence.**  The left and right adjoints
restrict to mutually inverse, order-preserving bijections between the closed
elements of `α` and the coclosed elements of `β`. -/
def fixedPointOrderIso (gc : GaloisConnection l u) : Closed l u ≃o Coclosed l u where
  toFun a := ⟨l a.1, l_u_l gc a.1⟩
  invFun b := ⟨u b.1, u_l_u gc b.1⟩
  left_inv a := Subtype.ext a.2
  right_inv b := Subtype.ext b.2
  map_rel_iff' := by
    intro a a'
    constructor
    · intro h
      have h2 : u (l a.1) ≤ u (l a'.1) := monotone_u gc h
      rwa [a.2, a'.2] at h2
    · intro h
      exact monotone_l gc h



/-! ## Section 5: the closed elements form a complete lattice

We use the closure-system structure rather than Knaster–Tarski:

* arbitrary infima of closed elements are closed (`closed_sInf_closed`);
* a least closed upper bound of a family is the closure of its ambient
  supremum (`closed_isLeastUB`).

The complete-lattice instance is then obtained from `completeLatticeOfInf`,
which only requires that every set of closed elements has an infimum that is a
greatest lower bound. -/





/-! ## Section 6: the coclosed elements form a complete lattice (dual) -/





end GaloisConnection

end GaloisConnectionFixedPoints


