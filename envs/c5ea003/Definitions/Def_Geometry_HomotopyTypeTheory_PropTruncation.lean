-- Prove2me | Definitions.Def_Geometry_HomotopyTypeTheory_PropTruncation
-- name    : Geometry_HomotopyTypeTheory_PropTruncation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:18:56.179181+00:00
-- url     : https://prove2.me/theorems/6a50896e-4cee-4c04-8505-f0acf02e0054
-- title:
--   Aether Catalog definitions — Geometry_HomotopyTypeTheory_PropTruncation
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.HomotopyTypeTheory.PropTruncation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/HomotopyTypeTheory/PropTruncation.lean by skeleton subtraction
import Mathlib

/-!
# Higher Inductive Types: Propositional Truncation

This file formalizes the simplest non-trivial **higher inductive type (HIT)** of Homotopy
Type Theory — the **propositional truncation** `∥A∥` — inside Lean 4 using `Quot`.  The point
constructor is `mk`, and the *path constructor* (every two elements are identified) is realized
by `Quot.sound` on the total relation.  We prove:

* the truncation is a *mere proposition* (the defining higher constructor),
* the recursion and dependent induction principles together with their computation rules,
* the **universal property** of the truncation as a left adjoint to the inclusion of
  propositions, in the form that truncation is idempotent on propositions, and
* that truncation **commutes with binary products**.

## Main results

* `HoTT.Trunc.isProp`          — `∥A∥` is a mere proposition (uses the path constructor).
* `HoTT.Trunc.lift_mk`         — computation rule for the recursor.
* `HoTT.Trunc.ind`             — dependent eliminator into proposition families.
* `HoTT.Trunc.equivOfIsProp`   — for a proposition `A`, `mk : A → ∥A∥` is an equivalence.
* `HoTT.Trunc.prod_equiv`      — `∥A × B∥ ↔ ∥A∥ × ∥B∥` (truncation preserves products).

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer): A HIT with a single path constructor identifying all points can be
encoded as `Quot` of the *total* relation `fun _ _ => True`. Conjecture: the resulting type is
provably a mere proposition, and its universal property collapses to `Quot.lift` because every
target proposition is a `Subsingleton`.

EXPERIMENT (Experimenter): `Trunc.isProp` needs `Quot.ind` to reduce two arbitrary elements to
`mk`-points and then `Quot.sound trivial`. The recursor lifts any `f : A → P` (P a proposition)
because `f a = f b` holds by `Subsingleton.elim`. Idempotence on propositions exhibits an
explicit two-sided inverse to `mk`.

ANALYSIS (Analyst): The encoding works. The genuinely HIT-flavored fact is `isProp` — it is
*false* for the bare quotient unless the relation is total, and its proof essentially *is* the
path constructor. The product-preservation theorem `prod_equiv` is the first place where both
directions require the recursor in a non-trivial way.

CRITIQUE (Critic): Is `prod_equiv` trivial? No: the backward map must combine two independent
truncated witnesses into a truncated pair, which requires nested elimination. We avoid the
degenerate "everything into Prop is equal" shortcut by keeping `Trunc A` in `Sort`, so `isProp`
is a theorem, not an instance-driven triviality.

SYNTHESIS (PI): `Quot` plus the total relation yields a faithful propositional-truncation HIT
with all expected computation rules.
-- !-- Lab Notes -- !--
-/

universe u v w

namespace HoTT

/-- A type is a **mere proposition** if any two of its elements are equal. -/
def IsProp (A : Sort u) : Prop := ∀ x y : A, x = y

namespace Trunc

/-- The total relation on `A`, used as the single path constructor of the HIT. -/
private def total (A : Sort u) : A → A → Prop := fun _ _ => True

end Trunc

/-- The **propositional truncation** `∥A∥`, the higher inductive type with a point constructor
`mk` and a path constructor identifying any two points. Encoded as the quotient of `A` by the
total relation. -/
def Trunc (A : Sort u) : Sort u := Quot (Trunc.total A)

namespace Trunc

/-- The point constructor of the truncation. -/
def mk {A : Sort u} (a : A) : Trunc A := Quot.mk _ a

/-- **The path constructor / defining higher property:** the truncation is a mere proposition.
Any two elements of `∥A∥` are equal. This is where the total relation (the path constructor)
is essential. -/
theorem isProp {A : Sort u} : IsProp (Trunc A) := by
  intro x y
  induction x using Quot.ind with
  | _ a =>
    induction y using Quot.ind with
    | _ b => exact Quot.sound trivial

/-- **Recursor** of the truncation into a mere proposition `P`. -/
def lift {A : Sort u} {P : Sort v} (hP : IsProp P) (f : A → P) : Trunc A → P :=
  Quot.lift f (fun a b _ => hP (f a) (f b))



/-- Functoriality: a map `A → B` lifts to `∥A∥ → ∥B∥`. -/
def map {A : Sort u} {B : Sort v} (f : A → B) : Trunc A → Trunc B :=
  lift isProp (fun a => mk (f a))


/-- **Universal property / idempotence on propositions.** If `A` is a mere proposition then the
point constructor `mk : A → ∥A∥` has a two-sided inverse, hence is an equivalence (it exhibits
`∥A∥` as logically equal to `A`). -/
def equivOfIsProp {A : Sort u} (hA : IsProp A) : Trunc A → A :=
  lift hA id




end Trunc

end HoTT


