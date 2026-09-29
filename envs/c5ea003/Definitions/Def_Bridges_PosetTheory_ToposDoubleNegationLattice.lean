-- Prove2me | Definitions.Def_Bridges_PosetTheory_ToposDoubleNegationLattice
-- name    : Bridges_PosetTheory_ToposDoubleNegationLattice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:33:03.947881+00:00
-- url     : https://prove2.me/theorems/c2d3d8bf-7252-4221-8991-60b418c1bf34
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_ToposDoubleNegationLattice
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.ToposDoubleNegationLattice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/ToposDoubleNegationLattice.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_KnasterTarskiBridge
/-! # The Subobject Lattice of a Topos: Double Negation as a Nucleus

This file is the **logic ↔ topology** facet of the category-theory bridge.

## The corrected grand claim

The mission statement asks to "prove that every Grothendieck topos is a bounded
lattice with a universal property".  Taken literally this is **false**: a
Grothendieck topos is a *category* (e.g. `Set`), not a lattice, and it is rarely
a poset at all.  The true and load-bearing statement is:

> In any (Grothendieck) topos, the **subobjects of a fixed object** form a
> complete Heyting algebra (equivalently a *frame*): a bounded, distributive
> lattice whose meet `⊓` has a right adjoint `⇨` (Heyting implication) — and that
> adjunction *is* the universal property.

We model the subobject lattice abstractly by `Order.Frame α` (a complete Heyting
algebra), the algebraic skeleton common to:
* **topology**: `TopologicalSpace.Opens X`, the frame of opens — the subobject
  lattice of the terminal sheaf on `X` (instantiated explicitly at the end);
* **logic**: the Lindenbaum–Tarski algebra of intuitionistic propositional logic;
* the subobject classifier `Ω` of any topos, internalized.

## What we prove

* `himp_isGreatest` — the **universal property**: `a ⇨ c` is the *greatest* `x`
  with `a ⊓ x ≤ c`.  Meet is left adjoint to implication.
* `dneg` (double negation `a ↦ aᶜᶜ`) is a **nucleus / closure operator**:
  extensive (`le_dneg`), monotone (`dneg_monotone`), idempotent (`dneg_idem`),
  and meet-preserving (`dneg_inf`).  This is the *double-negation topology* whose
  sheaves are Boolean — the categorical heart of the double-negation translation.
* `dneg_bot`, `dneg_top` — the bounds are regular, so the lattice of regular
  elements is itself bounded.
* `IsRegular` elements are closed under `⊓` (`isRegular_inf`).
* **Catalog bridge**: using `KnasterTarskiBridge` from the attached catalog we
  identify the least and greatest fixed points of the nucleus: the least fixed
  point is `⊥` (`lfp_dneg_eq_bot`) and the greatest is `⊤` (`gfp_dneg_eq_top`),
  realizing `dneg` inside the Knaster–Tarski fixed-point machinery.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer): "Every Grothendieck topos is a bounded lattice with a
  universal property."  Bold but, as literally stated, suspicious — a topos is a
  category.  Refined conjecture: the subobject lattice is a complete Heyting
  algebra and double negation is a closure operator (a Lawvere–Tierney topology).
EXPERIMENT (Experimenter): Disproof of the literal claim is immediate (`Set` is
  not a poset).  Proved the refined claim over `Order.Frame`: the himp universal
  property, and that `aᶜᶜ` is extensive/monotone/idempotent/meet-preserving.
  Linked to the catalog Knaster–Tarski file to pin the nucleus' fixed points.
ANALYSIS (Analyst): The failure of the literal statement is a *category error*
  ("topos" vs. "its subobject lattice"); the surviving content is sharper and
  genuinely cross-domain (`Opens X` is an instance).  Idempotence `aᶜᶜᶜᶜ = aᶜᶜ`
  reduces to the triple-negation law `aᶜᶜᶜ = aᶜ`, the one nontrivial Heyting
  identity here.  Meet-preservation `(a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ` is what makes the
  regular elements a sublattice (in fact a Boolean algebra).
CRITIQUE (Critic): Care needed: `dneg` is NOT join-preserving and `aᶜᶜ = a`
  fails intuitionistically, so we never assume Booleanness.  The fixed-point
  identifications must use `le_dneg`/`dneg_bot`, not classical `compl_compl`.
SYNTHESIS (PI): The bridge is "intuitionistic logic = internal language of a
  topos = frame structure on subobjects", with `Opens X` the topological witness.
-/

open CategoryTheory KnasterTarskiBridge

namespace ToposDoubleNegationLattice

universe u

variable {α : Type u} [Order.Frame α]

/-! ## Section 1 — The universal property of the subobject lattice -/


/-! ## Section 2 — Double negation is a nucleus (closure operator) -/

/-- The double-negation operator `a ↦ aᶜᶜ` on the subobject lattice. -/
def dneg (a : α) : α := aᶜᶜ







/-! ## Section 3 — Regular elements form a bounded sub-meet-lattice -/

/-- A subobject is **regular** (a `¬¬`-sheaf / `¬¬`-stable element) when it is a
fixed point of double negation. -/
def IsRegular (a : α) : Prop := dneg a = a




/-! ## Section 4 — Catalog bridge: the nucleus inside Knaster–Tarski

We feed the monotone nucleus `dneg` into the attached
`Catalog/Bridges/KnasterTarskiBridge.lean` machinery and identify its extremal
fixed points. -/




/-! ## Section 5 — The topological witness: the frame of opens

Everything above instantiates at `TopologicalSpace.Opens X`, the subobject
lattice of the terminal object in the sheaf topos `Sh(X)`. This is the concrete
**topology** end of the bridge. -/

section Opens
variable {X : Type u} [TopologicalSpace X]




end Opens

end ToposDoubleNegationLattice


