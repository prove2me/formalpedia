-- Prove2me | Definitions.Def_Geometry_HadwigerDebrunner_HellyBridge
-- name    : Geometry_HadwigerDebrunner_HellyBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:17:25.914554+00:00
-- url     : https://prove2.me/theorems/42f2ae17-d1d5-440f-881c-33fe1343242b
-- title:
--   Aether Catalog definitions — Geometry_HadwigerDebrunner_HellyBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.HadwigerDebrunner.HellyBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/HadwigerDebrunner/HellyBridge.lean by skeleton subtraction
import Mathlib
/-
# Hadwiger–Debrunner `(p,q)` ↔ Helly: the dimension/convexity bridge

This file connects the *set-class agnostic* combinatorial skeleton of
`Combinatorial.lean` to genuine geometry, by feeding in a **Helly number** as the
sole geometric input.

The abstract reduction `pqProperty_helly_transversal_one` says: if a finite
family `F` has *Helly number* `h` (every `h`-wise intersecting family has a global
common point) and satisfies the `(h,h)`-property, then the whole family is pierced
by a **single point**.

We then instantiate the Helly number two ways:

* **Convex sets** in `ℝ^d`, where Helly's theorem (`Convex.helly_theorem`, from
  `Mathlib.Analysis.Convex.Radon`) gives Helly number `d+1`.  This yields
  `convex_pqProperty_transversal_one`, fully proved.
* **Convex splinters**, where the Arocha–Bracho–Montejano Helly theorem gives
  Helly number `2d+1`.  Since that splinter Helly theorem is not (yet) in Mathlib,
  `splinter_pqProperty_transversal_one` takes it as an explicit hypothesis,
  exhibiting precisely how the `2d+1` threshold plugs into the same machinery.

## Main results

* `HasHellyNumber` : the abstract "Helly number `h`" property of a single family.
* `pqProperty_helly_transversal_one` : Helly number `h` + `(h,h)`-property ⟹ transversal of size `1`.
* `convex_hasHellyNumber` : convex sets in `ℝ^d` (with `d+1 ≤ |s|`) have Helly number `d+1`.
* `convex_pqProperty_transversal_one` : convex `(d+1,d+1)`-family in `ℝ^d` ⟹ transversal of size `1`.
* `splinter_pqProperty_transversal_one` : the `2d+1` splinter analogue, parameterised by its Helly input.
-/


open Finset
open scoped Convex

/-!
This file is intentionally self-contained (it imports only `Mathlib`): it
re-declares the `(p,q)`-property and transversal predicates of
`Combinatorial.lean` so that the Helly bridge can be developed and checked in
isolation.  The definitions are *identical* to those in `Combinatorial.lean`.
-/

namespace HadwigerDebrunner

variable {ι X : Type*}

/-- The Hadwiger–Debrunner **`(p,q)`-property** (see `Combinatorial.lean`): among
every `p` members of the family, some `q` of them have a common point. -/
def HasPQProperty (s : Finset ι) (F : ι → Set X) (p q : ℕ) : Prop :=
  ∀ A ⊆ s, A.card = p → ∃ B ⊆ A, B.card = q ∧ (⋂ i ∈ B, F i).Nonempty

/-- A **transversal** (piercing set) of `F` over `s` (see `Combinatorial.lean`). -/
def IsTransversal (T : Finset X) (s : Finset ι) (F : ι → Set X) : Prop :=
  ∀ i ∈ s, ∃ t ∈ T, t ∈ F i

/-- The abstract **Helly number `h`** property of one fixed finite family `F`
over `s`: if every `h`-element subfamily has a common point, then so does the
whole family.  This is the only geometric input needed for the bridge below;
its value (`d+1` for convex sets, `2d+1` for convex splinters) records the
dimension and the geometry of the set class. -/
def HasHellyNumber (s : Finset ι) (F : ι → Set X) (h : ℕ) : Prop :=
  (∀ A ⊆ s, A.card = h → (⋂ i ∈ A, F i).Nonempty) → (⋂ i ∈ s, F i).Nonempty





end HadwigerDebrunner

-- !-- Lab Notes -- !--
/-
## Team loop for `HellyBridge.lean`

### Hypothesis (Hypothesizer)
If the combinatorial core of `Combinatorial.lean` is genuinely set-class
agnostic, then a *single* geometric input — a Helly number `h` — should suffice to
turn the `(h,h)`-property into a one-point transversal, uniformly for convex sets
(`h = d+1`) and for convex splinters (`h = 2d+1`, Arocha–Bracho–Montejano).  Bold
conjecture: the *same* abstract lemma, instantiated at two different Helly
numbers, recovers both the classical Helly threshold and the raised splinter
threshold without any change to the proof.

### Experiment (Experimenter)
* `HasHellyNumber s F h` abstracts “every `h`-wise intersecting subfamily forces a
  global common point” for one fixed family.
* `pqProperty_helly_transversal_one` : the abstract bridge.  Its core step shows
  that the `(h,h)`-property forces every `h`-subset of `s` to intersect (a
  `B ⊆ A` with `#B = #A = h` must equal `A`, by `Finset.eq_of_subset_of_card_le`),
  which is precisely the antecedent of `HasHellyNumber`; the resulting common
  point is a transversal of size `1`.
* `convex_hasHellyNumber` : convex sets in `EuclideanSpace ℝ (Fin d)` have Helly
  number `d+1`, obtained directly from Mathlib's `Convex.helly_theorem`
  (`Mathlib.Analysis.Convex.Radon`) using
  `finrank ℝ (EuclideanSpace ℝ (Fin d)) = d`.
* `convex_pqProperty_transversal_one` / `splinter_pqProperty_transversal_one` :
  the two instantiations, at `h = d+1` and `h = 2d+1`.
All compile with no `sorry`; the convex chain bottoms out in genuine Mathlib
convex geometry (only `propext`, `Classical.choice`, `Quot.sound`).

### Analysis (Analyst)
The conjecture held *exactly*: the splinter corollary is the convex corollary
with `d+1` replaced by `2d+1` and the Mathlib Helly call replaced by a hypothesis
`hHelly`.  The splinter Helly theorem (Helly number `2d+1`) is not in Mathlib and
requires the precise Arocha–Bracho–Montejano definition of a *convex splinter*,
so we expose it as an explicit hypothesis rather than fabricate a definition.
The nonemptiness hypothesis `s.Nonempty` turned out to be unnecessary (the empty
family is pierced vacuously), so it was dropped, sharpening the statements.

### Critique (Critic)
The convex corollary is **not** a mere restatement of Helly: it converts Helly's
*global intersection* conclusion into the `(p,q)`-language transversal of size
`1`, via the abstract bridge, and it is non-vacuous (a family of `≥ d+1` equal
nonempty convex sets satisfies the `(d+1,d+1)`-property).  The splinter corollary
is honestly *conditional* on the Arocha–Bracho–Montejano Helly number; it is not
proved from thin air, and the `2d+1` threshold is the only thing that changes —
exactly the point the mission asks us to exhibit.  No theorem here is closed by a
bare `simp`/`decide`.

### Synthesis (PI)
`combinatorial core × (one Helly number)` is the right factorisation of the
`(p,q)`-to-transversal passage at the Helly threshold.  The unproved deep content
is (a) the dimension-independent bound `N(d,p,q)` for `p > q`, and (b) the
splinter Helly theorem itself; both are recorded in `FUTURE_DIRECTIONS.md`.
-/


