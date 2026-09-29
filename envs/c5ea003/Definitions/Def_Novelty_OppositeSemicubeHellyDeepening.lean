-- Prove2me | Definitions.Def_Novelty_OppositeSemicubeHellyDeepening
-- name    : Novelty_OppositeSemicubeHellyDeepening
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:34:36.301767+00:00
-- url     : https://prove2.me/theorems/5bb94ac1-1080-432f-98d0-bf279cfb6774
-- title:
--   Aether Catalog definitions — Novelty_OppositeSemicubeHellyDeepening
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.OppositeSemicubeHellyDeepening`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/OppositeSemicubeHellyDeepening.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Deepening: canonical matchings, parity, and the finite-family product law
for the opposite-semicube Helly property

This development deepens the theory of the **opposite-semicube Helly property** of
partial cubes.  A partial cube is an isometric subgraph of a hypercube; in the
coordinate model a vertex of the hypercube on coordinate set `α` is a sign vector
`α → Bool`, a partial cube is a finite set `V : Finset (α → Bool)`, and the
*semicube* of coordinate `i` with sign `b` is `{v ∈ V | v i = b}`.  Two structural
notions organise the theory:

* **Harmonic-evenness** — every coordinate (Θ-class) splits `V` into two
  equal-sized opposite semicubes; the exact discrete analogue of a mean-value
  (harmonic) symmetry.
* **The opposite-semicube Helly property** — for every coordinate the two opposite
  semicubes admit a matching (a bijection); a Hall/transversal-type condition.

The base characterisation `OppositeSemicubeHelly V ↔ HarmonicEven V` (a matching of
a cut exists iff its two sides are equinumerous) and the *binary* product law are
recorded in the companion development; here we build three deeper layers.

## 1. A canonical matching from antipodal symmetry

The Helly property only asserts *existence* of a matching.  We exhibit a canonical
one whenever the vertex set is closed under the coordinatewise complement (the
antipodal involution `v ↦ ¬ v`): the complement maps each semicube bijectively
onto its opposite.  This upgrades the existence statement to an explicit,
involutive system of representatives and proves harmonic-evenness constructively
(`antipodalClosed_harmonicEven`).

## 2. Parity of the vertex count

Harmonic-evenness forces an even number of vertices, since a single balanced cut
partitions the vertices into two equinumerous halves (`harmonicEven_even_card`).
As boundary cases, a single vertex is never harmonic-even
(`not_harmonicEven_singleton`) while the full hypercube always is
(`harmonicEven_univ`).

## 3. The finite-family product law

The central result generalises the binary product law to an **arbitrary finite
family** of partial cubes indexed by a finite type `ι`.  The product cube lives on
the disjoint union `Σ k, β k` of coordinate sets, and its `⟨k, i⟩`-semicube has
cardinality `|Semicube (V k) i c| · ∏_{j ≠ k} |V j|`.  Cancelling the (positive,
by nonemptiness) product factor yields:

* `harmonicEven_piCube` — the family product is harmonic-even iff every factor is;
* `oppositeSemicubeHelly_piCube` — the family product satisfies the
  opposite-semicube Helly property iff every factor is harmonic-even.

The binary theorem is the special case `ι = Bool`.

## References

* Djoković–Winkler theory of Θ-classes and semicubes of partial cubes.
* Polat's theorems on Helly properties in partial cubes.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The binary product law is the shadow of a fully
multiplicative law over finite families; moreover the mere *existence* of cut
matchings hides a canonical, symmetry-induced matching whenever the cube is
antipodally closed.  Bold form: harmonic-evenness is exactly the "each cut halves
the mass" condition and is therefore simultaneously a parity constraint and a
product-stable invariant.

Experiment (Experimenter): Model the family product on `Σ k, β k` via the merge
map `f ↦ (fun s => f s.1 s.2)`, injective by extensionality.  The one-coordinate
slice of `Fintype.piFinset V` is again a `piFinset` with the `k`-th factor
replaced by its semicube (`Function.update`), so `Fintype.card_piFinset` together
with `Finset.prod_update_of_mem` yield the product cardinality formula.  Positivity
of `∏_{j ≠ k} |V j|` (all factors nonempty) licenses cancellation.

Analysis (Analyst): Harmonic-evenness is (a) coordinate-local, (b) multiplicative
across products, (c) a parity obstruction, and (d) automatic under antipodal
closure.  Nonemptiness of every factor is load-bearing exactly at the cancellation
step; the antipodal route needs no nonemptiness because it builds the bijection
directly.

Critique (Critic): None of the results are definitional.  The product law needs
genuine cancellation of a positive natural-number product; the parity result uses
the disjoint two-block decomposition of a cut; the antipodal matching is a real
involution, not a renaming.  The binary theorem is recovered as an instance, so
the family law strictly extends the earlier development.

Synthesis (PI): The opposite-semicube Helly property is governed by a single
harmonic-balance invariant that is at once local, multiplicative,
parity-constraining, and symmetry-canonical; see `FUTURE_DIRECTIONS.md`.
-/

open Finset

namespace OSHDeepening

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Base notions -/

/-- The **semicube** of coordinate `i` with sign `b`: the vertices of `V` whose
`i`-th coordinate equals `b`. -/
def Semicube (V : Finset (α → Bool)) (i : α) (b : Bool) : Finset (α → Bool) :=
  V.filter (fun v => v i = b)

/-- A coordinate `i` is **balanced** in `V` if its two opposite semicubes are
equinumerous. -/
def Balanced (V : Finset (α → Bool)) (i : α) : Prop :=
  (Semicube V i true).card = (Semicube V i false).card

/-- `V` is **harmonic-even** if every coordinate splits `V` into two equal-sized
opposite semicubes. -/
def HarmonicEven (V : Finset (α → Bool)) : Prop := ∀ i, Balanced V i

/-- The **opposite-semicube Helly property**: for every coordinate the two opposite
semicubes admit a matching (a bijection between them). -/
def OppositeSemicubeHelly (V : Finset (α → Bool)) : Prop :=
  ∀ i, Nonempty (↥(Semicube V i true) ≃ ↥(Semicube V i false))


/-! ### Layer 1: canonical matching from antipodal symmetry -/

/-- The coordinatewise complement (antipodal involution) on sign vectors. -/
def antipode (v : α → Bool) : α → Bool := fun i => !(v i)



/-- A vertex set is **antipodally closed** if it is stable under the coordinatewise
complement. -/
def AntipodalClosed (V : Finset (α → Bool)) : Prop :=
  ∀ v ∈ V, antipode v ∈ V





/-! ### Layer 2: parity of the vertex count -/



/-! ### Layer 3: the finite-family product law -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {β : ι → Type*} [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)]

/-- The merge map assembling a family of sign vectors into a single sign vector on
the disjoint union `Σ k, β k` of coordinate sets. -/
def mergePi (f : ∀ k, β k → Bool) : (Σ k, β k) → Bool := fun s => f s.1 s.2


/-- The **finite-family Cartesian product** of partial cubes, realised on the
disjoint-union coordinate set `Σ k, β k`. -/
def piCube (V : ∀ k, Finset (β k → Bool)) : Finset ((Σ k, β k) → Bool) :=
  (Fintype.piFinset V).image mergePi





end OSHDeepening


