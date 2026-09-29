-- Prove2me | Definitions.Def_Geometry_HadwigerDebrunner_Combinatorial
-- name    : Geometry_HadwigerDebrunner_Combinatorial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:17:20.734628+00:00
-- url     : https://prove2.me/theorems/e9f24b06-9fa6-4ed6-ba6c-6e664f9e2900
-- title:
--   Aether Catalog definitions — Geometry_HadwigerDebrunner_Combinatorial
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.HadwigerDebrunner.Combinatorial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/HadwigerDebrunner/Combinatorial.lean by skeleton subtraction
import Mathlib
/-
# Hadwiger–Debrunner `(p,q)`-property: the combinatorial core

This file develops the *set-class agnostic* combinatorial skeleton underlying the
Hadwiger–Debrunner `(p,q)` transversal theory.  Nothing here depends on convexity
or on a dimension: we work with an arbitrary finite family `F : ι → Set X`
indexed by a `Finset s`, and isolate exactly the combinatorial content of the
`(p,q)`-property and of *transversals* (piercing sets).

The two genuinely combinatorial facts proved here are:

* monotonicity of the `(p,q)`-property (strengthen `p`, weaken `q`); and
* the elementary transversal bound coming from the *full* `(|s|, q)`-property:
  if some `q` members share a point, that single point pierces all `q` of them,
  so the whole family is pierced by `|s| - q + 1` points.

These are the ingredients that are *independent of the Helly number*; the
Helly-number input (which is where dimension and the convex-vs-splinter
distinction enters, `d+1` vs `2d+1`) is supplied in `HellyBridge.lean`.

## Main results

* `HasPQProperty.strengthen_p` : the `(p,q)`-property implies the `(p',q)`-property for `p ≤ p'`.
* `HasPQProperty.weaken_q`     : the `(p,q)`-property implies the `(p,q')`-property for `q' ≤ q`.
* `exists_transversal_of_nonempty` : every family of nonempty sets has a transversal of size `≤ |s|`.
* `exists_transversal_of_pqProperty_full` : the `(|s|, q)`-property yields a transversal of size `≤ |s| - q + 1`.
-/


open Finset

namespace HadwigerDebrunner

variable {ι X : Type*}

/-- The Hadwiger–Debrunner **`(p,q)`-property** for a finite family `F` indexed by
`s`: among every `p` members of the family, some `q` of them have a common point. -/
def HasPQProperty (s : Finset ι) (F : ι → Set X) (p q : ℕ) : Prop :=
  ∀ A ⊆ s, A.card = p → ∃ B ⊆ A, B.card = q ∧ (⋂ i ∈ B, F i).Nonempty

/-- A **transversal** (a.k.a. piercing set) of the family `F` over `s`: a finite
set `T` of points such that every member `F i` (`i ∈ s`) contains a point of `T`. -/
def IsTransversal (T : Finset X) (s : Finset ι) (F : ι → Set X) : Prop :=
  ∀ i ∈ s, ∃ t ∈ T, t ∈ F i

/-
Strengthening `p`: the `(p,q)`-property implies the `(p',q)`-property whenever
`p ≤ p'`.  (Among every `p'` members, look at any `p` of them.)
-/

/-
Weakening `q`: the `(p,q)`-property implies the `(p,q')`-property whenever
`q' ≤ q`.  (A common point of `q` sets is a common point of any `q'` of them.)
-/

/-
A family of nonempty sets always has a transversal of size at most `|s|`:
pick one point from each member.
-/


end HadwigerDebrunner

-- !-- Lab Notes -- !--
/-
## Team loop for `Combinatorial.lean`

### Hypothesis (Hypothesizer)
The Hadwiger–Debrunner `(p,q)` theorem is usually presented as one monolithic
statement entangling combinatorics (the `(p,q)`-property and transversals) with
deep geometry (fractional Helly, LP duality in the Alon–Kleitman proof).  Bold
conjecture: the *combinatorial* layer is entirely independent of dimension and of
the set class (convex vs. splinter), and can be isolated and proved on its own
with elementary tools, leaving the geometry to enter through a single scalar — a
Helly number.

### Experiment (Experimenter)
We formalised the `(p,q)`-property (`HasPQProperty`) and transversals
(`IsTransversal`) over an arbitrary family `F : ι → Set X` indexed by a `Finset`.
We then attempted four claims:
* `HasPQProperty.strengthen_p` — monotone in `p` (look at any `p` of the `p'`).
* `HasPQProperty.weaken_q`     — monotone in `q` (a common point of `q` sets is
  common to any `q'` of them).
* `exists_transversal_of_nonempty` — choice function over `s.attach`.
* `exists_transversal_of_pqProperty_full` — the headline elementary bound
  `τ ≤ |s| - q + 1` obtained by piercing the `q`-wise common members with one
  point and the rest individually (reusing `exists_transversal_of_nonempty` on
  the complement `s \ B`).
All four compile with no `sorry` and only the standard axioms.

### Analysis (Analyst)
Everything in this file is *true and easy* once stated over `Finset`-indexed
families; the truncated natural subtraction in the bound even let us drop the
hypothesis `q ≤ |s|` (it is automatically correct).  The genuinely hard,
dimension-dependent content does **not** live here — it lives in the Helly number,
which is exactly what `HellyBridge.lean` supplies.  The structural pattern: the
`(p,q)` theory factors as `combinatorics × (one Helly number)`.

### Critique (Critic)
None of the four results is vacuous: each is a universally quantified implication
with satisfiable hypotheses (e.g. take all `F i` equal to one fixed nonempty
set).  None is closed by a single `simp`/`decide`: the proofs use `induction`-free
but genuine steps — `Finset.exists_subset_card_eq`, antitone `biInter`, classical
choice over `attach`, and a `card_sdiff`/`omega` cardinality calculation.  The
bound `|s| - q + 1` is *not* the dimension-independent bound `N(d,p,q)` of the
full theorem; it depends on `|s|`.  Closing that gap is the deep open part and is
recorded in `FUTURE_DIRECTIONS.md`.

### Synthesis (PI)
This file is the reusable, set-class agnostic core.  `HellyBridge.lean` plugs in
the Helly number `d+1` (convex, via Mathlib's `Convex.helly_theorem`) and `2d+1`
(splinter, via Arocha–Bracho–Montejano) to obtain genuine geometric corollaries.
-/


