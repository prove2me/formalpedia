-- Prove2me | Definitions.Def_Novelty_AFLMatching_Basic
-- name    : Novelty_AFLMatching_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T13:59:03.320504+00:00
-- url     : https://prove2.me/theorems/39f4b05b-eb1e-4ea3-a50f-8754fbb7f71e
-- title:
--   Aether Catalog definitions — Novelty_AFLMatching_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AFLMatching.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AFLMatching/Basic.lean by skeleton subtraction
import Mathlib

/-!
# Monochromatic matchings in colored uniform hypergraphs — Basic theory

This file develops the rigorous combinatorial core behind the *Alon–Frankl–Lovász
(AFL) matching bound* for "random-like" (bounded-degree / pseudorandom) hypergraphs.

We model a hypergraph as its edge set `H : Finset (Finset V)`, a *matching* as a
collection of pairwise-disjoint edges, and an `r`-edge-colouring as a function
`c : Finset V → Fin r`.

The two foundational results proved here are:

* `IsMatching.exists_mono_of_card` — **pigeonhole on a matching**: every `r`-colouring
  of a matching `M` contains a monochromatic sub-matching `M'` with `r * #M' ≥ #M`.
* `MaximalMatching.isCover` — **maximal matchings are vertex covers**: the union of
  the edges of a maximal matching meets every edge of the host hypergraph.

These feed (in `Bounds.lean`) into a clean lower bound on the size of a guaranteed
monochromatic matching in terms of the number of edges and the maximum degree.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The classical AFL/Cockayne–Lorimer style monochromatic
matching guarantee for the *complete* hypergraph should already, in weak form, follow
from purely local data (edge count + maximum degree), with no completeness/pseudorandom
structure beyond bounded degree.  We test: "bounded degree alone forces a large
monochromatic matching".

Experiment (Experimenter): Formalize matchings, the maximal-matching-is-a-cover lemma,
and the colour pigeonhole.  Both are fully provable in Lean with no `sorry`.

Analysis (Analyst): The bounded-degree route yields the fraction `1/(r·t·Δ_norm)`,
i.e. asymptotically `n/(r·t)` for a `d`-regular-like host.  This is genuinely weaker
than the AFL target `n/(r+t-1)` — the gap `(r-1)(t-1) ≥ 0` (see `Bounds.lean`).  So
"bounded degree alone" is TRUE but NOT TIGHT; the AFL constant needs the global
LP/strip structure of the host.  Distinguishes "true but not the deep bound".

Critique (Critic): The cover lemma needs edges to be nonempty (else a maximal matching's
union could miss an empty edge); we carry `t`-uniformity / nonemptiness explicitly.

Synthesis (PI): Keep the two structural lemmas general (any vertex type, any matching),
defer the numeric assembly to `Bounds.lean`.
-/

namespace AFLMatching

open Finset

variable {V : Type*} [DecidableEq V]

/-- A finset of edges is a **matching** if its members are pairwise disjoint. -/
def IsMatching (M : Finset (Finset V)) : Prop :=
  ∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → Disjoint e f

/-
Any subset of a matching is a matching.
-/

/-
The empty collection is a matching.
-/

/-
**Pigeonhole on a matching.** Any `r`-colouring `c` of the edges of a matching `M`
admits a colour `i` whose colour class is a (mono-coloured) matching `M'` with
`r * #M' ≥ #M`.  Equivalently `M` contains a monochromatic matching of size at least
`#M / r`.
-/

/-- The set of vertices covered by a collection of edges. -/
def support (M : Finset (Finset V)) : Finset V := M.biUnion id

/-- A matching `M ⊆ H` is **maximal** in `H` if every edge of `H` that is disjoint from
all edges of `M` already belongs to `M` (so no further edge can be added). -/
def MaximalMatching (H M : Finset (Finset V)) : Prop :=
  M ⊆ H ∧ IsMatching M ∧ ∀ e ∈ H, (∀ f ∈ M, Disjoint e f) → e ∈ M

/-
**Maximal matchings are vertex covers.** If `M` is a maximal matching of `H` and all
edges of `H` are nonempty, then every edge of `H` shares a vertex with `support M`.
-/

/-
A matching of maximum cardinality among sub-matchings of `H` is a maximal matching.
-/

end AFLMatching


