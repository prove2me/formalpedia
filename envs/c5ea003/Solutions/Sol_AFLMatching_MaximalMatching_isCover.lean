-- Prove2me | solution 1 for AFLMatching.MaximalMatching.isCover
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T16:42:17.817693+00:00
-- url     : https://prove2.me/submissions/506c4f7c-a06d-4471-80d7-7cf870b03b6b

-- Sol generated from Novelty/AFLMatching/Basic.lean
import Mathlib
import Definitions.Def_Novelty_AFLMatching_Basic

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

open AFLMatching

open Finset

variable {V : Type*} [DecidableEq V]


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



/-
**Maximal matchings are vertex covers.** If `M` is a maximal matching of `H` and all
edges of `H` are nonempty, then every edge of `H` shares a vertex with `support M`.
-/

/-
A matching of maximum cardinality among sub-matchings of `H` is a maximal matching.
-/


open AFLMatching in
theorem solution{H M : Finset (Finset V)} (hmax : MaximalMatching H M)
    (hne : ∀ e ∈ H, e.Nonempty) :
    ∀ e ∈ H, ∃ v ∈ support M, v ∈ e := by
  intro e he;
  -- By cases on whether e is disjoint from every f ∈ M.
  by_cases h_disjoint : ∀ f ∈ M, Disjoint e f;
  · exact Exists.elim ( hne e he ) fun x hx => ⟨ x, Finset.mem_biUnion.mpr ⟨ e, hmax.2.2 e he h_disjoint, hx ⟩, hx ⟩;
  · simp_all +decide [ Finset.disjoint_left ];
    obtain ⟨ x, hx, y, hy, hyx ⟩ := h_disjoint; exact ⟨ y, Finset.mem_biUnion.2 ⟨ x, hx, hyx ⟩, hy ⟩ ;
