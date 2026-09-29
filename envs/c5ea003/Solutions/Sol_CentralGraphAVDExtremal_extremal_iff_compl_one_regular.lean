-- Prove2me | solution 1 for CentralGraphAVDExtremal.extremal_iff_compl_one_regular
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:56:55.327548+00:00
-- url     : https://prove2.me/submissions/1ae63e60-d827-4175-ab93-1df178cd07fb

-- Sol generated from Novelty/CentralGraphAVDExtremal.lean
import Mathlib
import Definitions.Def_Novelty_CentralGraphAVDExtremal

/-!
# The extremal regime of AVD‑total colourings of central graphs of regular graphs

For a `d`‑regular graph `G` that is not complete, the **central graph** `C(G)`
(subdivide every edge, join every non‑adjacent pair) satisfies two lower bounds on
its adjacent‑vertex‑distinguishing (AVD) total chromatic number:

* a `d`‑governed bound  `χ''ₐ(C(G)) ≥ d + 3`, and
* a `|V|`‑governed bound `χ''ₐ(C(G)) ≥ |V(G)| + 1`   (every original vertex of
  `C(G)` has degree `|V(G)| − 1`).

Because a non‑complete `d`‑regular graph always has `|V(G)| ≥ d + 2`, the
`|V|`‑bound is **at least as strong** as the `d`‑bound, and the two coincide
*exactly* in the **extremal regime** `|V(G)| = d + 2`.

This file isolates and characterises that extremal regime, continuing the theory
developed for the central graph.  The main results are:

* `compl_isRegular` : the complement of a `d`‑regular graph on `n` vertices is
  `(n − 1 − d)`‑regular.
* `extremal_iff_compl_one_regular` : for a `d`‑regular non‑complete graph,
  `|V(G)| = d + 2` **iff** the complement is `1`‑regular (a perfect matching); i.e.
  the extremal graphs are precisely `K_{d+2}` minus a perfect matching (the
  cocktail‑party graphs).
* `dbound_le_cardbound` : `d + 3 ≤ |V(G)| + 1`, so the `|V|`‑bound dominates.
* `bounds_agree_iff_extremal` : the two bounds are **equal** iff `|V(G)| = d + 2`.
* `central_degree_inl_extremal` : in the extremal case every original vertex of
  `C(G)` has degree `d + 1`.
* `extremal_avd_ge` : in the extremal case every AVD total colouring of `C(G)` uses
  at least `|V(G)| + 1 = d + 3` colours — the two bounds collapse to a single sharp
  value.
* `cycleGraph_four_extremal` / `cycle4_avd_ge_four` : the `4`‑cycle `C₄` is the
  smallest extremal instance (`d = 2`, `|V| = 4`, complement `= 2K₂`), and its
  central graph needs at least `4` colours; while the `5`‑cycle is **not** extremal
  (`5 > 4`), witnessing the strictness of `dbound_le_cardbound`.

## Set‑up (recalled, self‑contained)

A *total colouring* of a finite simple graph `H` is modelled as a proper vertex
colouring of the **total graph** `T(H)` on `V(H) ⊕ E(H)`; it is **AVD** when
adjacent vertices receive distinct colour sets
`C(w) = {colour w} ∪ {colour e : e ∋ w}`.
-/

open SimpleGraph Finset

open CentralGraphAVDExtremal

/-! ## The total graph `T(H)` and total colourings -/


variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]





/-! ### The star clique -/





/-! ### Colour sets and AVD total colourings -/

variable {κ : Type*} [DecidableEq κ]






/-! ### Padding the palette preserves AVD -/



/-! ## The central graph `C(G)` -/


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]







/-! ## Regular graphs: the `d + 3` lower bound (recalled) -/

/-- **Structural fact.** A `d`-regular graph that is not complete has at least
`d + 2` vertices. -/
theorem card_ge_of_regular_not_complete {d : ℕ} (hreg : G.IsRegularOfDegree d)
    (a b : V) (hne : a ≠ b) (hnadj : ¬ G.Adj a b) : d + 2 ≤ Fintype.card V := by
  have hcard : (insert a (insert b (G.neighborFinset a))).card = d + 2 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_neighborFinset_eq_degree, hreg a]
    · simp only [mem_neighborFinset]; exact fun h => hnadj h
    · simp only [mem_insert, mem_neighborFinset]
      push_neg
      exact ⟨hne, fun h => (SimpleGraph.irrefl G) h⟩
  calc d + 2 = (insert a (insert b (G.neighborFinset a))).card := hcard.symm
    _ ≤ Fintype.card V := card_le_univ _




/-! ## The extremal regime `|V| = d + 2`

The two lower bounds `d + 3` and `|V| + 1` are related by `card_ge`, and coincide
exactly when `|V| = d + 2`.  We characterise this extremal regime and record the
sharp consequence for `C(G)`.
-/

/-- **Complement of a regular graph is regular.** If `G` is `d`-regular on `n`
vertices then its complement is `(n − 1 − d)`-regular. -/
theorem compl_isRegular {d : ℕ} (hreg : G.IsRegularOfDegree d) :
    Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - d) := by
  intro v
  rw [degree_compl, hreg v]







/-! ## Concrete instances: the smallest extremal cycle `C₄` versus `C₅` -/










/-!
-- !-- Lab Notes -- !--

**Hypothesis.** The guiding conjecture `χ''ₐ(C(G)) = d + 3` for `d`-regular
non-complete `G` can only be an equality in a restricted regime, because the
`|V|`-governed bound `χ''ₐ(C(G)) ≥ |V(G)| + 1` already dominates the `d`-governed
bound `≥ d + 3`.  We hypothesised that the exact boundary is `|V(G)| = d + 2`, and
that these extremal graphs are precisely the cocktail-party graphs `K_{d+2}` minus
a perfect matching.

**Experiment.** We reproduced the self-contained total-graph/AVD machinery and both
lower bounds, then added: (i) `compl_isRegular`, the complement-degree computation;
(ii) `extremal_iff_compl_one_regular`, the characterisation `|V| = d + 2 ↔` the
complement is `1`-regular; (iii) `dbound_le_cardbound` and
`bounds_agree_iff_extremal`, locating exactly where the two bounds coincide; and
(iv) `extremal_avd_ge`, the sharp lower bound on the extremal family.  We tested the
theory on concrete cycles: `C₄` (extremal) and `C₅` (non-extremal).

**Analysis.** The characterisation is clean and reduces to a single
nat-arithmetic identity `n − 1 − d = 1 ⟺ n = d + 2` once the complement-degree
formula is in place; the non-triviality is entirely in `card_ge`, the
non-complete-regular vertex count, and in the degree structure of `C(G)`.  `C₄`
is the smallest extremal instance: its complement is `2K₂`, a perfect matching,
exactly as predicted.  `C₅` fails extremality (`5 ≠ 4`), and there the `|V|`-bound
(`6`) strictly beats the `d`-bound (`5`) — the concrete witness of why the naive
`d + 3` equality is false off the extremal family.

**Critique.** No result is vacuous: each main theorem is a genuine biconditional or
strict inequality with insight-bearing proofs (`omega`, `by_contra`, palette
padding, `fin_cases`/`decide` on concrete graphs).  The extremal characterisation
is stated with the necessary non-completeness witness `(a, b)`; dropping it would
make the statement false for complete graphs (where the `d`-bound argument breaks).

**Synthesis.** The extremal regime `|V| = d + 2` is now fully characterised as the
cocktail-party family, and the sharp lower bound `χ''ₐ(C(G)) ≥ d + 3 = |V| + 1`
is established there.  The remaining gap is the matching upper bound on this
family — a concrete `(d+3)`-colouring — recorded in `FUTURE_DIRECTIONS.md`.
-/
open CentralGraphAVDExtremal in
theorem solution{d : ℕ} (hreg : G.IsRegularOfDegree d)
    (a b : V) (hne : a ≠ b) (hnadj : ¬ G.Adj a b) :
    Fintype.card V = d + 2 ↔ Gᶜ.IsRegularOfDegree 1 := by
  have hge : d + 2 ≤ Fintype.card V := card_ge_of_regular_not_complete G hreg a b hne hnadj
  constructor
  · intro hcard
    have hcr := compl_isRegular G hreg
    rw [hcard] at hcr
    have e : d + 2 - 1 - d = 1 := by omega
    rwa [e] at hcr
  · intro h1
    have hcr := compl_isRegular G hreg a
    have h1a := h1 a
    have : Fintype.card V - 1 - d = 1 := by rw [← hcr]; exact h1a
    omega
