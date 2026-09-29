-- Prove2me | solution 1 for C4FreeDiam2.kovari_sos_turan_cherry_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:48:15.053242+00:00
-- url     : https://prove2.me/submissions/2ef4e1d5-10e5-4960-9b6e-c02528aa1c2c

-- Sol generated from Novelty/C4FreeDiameter2.lean
import Mathlib
import Definitions.Def_Novelty_C4FreeDiameter2

/-!
# C4-free diameter-2 graphs: structural bounds toward a non-3-colorability conjecture

This file formalizes the structural setting of the research target

> *Any C4-free graph of diameter 2 without universal vertices and maximum degree
> at least 17 is not 3-colorable.*

We isolate the three governing hypotheses as `Prop`-valued predicates on a finite
simple graph `G`:

* `IsC4Free G` — no two distinct vertices have two distinct common neighbours
  (equivalently, `G` contains no 4-cycle `C₄`);
* `HasDiameter2 G` — every pair of distinct vertices is adjacent or has a common
  neighbour (diameter `≤ 2`);
* `NoUniversalVertex G` — no vertex is adjacent to every other vertex.

The full conjecture is recorded verbatim as `NonThreeColorabilityConjecture`
(a `Prop`; it is the open target and is *not* claimed here).  What we *prove* are
the fully-verified structural inequalities that any attack on the conjecture must
use:

* `moore_bound` — the **diameter-2 Moore bound** `|V| ≤ Δ² + 1`.
* `kovari_sos_turan_cherry_bound` — the **Kővári–Sós–Turán cherry inequality**
  `∑_v C(deg v, 2) ≤ C(|V|, 2)` for C4-free graphs.
* `maxDegree_add_two_le_card` — no-universal-vertex forces `Δ + 2 ≤ |V|`.

The bridge to 3-colorability lives in `C4FreeDiameter2Coloring.lean`.

-- !-- Lab Notes -- !--
**Hypothesis (Hypothesizer).** The three hypotheses pull in opposite directions.
Diameter 2 forces the graph to be *dense enough* (Moore bound is an upper cap on
`|V|` in terms of `Δ`), C4-freeness forces it to be *locally sparse* (the
neighbourhood of any vertex induces a matching, quantified by the cherry
inequality), and "no universal vertex" removes the trivial 3-colorable stars.
The conjecture asserts that once `Δ ≥ 17`, this tension makes the chromatic
number exceed 3.  A proof must control the independence number `α`, since
3-colorability is equivalent to `3·α ≥ |V|` failing.

**Experiment (Experimenter).** We proved the two classical counting bounds and
the elementary degree bound directly from the predicates.  The Moore bound is a
covering argument: every far vertex hangs off a neighbour of a fixed vertex `v`,
so `|V| ≤ 1 + Δ + Δ(Δ−1)`.  The cherry inequality is a genuine use of
C4-freeness: the map (centre, unordered pair of its neighbours) ↦ (unordered
pair) is injective, because two distinct centres for the same pair would be two
common neighbours, i.e. a `C₄`.

**Analysis (Analyst).** The Moore bound does *not* need C4-freeness — it is the
generic diameter-2 cap.  C4-freeness only bites through the cherry inequality,
which is why the sharp Moore graphs (Petersen, Hoffman–Singleton) are exactly the
C4-free diameter-2 graphs meeting `|V| = Δ² + 1`.  The genuinely open content of
the conjecture is the *lower* bound on the chromatic number, which is not a pure
counting fact and is deferred to future work.

**Critique (Critic).** Each theorem uses an insight-bearing technique (covering +
`Finset` fibre counting, an injective double count, an `erase`/`card` argument);
none is `decide`/`native_decide`/`rfl`. The predicates are faithful: `IsC4Free`
is stated as "at most one common neighbour", equivalent to the absence of a
`C₄`, and `HasDiameter2` is the standard "adjacent or a common neighbour".

**Synthesis (PI).** These are the reusable structural primitives for the
conjecture; the colorability reduction is built on top of them in the companion
file.
-/

open SimpleGraph Finset

open C4FreeDiam2

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]









open C4FreeDiam2 in
theorem solution(h : IsC4Free G) :
    ∑ v : V, (G.degree v).choose 2 ≤ (Fintype.card V).choose 2 := by
  have hL : ∑ v : V, (G.degree v).choose 2
      = ((univ : Finset V).sigma (fun v => (G.neighborFinset v).powersetCard 2)).card := by
    rw [Finset.card_sigma]
    simp [Finset.card_powersetCard, SimpleGraph.card_neighborFinset_eq_degree]
  have hRhs : (Fintype.card V).choose 2 = ((univ : Finset V).powersetCard 2).card := by
    rw [Finset.card_powersetCard]; simp [Finset.card_univ]
  rw [hL, hRhs]
  refine Finset.card_le_card_of_injOn (fun p => p.2) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_sigma] at hp
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨(Finset.mem_powersetCard.mp hp.2).1.trans (Finset.subset_univ _),
      (Finset.mem_powersetCard.mp hp.2).2⟩
  · intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_sigma] at hp hq
    obtain ⟨v, s⟩ := p; obtain ⟨w, t⟩ := q
    simp only at hpq
    subst hpq
    have hps := Finset.mem_powersetCard.mp hp.2
    have hqs := Finset.mem_powersetCard.mp hq.2
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hps.2
    have hav : G.Adj a v := ((G.mem_neighborFinset v a).mp (hps.1 (by simp))).symm
    have hbv : G.Adj b v := ((G.mem_neighborFinset v b).mp (hps.1 (by simp))).symm
    have haw : G.Adj a w := ((G.mem_neighborFinset w a).mp (hqs.1 (by simp))).symm
    have hbw : G.Adj b w := ((G.mem_neighborFinset w b).mp (hqs.1 (by simp))).symm
    have hvw : v = w := by
      have hv : v ∈ G.commonNeighbors a b := (G.mem_commonNeighbors).mpr ⟨hav, hbv⟩
      have hw : w ∈ G.commonNeighbors a b := (G.mem_commonNeighbors).mpr ⟨haw, hbw⟩
      exact h a b hab hv hw
    subst hvw; rfl
