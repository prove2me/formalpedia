-- Prove2me | solution 1 for C4FreeDiam2.moore_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:48:25.722763+00:00
-- url     : https://prove2.me/submissions/37f2752e-f3cd-4894-9b64-316eca90605b

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
theorem solution(h : HasDiameter2 G) :
    Fintype.card V ≤ G.maxDegree ^ 2 + 1 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [Fintype.card_eq_zero]
  · obtain ⟨v⟩ := hV
    set Δ := G.maxDegree with hΔ
    set R : Finset V := univ.filter (fun w => w ≠ v ∧ ¬ G.Adj v w) with hR
    have hRsub : R ⊆ (G.neighborFinset v).biUnion (fun u => G.neighborFinset u \ {v}) := by
      intro w hw
      rw [hR, Finset.mem_filter] at hw
      obtain ⟨-, hwv, hnadj⟩ := hw
      rcases h v w (fun e => hwv e.symm) with hadj | hne
      · exact absurd hadj hnadj
      · obtain ⟨u, hu⟩ := hne
        rw [SimpleGraph.mem_commonNeighbors] at hu
        rw [Finset.mem_biUnion]
        refine ⟨u, (G.mem_neighborFinset v u).mpr hu.1, ?_⟩
        rw [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨(G.mem_neighborFinset u w).mpr hu.2.symm, hwv⟩
    have hRcard : R.card ≤ Δ * (Δ - 1) := by
      calc R.card ≤ ((G.neighborFinset v).biUnion (fun u => G.neighborFinset u \ {v})).card :=
              Finset.card_le_card hRsub
        _ ≤ ∑ u ∈ G.neighborFinset v, (G.neighborFinset u \ {v}).card := Finset.card_biUnion_le
        _ ≤ ∑ u ∈ G.neighborFinset v, (Δ - 1) := by
              apply Finset.sum_le_sum
              intro u hu
              have huv : G.Adj v u := (G.mem_neighborFinset v u).mp hu
              have hvu : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr huv.symm
              have hcard : (G.neighborFinset u \ {v}).card = G.degree u - 1 := by
                rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hvu,
                  SimpleGraph.card_neighborFinset_eq_degree]
              rw [hcard]
              exact Nat.sub_le_sub_right (G.degree_le_maxDegree u) 1
        _ = (G.neighborFinset v).card * (Δ - 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ Δ * (Δ - 1) := by
              apply Nat.mul_le_mul_right
              rw [SimpleGraph.card_neighborFinset_eq_degree]
              exact G.degree_le_maxDegree v
    have hcover : (univ : Finset V) ⊆ insert v (G.neighborFinset v ∪ R) := by
      intro w _
      by_cases hwv : w = v
      · subst hwv; exact Finset.mem_insert_self _ _
      · rw [Finset.mem_insert]
        right
        by_cases hadj : G.Adj v w
        · exact Finset.mem_union_left _ ((G.mem_neighborFinset v w).mpr hadj)
        · exact Finset.mem_union_right _
            (by rw [hR, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hwv, hadj⟩)
    have hfin : Fintype.card V ≤ 1 + G.degree v + R.card := by
      rw [← Finset.card_univ]
      have h1 : (univ : Finset V).card ≤ (insert v (G.neighborFinset v ∪ R)).card :=
        Finset.card_le_card hcover
      have h2 : (insert v (G.neighborFinset v ∪ R)).card ≤ 1 + (G.neighborFinset v ∪ R).card := by
        have := Finset.card_insert_le v (G.neighborFinset v ∪ R); omega
      have h3 : (G.neighborFinset v ∪ R).card ≤ (G.neighborFinset v).card + R.card :=
        Finset.card_union_le _ _
      rw [SimpleGraph.card_neighborFinset_eq_degree] at h3
      omega
    have hdeg : G.degree v ≤ Δ := G.degree_le_maxDegree v
    have hfinal : Fintype.card V ≤ 1 + Δ + Δ * (Δ - 1) := by omega
    have harith : ∀ d : ℕ, 1 + d + d * (d - 1) ≤ d ^ 2 + 1 := by
      intro d
      rcases d with _ | k
      · simp
      · simp only [Nat.succ_sub_one]; nlinarith
    exact hfinal.trans (harith Δ)
