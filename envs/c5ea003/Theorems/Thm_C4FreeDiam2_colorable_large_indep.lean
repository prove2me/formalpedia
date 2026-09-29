-- Prove2me | Theorems.Thm_C4FreeDiam2_colorable_large_indep
-- name    : C4FreeDiam2.colorable_large_indep
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:05:54.182207+00:00
-- url     : https://prove2.me/theorems/f693672f-8952-4f03-942d-e86d5f149b56
-- title:
--   A graph with an `n`-coloring (`n ≥ 1`) on a nonempty vertex set has an
-- statement:
--   A graph with an `n`-coloring (`n ≥ 1`) on a nonempty vertex set has an
--   independent set `S` (a whole color class) with `|V| ≤ n · |S|`.
--
--   ```lean
--   theorem C4FreeDiam2.colorable_large_indep{n : ℕ} (hn : 0 < n) [Nonempty V] (h : G.Colorable n) :
--       ∃ S : Finset V, (∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) ∧ Fintype.card V ≤ n * S.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/C4FreeDiameter2Coloring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/C4FreeDiameter2Coloring.lean#L66

-- Thm stub generated from Novelty/C4FreeDiameter2Coloring.lean
import Mathlib
import Definitions.Def_Novelty_C4FreeDiameter2

/-!
# The 3-colorability bridge for C4-free diameter-2 graphs

This companion to `C4FreeDiameter2.lean` supplies the *colorability* half of the
research target.  The conjecture

> *A C4-free diameter-2 graph without universal vertices with `Δ ≥ 17` is not
> 3-colorable*

is an upper bound on the independence number in disguise, because a proper
`n`-coloring is exactly a partition into `n` independent sets.

## Main results

* `colorable_large_indep` — a graph with an `n`-coloring (`n ≥ 1`) has an
  independent set `S` with `|V| ≤ n · |S|` (a color class of size `≥ |V|/n`).
* `not_colorable_of_small_indep` — the contrapositive route to
  non-3-colorability: if *every* independent set `S` satisfies `3·|S| < |V|`,
  then `G` is not 3-colorable.
* `conjecture_from_independence_bound` — the explicit reduction of the research
  target to the independence-number bound, phrased with the structural predicates
  of `C4FreeDiam2`.
* `card_ge_of_maxDegree_ge_seventeen` — a concrete consequence of the structural
  file: under the conjecture's hypotheses every such graph has at least 19
  vertices.

-- !-- Lab Notes -- !--
**Hypothesis (Hypothesizer).** Non-3-colorability is a statement about the
*independence number* `α`: `G.Colorable 3` forces `3·α ≥ |V|` by pigeonhole on
the three color classes.  Hence the entire conjecture reduces to proving
`3·α < |V|`, i.e. `α ≤ (|V|−1)/3`, for C4-free diameter-2 graphs with `Δ ≥ 17`.

**Experiment (Experimenter).** We proved the pigeonhole direction unconditionally:
if all three color classes were smaller than `|V|/3` their sizes would sum to less
than `|V|`, contradicting that they partition `V`.  This gives
`colorable_large_indep` and, by contraposition, `not_colorable_of_small_indep`.
Combining with the structural file, `Δ ≥ 17` and the no-universal-vertex bound
`Δ + 2 ≤ |V|` immediately yield `|V| ≥ 19`.

**Analysis (Analyst).** The colorability bridge is *tight and general* — it holds
for every finite graph, so it cannot itself be where the `Δ ≥ 17` threshold
enters.  The threshold must come from an independence bound specific to the
C4-free diameter-2 structure (the still-open piece).  This cleanly separates the
"soft" reduction (done here) from the "hard" extremal input.

**Critique (Critic).** `colorable_large_indep` uses a strict-sum pigeonhole
(`by_contra` + `Finset.sum_lt_sum_of_nonempty`), not `decide`; the reduction
theorem genuinely applies `not_colorable_of_small_indep`; the numeric corollary
genuinely applies `maxDegree_add_two_le_card` from the catalog file.  No result is
vacuous: `card_ge_of_maxDegree_ge_seventeen` has a satisfiable hypothesis and a
non-trivial conclusion.

**Synthesis (PI).** Together the two files reduce the grand conjecture to a single
extremal statement about the independence number, and package the classical
counting bounds (Moore, Kővári–Sós–Turán) needed to attack it.
-/

open SimpleGraph Finset

open C4FreeDiam2

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in

theorem C4FreeDiam2.colorable_large_indep{n : ℕ} (hn : 0 < n) [Nonempty V] (h : G.Colorable n) :
    ∃ S : Finset V, (∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) ∧ Fintype.card V ≤ n * S.card := by sorry
