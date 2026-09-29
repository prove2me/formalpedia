-- Prove2me | Theorems.Thm_SimpleGraph_IsOneSum_card_add_indicator_eq
-- name    : SimpleGraph.IsOneSum.card_add_indicator_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:31:24.105235+00:00
-- url     : https://prove2.me/theorems/26181d6c-d606-489d-8e91-f28b41b39211
-- title:
--   The splitting identity of a 1-sum.
-- statement:
--   **The splitting identity of a 1-sum.**  Any finite vertex set `s` splits along the two
--   sides, and the cut vertex is the only possible double count.
--
--   ```lean
--   theorem SimpleGraph.IsOneSum.card_add_indicator_eq[Fintype V] [DecidableEq V] (s : Finset V)
--       [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
--       s.card + (if v ∈ s then 1 else 0)
--         = (s.filter (· ∈ A)).card + (s.filter (· ∈ B)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/OneSumEqualityAnalysis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/OneSumEqualityAnalysis.lean#L238

-- Thm stub generated from Novelty/OneSumEqualityAnalysis.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis

/-!
# 1-sums (vertex amalgamations), the sharp pigeonhole bound, and its equality case

This file develops the *structure theory of 1-sums* for the colouring / independence-ratio
circle formalised in `Novelty.IndependenceRatioChromatic` and
`Novelty.IndependenceRatioLowerBound`.

A graph `G` is the **1-sum** (vertex amalgamation, clique-sum of order one) of `G₁` and `G₂`
along the cut vertex `v` if `G = G₁ ⊔ G₂`, all edges of `Gᵢ` live inside a side `A` resp. `B`,
the two sides cover the vertex set and meet exactly in `{v}`.  This is `SimpleGraph.IsOneSum`.

Main results.

* `SimpleGraph.IsOneSum.colorable` — **1-sum closure of colourability**: `k`-colourability is
  preserved by 1-sums.  The proof recolours the second side by the transposition that matches
  the two colours of the cut vertex.
* `SimpleGraph.IsOneSum.chromaticNumber_eq_max` — `χ(G) = max (χ G₁) (χ G₂)`.
* `SimpleGraph.IsOneSum.isClique_left_or_right`, `SimpleGraph.IsOneSum.cliqueNum_eq_max` —
  every clique of a 1-sum lies on one side, hence `ω(G) = max (ω G₁) (ω G₂)`.
* `SimpleGraph.IsOneSum.chromaticNumber_eq_cliqueNum` — **weak perfection (`χ = ω`) is closed
  under 1-sums**; the equality analysis is exactly the pair of `max` formulas above.
* `SimpleGraph.IsOneSum.card_add_indicator_eq` — the exact splitting identity for an arbitrary
  vertex set: `|s| + [v ∈ s] = |s ∩ A| + |s ∩ B|`.
* `SimpleGraph.card_eq_colors_mul_indepNum_iff` — **the equality analysis of the sharp
  pigeonhole bound** `n ≤ k·α(G)` of the catalog: equality holds for a `k`-colouring `C`
  precisely when *every* colour class of `C` is a maximum independent set.
* `SimpleGraph.indepRatio_eq_inv_iff` — consequently `i(G) = 1/k` iff all colour classes are
  maximum independent sets, and `SimpleGraph.IsOneSum.indepRatio_ge_quarter` /
  `SimpleGraph.IsOneSum.indepRatio_eq_quarter_iff` transport the sharp bound `i(G) ≥ 1/4`
  and its equality case across a 1-sum of two `4`-colourable graphs.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the two catalog ingredients — the sharp bound `n ≤ k·α` and the
closure of the colouring class under 1-sums — should combine into a *dictionary*: on the
colouring side a 1-sum is a `max`, so every `max`-stable invariant (`χ`, `ω`) is determined by
the pieces, and the conjecture "`i ≥ 1/4` is 1-sum stable" reduces to whether the *ratio* is
`max`-stable too.  Ratios are not `max`-stable (they are mediants), so the prediction is:
colouring closure survives, ratio closure fails.
Experiment (Experimenter): the colouring closure was proved by the transposition recolouring
`x ↦ if x ∈ A then C₁ x else (swap (C₁ v) (C₂ v)) (C₂ x)`; the only delicate case is an edge of
`G₂` incident to the cut vertex, where `swap` is used through `Equiv.swap_apply_left`.  The
clique statement needed the observation that a vertex of `A \ B` and a vertex of `B \ A` are
never adjacent, so a clique cannot straddle the cut.
Analysis (Analyst): the equality analysis of the pigeonhole bound is a `Finset.sum_lt_sum`
argument: `n = ∑_c |C⁻¹ c| ≤ ∑_c α = k·α`, with equality iff no fibre is strictly smaller than
`α`.  This makes "`i(G) = 1/k`" a *balancedness* statement, not a metric accident.
Critique (Critic): `A ∪ B = univ` is load-bearing for the clique and splitting statements
(otherwise a vertex outside both sides is isolated in `G` and joins every independent set but
no side); `A ∩ B = {v}` is load-bearing for the colouring proof (two shared vertices need a
simultaneous match, which a single transposition cannot deliver).  No statement here is
definitional: each `max` formula needs both inequalities and one of them uses the
recolouring.
Synthesis (PI): 1-sums act as `max` on `χ` and `ω` and as a *mediant with a defect `-1`* on
`(α, n)`.  The defect is exactly the cut vertex counted twice, which is what
`card_add_indicator_eq` isolates — and it is what the companion file
`Novelty.OneSumIndepRatioCounterexample` turns into a refutation of ratio closure.
-- !-- end Lab Notes -- !--
-/

open Finset

open SimpleGraph

variable {V : Type*} {G G₁ G₂ : SimpleGraph V} {A B : Set V} {v : V}


open IsOneSum

variable (h : IsOneSum G G₁ G₂ A B v)
include h

theorem SimpleGraph.IsOneSum.card_add_indicator_eq[Fintype V] [DecidableEq V] (s : Finset V)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    s.card + (if v ∈ s then 1 else 0)
      = (s.filter (· ∈ A)).card + (s.filter (· ∈ B)).card := by sorry
