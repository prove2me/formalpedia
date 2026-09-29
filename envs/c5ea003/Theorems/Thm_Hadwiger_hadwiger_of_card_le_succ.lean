-- Prove2me | Theorems.Thm_Hadwiger_hadwiger_of_card_le_succ
-- name    : Hadwiger.hadwiger_of_card_le_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:43:02.55863+00:00
-- url     : https://prove2.me/theorems/0ae9af41-a3da-4f83-9e7d-62b024f567ff
-- title:
--   Hadwiger's conjecture holds for all graphs with at most `k+1` vertices,
-- statement:
--   **Hadwiger's conjecture holds for all graphs with at most `k+1` vertices**,
--   for every `k` — including the open cases `k ≥ 5`.
--
--   ```lean
--   theorem Hadwiger.hadwiger_of_card_le_succ[Fintype V] {k : ℕ} (hcard : Fintype.card V ≤ k + 1)
--       (h : ¬ G.Colorable k) : CompleteMinor (k + 1) G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HadwigerSmallGraphs.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HadwigerSmallGraphs.lean#L100

-- Thm stub generated from Probability/HadwigerSmallGraphs.lean
import Mathlib
import Definitions.Def_Probability_HadwigerK3
/-
  Cliques, and Hadwiger's Conjecture in the Small-Graph Range
  ==========================================================

  Two unconditional results that hold for *every* `k`, and so cut off the
  "trivial range" of Hadwiger's conjecture:

  * `Hadwiger.completeMinor_of_isNClique` : a clique of size `n` is in
                                            particular a `Kₙ` minor (the
                                            Hadwiger number dominates the clique
                                            number).
  * `Hadwiger.hadwiger_of_card_le_succ`   : **Hadwiger's conjecture holds for
                                            every graph with at most `k+1`
                                            vertices** — such a graph fails to be
                                            `k`-colourable only if it is the
                                            complete graph `K_{k+1}` itself.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): the extremal case of Hadwiger's conjecture is
    `G = K_{k+1}`; below that vertex count the conjecture should be provable
    outright for all `k`, giving an unconditional theorem covering infinitely
    many open instances (`k ≥ 5`) in a restricted regime.
  Experiment (Experimenter): if `|V| ≤ k` a mere injection `V ↪ Fin k` colours
    `G`, so `|V| = k+1`; and if two vertices `u ≠ v` were non-adjacent, the
    colouring "identify `v` with `u`, and be injective elsewhere" uses only `k`
    colours.  Hence `G = ⊤`, and the singleton branch sets on a clique give the
    `K_{k+1}` model.
  Analysis (Analyst): the argument isolates *why* the conjecture is hard: the
    only obstruction in the small regime is the complete graph, whereas for
    `|V| > k+1` genuinely global structure (contraction) is needed.
  Critique (Critic): the identification colouring must be checked on the edge
    `v–u` — this is exactly where non-adjacency of `u` and `v` is used, so the
    hypothesis is load-bearing rather than decorative.
  Synthesis (PI): together with `hadwiger_monotone` these give unconditional
    fragments of every open case of the conjecture.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem Hadwiger.hadwiger_of_card_le_succ[Fintype V] {k : ℕ} (hcard : Fintype.card V ≤ k + 1)
    (h : ¬ G.Colorable k) : CompleteMinor (k + 1) G := by sorry
