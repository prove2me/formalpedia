-- Prove2me | Theorems.Thm_SimpleGraph_not_colorable_four_of_indepRatio_lt
-- name    : SimpleGraph.not_colorable_four_of_indepRatio_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:34:08.101985+00:00
-- url     : https://prove2.me/theorems/4e257457-f178-4007-a16c-fdd9243647b6
-- title:
--   Not colorable four of indepRatio lt
-- statement:
--   Formal statement of `SimpleGraph.not_colorable_four_of_indepRatio_lt` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SimpleGraph.not_colorable_four_of_indepRatio_lt(hpos : 0 < Fintype.card V)
--       (h : G.indepRatio < 1 / 4) : ¬ G.Colorable 4 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IndependenceRatioChromatic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IndependenceRatioChromatic.lean#L83

-- Thm stub generated from Novelty/IndependenceRatioChromatic.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic

/-!
# Independence ratio, colourings, and the fractional chromatic lower bound

This file develops the finite-graph combinatorics underlying the Hadwiger–Nelson /
fractional-chromatic-number circle of problems.  The *independence ratio* of a finite
graph `G` on `n > 0` vertices is `i(G) = α(G) / n`, where `α(G) = G.indepNum` is the
independence number.  The motivating question (Erdős 1987; Matolcsi–Ruzsa–Varga–Zsámboki)
asks whether a finite unit-distance graph in the plane can have `i(G) < 1/4`; a positive
answer forces the *fractional* chromatic number of the plane to exceed `4`.

Here we prove the two structural inequalities that make "`i(G) < 1/4`" a lower bound on
colourings:

* `SimpleGraph.card_le_colors_mul_indepNum` — the integral pigeonhole bound
  `n ≤ k · α(G)` for any proper `k`-colouring (each colour class is independent).
* `SimpleGraph.not_colorable_four_of_indepRatio_lt` and
  `SimpleGraph.four_lt_chromaticNumber_of_indepRatio_lt` — if `i(G) < 1/4` then `G` is
  not `4`-colourable and `χ(G) > 4`.
* `SimpleGraph.FracColoring` — a *fractional* colouring (nonnegative weights on
  independent sets covering every vertex), with
  `SimpleGraph.FracColoring.value_ge_of_indepNum` giving the LP lower bound
  `value ≥ n / α(G)`, and `SimpleGraph.four_lt_fracValue_of_indepRatio_lt` giving the
  fractional analogue: if `i(G) < 1/4` then **every** fractional colouring has value `> 4`,
  i.e. `χ_f(G) > 4`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the reason a small independence ratio forces many colours is
purely the LP-duality inequality `value(fractional colouring) ≥ n/α`; the "1/4" threshold
is just `α/n < 1/4 ⇔ n/α > 4`.  Bold form: the *fractional* bound, not only the integral
one, follows from a one-line double-counting of the covering constraint.
Experiment (Experimenter): for the integral bound, partition the vertex set into colour
classes via `Finset.card_eq_sum_card_fiberwise`, bound each class by `indepNum` through
`IsIndepSet.card_le_indepNum`, and sum.  For the fractional bound, double-count
`∑_v ∑_{s ∋ v} w s = ∑_s w s · |s|`, then use `|s| ≤ α` on the support.
Analysis (Analyst): the integral statement is the special case where the weights are the
indicators of the colour classes; the fractional statement is strictly stronger and is the
one relevant to `χ_f(ℝ²) > 4`.  The threshold `1/4` is sharp in the sense that it is exactly
the reciprocal of the conjectured value `χ_f(ℝ²) = 4`.
Critique (Critic): the covering hypothesis `covers` (each vertex has total weight ≥ 1) and
the support hypothesis (`w s ≠ 0 → IsIndepSet s`) are both load-bearing: dropping `covers`
makes `value = 0` admissible; dropping the support constraint lets a single all-vertex set
carry the weight and destroys the `|s| ≤ α` step.  `n > 0` is needed to divide.
Synthesis (PI): these inequalities are the graph-theoretic engine converting the geometric
construction "a finite planar unit-distance graph with `i(G) < 1/4`" into the analytic
conclusion "`χ_f(ℝ²) > 4`".
-- !-- end Lab Notes -- !--
-/

open Finset

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-
**Pigeonhole / colour-class bound.**  In any proper `k`-colouring the vertex set is
partitioned into `k` independent colour classes, each of size at most `α(G)`, hence
`n ≤ k · α(G)`.
-/


/-
If the independence ratio is below `1/4`, then `G` is not `4`-colourable.
-/
omit [DecidableEq V] [DecidableRel G.Adj] in

theorem SimpleGraph.not_colorable_four_of_indepRatio_lt(hpos : 0 < Fintype.card V)
    (h : G.indepRatio < 1 / 4) : ¬ G.Colorable 4 := by sorry
