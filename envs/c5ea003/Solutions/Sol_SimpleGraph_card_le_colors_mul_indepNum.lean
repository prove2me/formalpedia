-- Prove2me | solution 1 for SimpleGraph.card_le_colors_mul_indepNum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:06:15.357882+00:00
-- url     : https://prove2.me/submissions/90bdee8c-b44e-4334-9ae5-90de77732de4

-- Sol generated from Novelty/IndependenceRatioChromatic.lean
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

/-
If the independence ratio is below `1/4`, the chromatic number exceeds `4`.
-/

/-! ### Fractional colourings -/



/-
**LP lower bound for fractional colourings.**  Any fractional colouring has value at
least `n / α(G)`, obtained by double-counting the covering constraint.
-/






/-
**Fractional analogue of the `1/4` threshold.**  If the independence ratio is below
`1/4`, then *every* fractional colouring has value strictly greater than `4`; equivalently
`χ_f(G) > 4`.
-/


open SimpleGraph in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem solution{k : ℕ} (C : G.Coloring (Fin k)) :
    Fintype.card V ≤ k * G.indepNum := by
  -- By definition of $C$, each color class is an independent set.
  have h_indep_class : ∀ (c : Fin k), ∀ v ∈ Finset.filter (fun v => C v = c) Finset.univ, ∀ w ∈ Finset.filter (fun v => C v = c) Finset.univ, v ≠ w → ¬G.Adj v w := by
    exact fun c v hv w hw hne hadj => by have := C.valid hadj; aesop;
  -- By definition of $C$, each color class is an independent set, so its size is at most $\alpha(G)$.
  have h_card_indep_class : ∀ (c : Fin k), (Finset.filter (fun v => C v = c) Finset.univ).card ≤ G.indepNum := by
    exact fun c => IsIndepSet.card_le_indepNum (h_indep_class c)
  convert Finset.sum_le_sum fun c ( hc : c ∈ Finset.univ ) => h_card_indep_class c;
  · simp +decide only [card_filter];
    rw [ Finset.sum_comm ] ; aesop;
  · simp +decide
