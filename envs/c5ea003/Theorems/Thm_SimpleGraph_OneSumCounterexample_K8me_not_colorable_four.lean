-- Prove2me | Theorems.Thm_SimpleGraph_OneSumCounterexample_K8me_not_colorable_four
-- name    : SimpleGraph.OneSumCounterexample.K8me_not_colorable_four
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:33:02.326237+00:00
-- url     : https://prove2.me/theorems/74581bdc-572c-423a-9107-c141e9575f5a
-- title:
--   The sides are *not* `4`-colourable: they contain a `K₇`.
-- statement:
--   The sides are *not* `4`-colourable: they contain a `K₇`.  (By the closure theorem of the
--   companion file this is forced for any counterexample to closure of `i ≥ 1/4`.)
--
--   ```lean
--   theorem SimpleGraph.OneSumCounterexample.K8me_not_colorable_four: ¬ K8me.Colorable 4 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/OneSumIndepRatioCounterexample.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/OneSumIndepRatioCounterexample.lean#L134

-- Thm stub generated from Novelty/OneSumIndepRatioCounterexample.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumIndepRatioCounterexample

/-!
# The independence-ratio constraint `i(G) ≥ 1/4` is *not* closed under 1-sums

The companion file `Novelty.OneSumEqualityAnalysis` proved two things about 1-sums (vertex
amalgamations) `G = G₁ ⊕_v G₂`:

* colourability *is* closed under 1-sums (`SimpleGraph.IsOneSum.colorable`), so the class of
  `4`-colourable graphs — which by the catalog bound `indepRatio_ge_quarter_of_colorable_four`
  satisfies `i ≥ 1/4` — is 1-sum stable; and
* independence is only *superadditive with a defect of one*
  (`SimpleGraph.IsOneSum.card_add_card_le_indepNum_succ`), giving the sharp ratio bound
  `i(G) ≥ r - (1-r)/n` (`SimpleGraph.IsOneSum.indepRatio_ge_of_sides`).

This file settles the resulting dichotomy by an explicit extremal example, hence proves that
the "Minimum Independence Ratio Constraint" `i ≥ 1/4` is **not** a 1-sum closed property, and
that the defect term `-(1-r)/n` above cannot be improved.

The example is the 1-sum of two copies of `K₈` minus an edge (`K8me`), amalgamated at an
endpoint of the missing edge:

* `K8me.indepRatio = 1/4` — each side sits exactly on the threshold;
* `Glue.indepNum = 3` and `Glue.indepRatio = 1/5 < 1/4` — the amalgam falls below it;
* `Glue.indepRatio = 1/4 - (1 - 1/4)/15` — the general defect bound of the companion file is
  attained *with equality*, so it is sharp;
* `K8me_not_colorable_four` — consistently with the closure theorem, the sides are not
  `4`-colourable (they contain `K₇`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): 1-sums act as `max` on `χ` and `ω` but as a *mediant with defect*
on the pair `(α, n)`.  Bold prediction: the threshold property `i ≥ 1/4` is therefore not
1-sum closed, and the extremal configuration is a graph whose every maximum independent set
uses the cut vertex.
Experiment (Experimenter): brute-force search over the parameter space
`(n₁, α₁, α(G₁ - v))` showed that a drop below the threshold needs `4α_i - n_i ≤ 1` and
`α(G_i - v) = α_i - 1` on both sides; the smallest realisation is `K₈` minus an edge with
`v` an endpoint of the missing edge (`n = 8`, `α = 2`, `α(G - v) = 1`).  Exhaustive
enumeration of the `2¹⁵` vertex subsets of the amalgam confirmed `α = 3` (witness `{0,1,8}`),
i.e. `i = 1/5`.
Analysis (Analyst): the drop is exactly the defect term: `1/4 - (1 - 1/4)/15 = 1/5`.  So the
failure is not an accident of the example but the equality case of the general bound; any
1-sum of two threshold graphs loses at most `(1-r)/n`.
Critique (Critic): the sides are necessarily *not* `4`-colourable — otherwise the closure
theorem of the companion file would force `i ≥ 1/4` on the amalgam.  We verify this directly
(`K8me` contains a `K₇`), so the example does not contradict the colouring side of the
dictionary; it delimits it.
Synthesis (PI): "sharp bound + closure" do *not* compose into "closure of the sharp bound":
the reciprocal dictionary `i ≥ 1/k ↔ k`-colourability survives amalgamation only on the
colouring side.
-- !-- end Lab Notes -- !--
-/

open Finset

open SimpleGraph

open OneSumCounterexample

/-! ### A generic two-element bound

If any two distinct elements of a finite set are forced to be the pair `{a, b}`, then the set
has at most two elements, and it contains `a` as soon as it has two. -/


/-! ### The side graph: `K₈` minus an edge -/

theorem SimpleGraph.OneSumCounterexample.K8me_not_colorable_four: ¬ K8me.Colorable 4 := by sorry
