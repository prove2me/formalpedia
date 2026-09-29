-- Prove2me | solution 1 for SimpleGraph.OneSumCounterexample.K8me_indepNum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:21:42.82098+00:00
-- url     : https://prove2.me/submissions/47364e53-2f6b-4586-b697-532884e583b3

-- Sol generated from Novelty/OneSumIndepRatioCounterexample.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumIndepRatioCounterexample
import Theorems.Thm_SimpleGraph_OneSumCounterexample_card_le_two_of_forced_pair

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





/-- In `K₈ - e`, two distinct non-adjacent vertices are the endpoints of the missing edge. -/
theorem forced_pair_k8me (x y : Fin 8) (hne : x ≠ y) (hadj : ¬ K8me.Adj x y) :
    (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  revert x y; decide




/-! ### The amalgam: two copies of `K₈ - e` glued at an endpoint of the missing edge

Vertices `0,…,7` form the first side (missing edge `{0,1}`), vertices `0, 8,…,14` the second
(missing edge `{0,8}`); the cut vertex is `0`. -/




instance : DecidableRel glueAdj := fun x y => by unfold glueAdj; infer_instance










instance : DecidablePred (· ∈ sideB) := fun x => by unfold sideB; infer_instance






/-! ### The two sides are copies of `K₈ - e` -/









/-! ### The main negative result -/





open SimpleGraph in
theorem solution: K8me.indepNum = 2 := by
  classical
  refine le_antisymm ?_ ?_
  · obtain ⟨s, hs, hcard⟩ := K8me.exists_isNIndepSet_indepNum
    have H : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        (x = (0 : Fin 8) ∧ y = (1 : Fin 8)) ∨ (x = (1 : Fin 8) ∧ y = (0 : Fin 8)) := by
      intro x hx y hy hne
      exact forced_pair_k8me x y hne (hs (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hne)
    have := (card_le_two_of_forced_pair H).1
    omega
  · have hind : K8me.IsIndepSet ↑({0, 1} : Finset (Fin 8)) := by
      intro x hx y hy hne
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first
        | exact absurd rfl hne
        | decide
    have := hind.card_le_indepNum
    simpa using this
