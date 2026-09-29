-- Prove2me | Definitions.Def_Novelty_OneSumIndepRatioCounterexample
-- name    : Novelty_OneSumIndepRatioCounterexample
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:34:53.970993+00:00
-- url     : https://prove2.me/theorems/828a30cb-01ee-4a5e-a1fa-822afd0b882f
-- title:
--   Aether Catalog definitions — Novelty_OneSumIndepRatioCounterexample
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.OneSumIndepRatioCounterexample`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/OneSumIndepRatioCounterexample.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis

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

namespace SimpleGraph

namespace OneSumCounterexample

/-! ### A generic two-element bound

If any two distinct elements of a finite set are forced to be the pair `{a, b}`, then the set
has at most two elements, and it contains `a` as soon as it has two. -/


/-! ### The side graph: `K₈` minus an edge -/

/-- Adjacency of `K₈` minus the edge `{0, 1}`. -/
def k8meAdj (x y : Fin 8) : Prop :=
  x ≠ y ∧ ¬((x : ℕ) = 0 ∧ (y : ℕ) = 1) ∧ ¬((x : ℕ) = 1 ∧ (y : ℕ) = 0)

instance : DecidableRel k8meAdj := fun x y => by unfold k8meAdj; infer_instance

/-- `K₈` minus one edge: the extremal side graph, with independence ratio exactly `1/4`. -/
def K8me : SimpleGraph (Fin 8) where
  Adj := k8meAdj
  symm := by intro x y hxy; revert hxy; revert x y; decide
  loopless := ⟨by decide⟩

instance : DecidableRel K8me.Adj := inferInstanceAs (DecidableRel k8meAdj)





/-! ### The amalgam: two copies of `K₈ - e` glued at an endpoint of the missing edge

Vertices `0,…,7` form the first side (missing edge `{0,1}`), vertices `0, 8,…,14` the second
(missing edge `{0,8}`); the cut vertex is `0`. -/

/-- Adjacency of the first part: `K₈` minus `{0,1}` on the vertices `0,…,7`. -/
def glueLeftAdj (x y : Fin 15) : Prop :=
  x ≠ y ∧ (x : ℕ) ≤ 7 ∧ (y : ℕ) ≤ 7 ∧
    ¬((x : ℕ) = 0 ∧ (y : ℕ) = 1) ∧ ¬((x : ℕ) = 1 ∧ (y : ℕ) = 0)

/-- Adjacency of the second part: `K₈` minus `{0,8}` on the vertices `0, 8,…,14`. -/
def glueRightAdj (x y : Fin 15) : Prop :=
  x ≠ y ∧ ((x : ℕ) = 0 ∨ 8 ≤ (x : ℕ)) ∧ ((y : ℕ) = 0 ∨ 8 ≤ (y : ℕ)) ∧
    ¬((x : ℕ) = 0 ∧ (y : ℕ) = 8) ∧ ¬((x : ℕ) = 8 ∧ (y : ℕ) = 0)

/-- Adjacency of the 1-sum. -/
def glueAdj (x y : Fin 15) : Prop := glueLeftAdj x y ∨ glueRightAdj x y

instance : DecidableRel glueLeftAdj := fun x y => by unfold glueLeftAdj; infer_instance
instance : DecidableRel glueRightAdj := fun x y => by unfold glueRightAdj; infer_instance
instance : DecidableRel glueAdj := fun x y => by unfold glueAdj; infer_instance

/-- The first part of the amalgam. -/
def GlueLeft : SimpleGraph (Fin 15) where
  Adj := glueLeftAdj
  symm := by intro x y hxy; revert hxy; revert x y; decide
  loopless := ⟨by decide⟩

/-- The second part of the amalgam. -/
def GlueRight : SimpleGraph (Fin 15) where
  Adj := glueRightAdj
  symm := by intro x y hxy; revert hxy; revert x y; decide
  loopless := ⟨by decide⟩

/-- The amalgam of two copies of `K₈ - e` at an endpoint of the missing edge. -/
def Glue : SimpleGraph (Fin 15) where
  Adj := glueAdj
  symm := by intro x y hxy; revert hxy; revert x y; decide
  loopless := ⟨by decide⟩

instance : DecidableRel Glue.Adj := inferInstanceAs (DecidableRel glueAdj)

/-- The first side. -/
def sideA : Set (Fin 15) := {x | (x : ℕ) ≤ 7}

/-- The second side. -/
def sideB : Set (Fin 15) := {x | (x : ℕ) = 0 ∨ 8 ≤ (x : ℕ)}




instance : DecidablePred (· ∈ sideA) := fun x => by unfold sideA; infer_instance
instance : DecidablePred (· ∈ sideB) := fun x => by unfold sideB; infer_instance






/-! ### The two sides are copies of `K₈ - e` -/

/-- Embedding of the first side. -/
def embA (x : Fin 8) : Fin 15 := ⟨(x : ℕ), by omega⟩

/-- Embedding of the second side (the cut vertex `0` is fixed). -/
def embB (x : Fin 8) : Fin 15 := if (x : ℕ) = 0 then 0 else ⟨(x : ℕ) + 7, by omega⟩







/-! ### The main negative result -/



end OneSumCounterexample

end SimpleGraph


