-- Prove2me | solution 1 for AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS.card_rootedLabeledTree_one
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:13:16.784891+00:00
-- url     : https://prove2.me/submissions/0465d5d0-f212-4565-b50d-0bf8afd808fd

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_LabeledTreeBasic
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

namespace AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS end AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# Labelled trees on a finite vertex set

We introduce the genuine combinatorial object underlying Cayley's formula: the
type of labelled trees on `Fin n`, namely simple graphs on `Fin n` that are
trees (connected and acyclic), and the rooted version.  These are finite types.

The cardinality results (`card (LabeledTree n) = n^(n-2)`,
`card (RootedLabeledTree n) = n^(n-1)`) and the connection to the banked
`cayleyRootedTree` are established in `Prufer.lean` / `Cayley.lean`.
-/

namespace AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS

/-- The rooted count factors as the unrooted count times `n`. -/
theorem card_rootedLabeledTree_eq (n : ℕ) :
    Fintype.card (RootedLabeledTree n) = Fintype.card (LabeledTree n) * n := by
  show Fintype.card (LabeledTree n × Fin n) = _
  rw [Fintype.card_prod, Fintype.card_fin]

end AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS
end

/-!
# Cayley's formula: cardinalities of labelled trees

This file collects the cardinality results for `LabeledTree` and
`RootedLabeledTree` and connects them to the banked `cayleyRootedTree`.

The base cases `n = 0` and `n = 1` are proved here directly.  The general
`n ≥ 2` case (via the Prüfer bijection) lives in `Prufer.lean`; this file
assembles the final connection.
-/

open AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

namespace AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS

/-- On a single vertex, the (unique) empty graph is a tree. -/
theorem isTree_bot_fin_one : (⊥ : SimpleGraph (Fin 1)).IsTree := by
  have hconn : (⊥ : SimpleGraph (Fin 1)).Connected := by
    refine ⟨?_⟩
    intro u v
    have huv : u = v := Subsingleton.elim u v
    subst huv
    exact SimpleGraph.Reachable.refl u
  exact ⟨hconn, SimpleGraph.isAcyclic_bot⟩

theorem card_labeledTree_one : Fintype.card (LabeledTree 1) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨⊥, isTree_bot_fin_one⟩, ?_⟩
  rintro ⟨G, hG⟩
  exact Subtype.ext (Subsingleton.elim _ _)

end AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS

open AnalyticCombinatorics AnalyticCombinatorics.Ch7 AnalyticCombinatorics.Ch7.SingularityApp AnalyticCombinatorics.Ch7.SingularityApp.LabeledTreeNS
open AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS
theorem solution : Fintype.card (RootedLabeledTree 1) = 1 := by
  rw [card_rootedLabeledTree_eq, card_labeledTree_one]
