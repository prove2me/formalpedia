-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SimplexHypergraph.toWeighted_simplexWeight_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:01.260565+00:00
-- url     : https://prove2.me/submissions/366c521d-7663-4fe6-afed-eba8f419e938

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Unweighted partite simplex hypergraphs

The removal argument uses a `(k - 1)`-uniform, `k`-partite hypergraph whose
edge of colour `j` depends on every vertex coordinate except `j`.  This file
gives the finite predicate-valued interface and connects its labelled
simplices exactly to the weighted counting API.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



namespace SimplexHypergraph













@[simp]
theorem toWeighted_edgeWeight_of_not_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : ¬H.edge j x) :
    H.toWeighted.edgeWeight j x = 0 := by
  classical
  simp [toWeighted, hx]













end SimplexHypergraph

end Wikipedia.SzemeredisTheorem

end
/-!
# Unweighted partite simplex hypergraphs

The removal argument uses a `(k - 1)`-uniform, `k`-partite hypergraph whose
edge of colour `j` depends on every vertex coordinate except `j`.  This file
gives the finite predicate-valued interface and connects its labelled
simplices exactly to the weighted counting API.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.SimplexHypergraph

open Wikipedia.SzemeredisTheorem.SimplexHypergraph in
/-- A zero-one simplex weight is exactly the indicator of the labelled
simplex finset. -/
theorem solution {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    H.toWeighted.simplexWeight x =
      finsetIndicator H.simplexFinset x := by
  classical
  by_cases hx : x ∈ H.simplexFinset
  · have hedges :
        ∀ j, H.edge j (deleteCoordinate x j) :=
      (H.mem_simplexFinset x).mp hx
    simp [WeightedSimplexSystem.simplexWeight, toWeighted,
      finsetIndicator, hx, hedges]
  · have hnot :
        ¬∀ j, H.edge j (deleteCoordinate x j) := by
      simpa using hx
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have hzero :
        ∏ i : Fin k,
            H.toWeighted.edgeWeight i (deleteCoordinate x i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact toWeighted_edgeWeight_of_not_edge H hj
    rw [WeightedSimplexSystem.simplexWeight, hzero]
    exact (finsetIndicator_of_not_mem hx).symm
