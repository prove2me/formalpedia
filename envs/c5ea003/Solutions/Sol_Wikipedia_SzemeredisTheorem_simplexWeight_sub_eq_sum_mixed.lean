-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.simplexWeight_sub_eq_sum_mixed
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:28:42.654208+00:00
-- url     : https://prove2.me/submissions/921d2259-d637-4a2d-ae99-6bc390cb115b

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_prod_sub_prod_eq_sum_ordered

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Edge-by-edge telescoping for weighted simplex counts

The relative counting lemma compares two products by replacing one edge at a
time.  This file isolates that exact finite algebra.  No boundedness is
required: all analytic work is reduced to bounding one mixed correlation for
each edge colour.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Exact pointwise edge-by-edge telescoping of simplex weights. -/
theorem solution
    {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V)
    (x : (i : Fin k) → V i) :
    H.simplexWeight x - G.simplexWeight x =
      ∑ j : Fin k, mixedSimplexTerm H G j x := by
  change
    (∏ j : Fin k,
        H.edgeWeight j (deleteCoordinate x j)) -
      ∏ j : Fin k,
        G.edgeWeight j (deleteCoordinate x j) =
      ∑ j : Fin k, mixedSimplexTerm H G j x
  simpa [mixedSimplexTerm] using
    prod_sub_prod_eq_sum_ordered Finset.univ
      (fun j : Fin k =>
        H.edgeWeight j (deleteCoordinate x j))
      (fun j : Fin k =>
        G.edgeWeight j (deleteCoordinate x j))
