-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_SimplexHypergraph_toWeighted_simplexWeight_eq_indicator
-- name    : Wikipedia.SzemeredisTheorem.SimplexHypergraph.toWeighted_simplexWeight_eq_indicator
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:34:51.385187+00:00
-- url     : https://prove2.me/theorems/a80ba400-9ba3-45f6-94d9-acaeb386eb2c
-- title:
--   The indicator-weighted simplex weight is the simplex indicator
-- statement:
--   Let $V_i$ be finite types with decidable equality indexed by $i\in\mathrm{Fin}(k)$, and let $H$ be a simplex hypergraph on these types. At each full tuple $x$, the simplex weight of the indicator-weighted system equals the indicator of the finite set of labelled simplices of $H$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Unweighted.lean#L97-L123

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

theorem Wikipedia.SzemeredisTheorem.SimplexHypergraph.toWeighted_simplexWeight_eq_indicator {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    H.toWeighted.simplexWeight x =
      finsetIndicator H.simplexFinset x := by sorry
