-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_simplexWeight_sub_eq_sum_mixed
-- name    : Wikipedia.SzemeredisTheorem.simplexWeight_sub_eq_sum_mixed
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:28:17.357815+00:00
-- url     : https://prove2.me/theorems/89da6982-705f-4bda-af4c-f3f19014ce37
-- title:
--   Pointwise telescoping of simplex weights
-- statement:
--   For any coordinate types $V_i$ indexed by $\mathrm{Fin}(k)$, weighted simplex systems $H,G$, and full tuple $x$, the difference of their simplex weights at $x$ equals the sum over coordinates $j$ of the mixed simplex terms at $j,x$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/SimplexTelescoping.lean#L60-L78

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

theorem Wikipedia.SzemeredisTheorem.simplexWeight_sub_eq_sum_mixed
    {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V)
    (x : (i : Fin k) → V i) :
    H.simplexWeight x - G.simplexWeight x =
      ∑ j : Fin k, mixedSimplexTerm H G j x := by sorry
