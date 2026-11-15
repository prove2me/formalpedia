-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_simplexCount_sub_eq_sum_mixedCorrelation
-- name    : Wikipedia.SzemeredisTheorem.simplexCount_sub_eq_sum_mixedCorrelation
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:27:53.878125+00:00
-- url     : https://prove2.me/theorems/6be757f6-5ab6-4e7c-85d3-fbf5094c58de
-- title:
--   Telescoping normalized simplex counts
-- statement:
--   Let $V_i$ be finite types indexed by $i\in\mathrm{Fin}(k)$ and let $H,G$ be weighted simplex systems on them. The difference $H.\mathrm{simplexCount}-G.\mathrm{simplexCount}$ equals the sum over all distinguished coordinates $j$ of the mixed simplex correlations of $H,G$ at $j$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/SimplexTelescoping.lean#L87-L107

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

theorem Wikipedia.SzemeredisTheorem.simplexCount_sub_eq_sum_mixedCorrelation
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) :
    H.simplexCount - G.simplexCount =
      ∑ j : Fin k, mixedSimplexCorrelation H G j := by sorry
