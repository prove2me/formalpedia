-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_prod_sub_prod_eq_sum_ordered
-- name    : Wikipedia.SzemeredisTheorem.prod_sub_prod_eq_sum_ordered
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:26:09.751807+00:00
-- url     : https://prove2.me/theorems/558eb8ec-ffd7-4ad0-8ca3-cfa1d870bd83
-- title:
--   An ordered telescoping identity for finite products
-- statement:
--   For any finite set $s$ in a linearly ordered type and real functions $f,g$, $\prod_{i\in s}f(i)-\prod_{i\in s}g(i)$ equals $\sum_{i\in s}(f(i)-g(i))(\prod_{j\in s,\,j<i}f(j))(\prod_{j\in s,\,i<j}g(j))$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/SimplexTelescoping.lean#L18-L45

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

theorem Wikipedia.SzemeredisTheorem.prod_sub_prod_eq_sum_ordered
    {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (f g : ι → ℝ) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i =
      ∑ i ∈ s,
        (f i - g i) *
          (∏ j ∈ s with j < i, f j) *
          ∏ j ∈ s with i < j, g j := by sorry
