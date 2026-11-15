-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_apSimplexSystem_simplexWeight
-- name    : Wikipedia.SzemeredisTheorem.apSimplexSystem_simplexWeight
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:41:52.556204+00:00
-- url     : https://prove2.me/theorems/8be4f997-299a-4762-9c65-264159f3a35e
-- title:
--   An AP-simplex weight is the corresponding cyclic progression product
-- statement:
--   For natural $k,N$, a real function $f$ on $\mathbb Z/N\mathbb Z$, and tuple $x$ of length $k$, the AP-simplex weight at $x$ equals the cyclic progression product whose initial value is the simplex coordinate moment and whose difference is the negative simplex coordinate sum.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Simplex.lean#L139-L159

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
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
# Partite weighted simplices

The dense and relative Szemerédi arguments are organized as counting lemmas
for a `(k-1)`-uniform, `k`-partite simplex.  An edge of colour `j` depends on
every vertex coordinate except `j`.  Keeping that dependency in the type
prevents accidental use of the omitted coordinate and matches the dependent
index used by the CFZ blow-up forms.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.apSimplexSystem_simplexWeight
    (k N : ℕ) (f : ZMod N → ℝ)
    (x : Fin k → ZMod N) :
    (apSimplexSystem k N f).simplexWeight x =
      cyclicAPProduct k N f
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) := by sorry
