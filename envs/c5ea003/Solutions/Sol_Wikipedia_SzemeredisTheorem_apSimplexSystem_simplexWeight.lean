-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.apSimplexSystem_simplexWeight
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:07:40.865424+00:00
-- url     : https://prove2.me/submissions/d7deb423-fcad-4cc0-8d98-0737dbf532d5

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

open Wikipedia.SzemeredisTheorem in
/-- A labelled simplex in the AP system contributes exactly the weight of
the cyclic progression with initial term the coordinate moment and common
difference the negative coordinate sum. -/
theorem solution
    (k N : ℕ) (f : ZMod N → ℝ)
    (x : Fin k → ZMod N) :
    (apSimplexSystem k N f).simplexWeight x =
      cyclicAPProduct k N f
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) := by
  apply Finset.prod_congr rfl
  intro j _
  change
    f (apSimplexForm k N j (deleteCoordinate x j)) =
      f (cyclicAPTerm
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) j)
  congr 1
  rw [apSimplexForm_deleteCoordinate]
  simp [cyclicAPTerm]
  ring
