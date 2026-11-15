-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_apSimplexSystem_simplexCount_eq_cyclicAPCount
-- name    : Wikipedia.SzemeredisTheorem.apSimplexSystem_simplexCount_eq_cyclicAPCount
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:41:57.474137+00:00
-- url     : https://prove2.me/theorems/b2edd016-bb47-4fb2-91ce-910f6063cb31
-- title:
--   Normalized AP-simplex counts equal cyclic progression counts
-- statement:
--   For every natural $r$, nonzero modulus $N$, and real function $f$ on $\mathbb Z/N\mathbb Z$, the normalized simplex count of the AP system of length $r+2$ equals the cyclic AP count of $f$ in that length.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/APCorrespondence.lean#L169-L203

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
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
# The arithmetic-progression/simplex correspondence

For `k = r + 2`, the coordinate moment and the negative coordinate sum give
the initial term and common difference of the encoded cyclic progression.
The remaining `r` coordinates parametrize every fiber uniformly.  An
explicit equivalence records this change of variables and transports the
normalized simplex average to the normalized arithmetic-progression count.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.apSimplexSystem_simplexCount_eq_cyclicAPCount
    (r N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    (apSimplexSystem (r + 2) N f).simplexCount =
      cyclicAPCount (r + 2) N f := by sorry
