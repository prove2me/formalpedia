-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cyclicAPMass_eq_diagonal_add_offDiagMass
-- name    : Wikipedia.SzemeredisTheorem.cyclicAPMass_eq_diagonal_add_offDiagMass
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:52:35.580211+00:00
-- url     : https://prove2.me/theorems/f166e976-a3f8-4a87-80e8-fb0264c5b530
-- title:
--   Total cyclic progression mass splits into diagonal and nonzero-difference mass
-- statement:
--   For every natural length $k$, positive modulus $N$, and real weight $f$ on the cyclic group, its total unnormalized progression mass is the sum of its diagonal mass and off-diagonal mass. The latter sums over nonzero common differences. No sign condition on $f$ is required.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/CountExtraction.lean#L82-L104

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Extracting an off-diagonal cyclic progression

For extraction it is convenient to use unnormalized finite masses.  In
particular, summing over the filtered finset of nonzero differences avoids
introducing a type of nonzero residues, which would be empty when `N = 1`,
and avoids dividing by `N - 1`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.cyclicAPMass_eq_diagonal_add_offDiagMass
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPMass k N f =
      cyclicAPDiagonalMass k N f + cyclicAPOffDiagMass k N f := by sorry
