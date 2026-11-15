-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_coordinateCutForm_sq_le_paired_mean
-- name    : Wikipedia.SzemeredisTheorem.coordinateCutForm_sq_le_paired_mean
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:51:58.025202+00:00
-- url     : https://prove2.me/theorems/f0873fcb-90d7-4211-b826-6ffdf82caf4f
-- title:
--   One Cauchy–Schwarz step pairs the head coordinate of a cut form
-- statement:
--   For a nonempty finite type $G$, a real function $F$ of $n+1$ coordinates, and an absolutely bounded cut-test family $u$,
--
--   $$
--   Q_{n+1}(F,u)^2\le\mathbb E_{p\in G^2}Q_n(F_p,u_p).
--   $$
--
--   Here $F_p(y)=F(p_0,y)F(p_1,y)$, and $u_p$ is the paired tail cut obtained by multiplying the two corresponding remaining deleted-coordinate factors.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/BoxNorm.lean#L339-L375

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Finite box moments and generalized von Neumann

This file packages the iterated Cauchy--Schwarz argument for a function on a
finite product.  A coordinate cut form pairs the function with one bounded
factor for every deleted coordinate.  Its `2 ^ n`-th power is bounded by the
recursive `n`-dimensional box moment.

The recursive definition duplicates one coordinate at a time.  It is
definitionally aligned with the Cauchy--Schwarz proof and is equivalent to
the usual average of the product over all vertices of an `n`-cube.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.coordinateCutForm_sq_le_paired_mean
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (u : CutTestFamily G (n + 1))
    (hu : IsAbsBoundedCutTest u) :
    coordinateCutForm (n + 1) F u ^ 2 ≤
      mean fun p : G × G =>
        coordinateCutForm n
          (pairedTupleFunction F p) (pairedTailCut u p) := by sorry
