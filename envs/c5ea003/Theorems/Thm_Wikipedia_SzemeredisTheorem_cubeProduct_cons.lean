-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cubeProduct_cons
-- name    : Wikipedia.SzemeredisTheorem.cubeProduct_cons
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:52:33.877204+00:00
-- url     : https://prove2.me/theorems/7d794ce5-e07f-4b20-9ba4-e94f84bc9b10
-- title:
--   Splitting a cube product along its first coordinate
-- statement:
--   For any vertex type $G$, real function $F$ of $n+1$ coordinates, head endpoint pair $p$, and $n$ tail endpoint pairs $x$, the product of $F$ over all vertices of the resulting $(n+1)$-cube equals the product over tail-cube vertices of
--
--   $$
--   F_p(y)=F(p_0,y)F(p_1,y).
--   $$
--
--   The identity is finite and does not require $G$ to be finite.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/BoxNorm.lean#L138-L167

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

theorem Wikipedia.SzemeredisTheorem.cubeProduct_cons
    {G : Type*} {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (p : G × G) (x : Fin n → G × G) :
    (∏ ω : Fin (n + 1) → Bool,
        F (cubeVertex (Fin.cons p x) ω)) =
      ∏ ω : Fin n → Bool,
        pairedTupleFunction F p (cubeVertex x ω) := by sorry
