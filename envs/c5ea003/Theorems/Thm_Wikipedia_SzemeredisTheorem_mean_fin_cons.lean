-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_fin_cons
-- name    : Wikipedia.SzemeredisTheorem.mean_fin_cons
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:27:54.239514+00:00
-- url     : https://prove2.me/theorems/fe0fe128-1bd3-4556-9ed2-756389177cb2
-- title:
--   Splitting a finite tuple average into head and tail
-- statement:
--   Let $G$ be a finite set, let $n\ge0$ be an integer, and let $F:G^{n+1}\to\mathbb R$. Its normalized mean decomposes as
--   $$
--   \mathbb E_{x\in G^{n+1}}F(x)=\mathbb E_{a\in G}\mathbb E_{y\in G^n}F(a,y).
--   $$
--   On the right, $(a,y)$ is the tuple obtained by prepending $a$ to the $n$-tuple $y$. The identity uses the source's normalized finite-mean convention and does not assume $G$ is nonempty.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Finite/ProductMean.lean#L25-L45

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Products of independent finite means

The product of normalized averages over independent finite variables is the
normalized average over their product space.  This is the finite-probability
Fubini identity used when expanding products of generalized convolutions.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.mean_fin_cons
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) :
    mean F =
      mean₂ (fun a : G => fun y : Fin n → G => F (Fin.cons a y)) := by sorry
