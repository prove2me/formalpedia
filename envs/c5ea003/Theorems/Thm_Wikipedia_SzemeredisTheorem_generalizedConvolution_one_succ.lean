-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_generalizedConvolution_one_succ
-- name    : Wikipedia.SzemeredisTheorem.generalizedConvolution_one_succ
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:08:21.16097+00:00
-- url     : https://prove2.me/theorems/8e2bc27d-884b-4583-b16d-f8bf58f08ea8
-- title:
--   Generalized convolution of constant-one cut tests
-- statement:
--   Let $G$ be a finite abelian group, let $n\ge0$ be an integer, and let $z\in G$. Consider the family of $n+1$ cut tests on $G^n$, each identically equal to $1$. Their generalized convolution is also identically equal to $1$:
--   $$
--   \mathcal C_{n+1}(1,\ldots,1)(z)=1.
--   $$
--   This includes the boundary case $n=0$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/GeneralizedConvolution.lean#L305-L321

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Generalized convolutions on finite additive groups

For positive arity, the generalized convolution is the normalized average of
a weight over a fiber of the coordinate-sum map. At arity zero the sum map
has only the value zero, so the fiber density is a scaled delta function.
Keeping this scaling makes the pairing identity valid without an arity
exception; the `[0,1]` range statement is correctly restricted to positive
arity.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

@[simp]
theorem Wikipedia.SzemeredisTheorem.generalizedConvolution_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    generalizedConvolution (n + 1)
      (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ)) z = 1 := by sorry
