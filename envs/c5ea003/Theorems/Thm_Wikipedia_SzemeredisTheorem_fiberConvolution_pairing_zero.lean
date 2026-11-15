-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_fiberConvolution_pairing_zero
-- name    : Wikipedia.SzemeredisTheorem.fiberConvolution_pairing_zero
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:04:38.323071+00:00
-- url     : https://prove2.me/theorems/0d1fa689-a700-46ec-aea7-006f9e4124fb
-- title:
--   Disintegration of a zero-arity coordinate-sum pairing
-- statement:
--   Let $G$ be a finite additive commutative group, let $w$ be real-valued on the unique empty tuple, and let $h:G\to\mathbb R$. The normalized mean of $h$ of the empty coordinate sum times $w$ equals the normalized pairing of $h$ with the zero-arity fiber convolution of $w$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/GeneralizedConvolution.lean#L332-L355

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

theorem Wikipedia.SzemeredisTheorem.fiberConvolution_pairing_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin 0 → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution 0 w z) := by sorry
