-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.fiberConvolution_pairing_succ
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:09:55.996972+00:00
-- url     : https://prove2.me/submissions/be830163-c8ac-4c8e-87fd-81bdf7831c76

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

section


/-!
# Generalized convolutions on finite additive groups

For positive arity, the generalized convolution is the normalized average of
a weight over a fiber of the coordinate-sum map. At arity zero the sum map
has only the value zero, so the fiber density is a scaled delta function.
Keeping this scaling makes the pairing identity valid without an arity
exception; the `[0,1]` range statement is correctly restricted to positive
arity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





















@[simp]
theorem fiberConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (z : G) :
    fiberConvolution 0 w z =
      zeroFiberDelta z * w (fun i => Fin.elim0 i) :=
  rfl































































end Wikipedia.SzemeredisTheorem

end
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

open Wikipedia.SzemeredisTheorem in
/-- Disintegration over the coordinate-sum map at positive arity. -/
theorem solution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution (n + 1) w z) := by
  calc
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i) * w x) =
        mean (fun p : G × (Fin n → G) =>
          h p.1 * w (sumFiberTuple n p.1 p.2)) := by
      unfold mean
      apply Fintype.expect_equiv (sumFiberEquiv G n)
      intro x
      change h (∑ i, x i) * w x =
        h (∑ i, x i) *
          w (sumFiberTuple n (∑ i, x i) (Fin.tail x))
      have hx : sumFiberTuple n (∑ i, x i) (Fin.tail x) = x :=
        (sumFiberEquiv G n).left_inv x
      rw [hx]
    _ = mean₂ (fun z : G => fun y : Fin n → G =>
          h z * w (sumFiberTuple n z y)) := by
      simpa [mean, mean₂] using
        (Finset.expect_product (Finset.univ : Finset G)
          (Finset.univ : Finset (Fin n → G))
          (fun p : G × (Fin n → G) =>
            h p.1 * w (sumFiberTuple n p.1 p.2)))
    _ = mean (fun z : G =>
          h z * mean (fun y : Fin n → G =>
            w (sumFiberTuple n z y))) := by
      apply congrArg mean
      funext z
      exact mean_smul (h z) _
    _ = mean (fun z : G =>
          h z * fiberConvolution (n + 1) w z) := by
      rfl
