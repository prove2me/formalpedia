-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.fiberConvolution_pairing_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:11:52.557208+00:00
-- url     : https://prove2.me/submissions/3342ce6e-100b-4c3a-a59e-1f25fe8f54be

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
/-- Disintegration over the zero-coordinate sum map. -/
theorem solution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin 0 → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution 0 w z) := by
  classical
  let e : Fin 0 → G := fun i => Fin.elim0 i
  calc
    mean (fun x : Fin 0 → G => h (∑ i, x i) * w x) =
        h 0 * w e := by
      have heq :
          (fun x : Fin 0 → G => h (∑ i, x i) * w x) =
            (fun _ : Fin 0 → G => h 0 * w e) := by
        funext x
        have hx : x = e := Subsingleton.elim _ _
        subst x
        simp [e]
      rw [heq]
      exact mean_const _
    _ = mean (fun z : G => h z * fiberConvolution 0 w z) := by
      rw [mean, Fintype.expect_eq_sum_div_card]
      simp [fiberConvolution_arity_zero, zeroFiberDelta, e]
      field_simp
