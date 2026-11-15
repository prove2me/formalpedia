-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_faceCenteredProduct_eq_boxMoment
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:54:40.977784+00:00
-- url     : https://prove2.me/submissions/593223f6-7300-4e5b-8bf5-838370ab5a17

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_boxMoment_eq_cubeMean
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_faceCenteredProduct_eq_weightedCube

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Transport of cut discrepancy by coordinate automorphisms

Arithmetic-progression face forms are weighted coordinate sums rather than
literal sums.  When every coefficient acts by an additive automorphism, a
coordinatewise change of variables reduces them to the literal sum used in
`CutDiscrepancyLe`.  This file proves that reduction once and for all.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem mulAddEquivOfIsUnit_apply
    {R : Type*} [CommRing R] (a : R) (ha : IsUnit a)
    (x : R) :
    mulAddEquivOfIsUnit a ha x = a * x := by
  change (ha.unit : R) * x = a * x
  rw [IsUnit.unit_spec]

















end Wikipedia.SzemeredisTheorem

end

section



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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators















@[simp]
theorem boxMoment_zero {G : Type*} [Fintype G]
    (F : (Fin 0 → G) → ℝ) :
    boxMoment 0 F = mean F :=
  rfl







@[simp]
theorem endpointTupleEquiv_apply_fst
    {G : Type*} {n : ℕ}
    (x : Fin n → Bool → G) (i : Fin n) :
    (endpointTupleEquiv x i).1 = x i false :=
  rfl

@[simp]
theorem endpointTupleEquiv_apply_snd
    {G : Type*} {n : ℕ}
    (x : Fin n → Bool → G) (i : Fin n) :
    (endpointTupleEquiv x i).2 = x i true :=
  rfl



/-- The endpoint-function and endpoint-pair presentations give the same
cube average. -/
theorem cubeFunctionMean_eq_cubeMean
    {G : Type*} [Fintype G]
    (n : ℕ) (F : (Fin n → G) → ℝ) :
    cubeFunctionMean n F = cubeMean n F := by
  unfold cubeFunctionMean cubeMean mean
  apply Fintype.expect_equiv (endpointTupleEquiv (G := G) (n := n))
  intro x
  apply Finset.prod_congr rfl
  intro ω _
  apply congrArg F
  funext i
  cases h : ω i <;> simp [cubeVertex, h]







































end Wikipedia.SzemeredisTheorem

end

section






/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





@[simp]
theorem apCoefficientAddEquiv_apply
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) (x : ZMod N) :
    apCoefficientAddEquiv hN i j hij x =
      (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x := by
  simp [apCoefficientAddEquiv]

















@[simp]
theorem apFaceScalingEquiv_apply
    {n N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) (t : Fin n) (x : ZMod N) :
    apFaceScalingEquiv hN j t x =
      ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
        ZMod N) * x) := by
  simp [apFaceScalingEquiv]

end Wikipedia.SzemeredisTheorem

end

section





/-!
# Centered moments on one progression face

The CFZ linear-forms condition controls every Boolean subproduct of the
forms belonging to a fixed deleted coordinate.  Inclusion--exclusion then
bounds the product of all centered factors on that face.  This is the
linear-forms estimate that appears at the endpoint of the generalized
von Neumann Cauchy--Schwarz argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





























/-- Coordinatewise additive automorphisms transport a weighted cube mean to
the ordinary coordinate-sum cube mean. -/
theorem mean_weightedCube_eq_cubeFunctionMean
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (e : Fin n → G ≃+ G) (h : G → ℝ) :
    mean (fun x : Fin n → Bool → G =>
      ∏ ω : Fin n → Bool,
        h (∑ i, e i (x i (ω i)))) =
      cubeFunctionMean n
        (fun y : Fin n → G => h (∑ i, y i)) := by
  unfold cubeFunctionMean mean
  apply Fintype.expect_equiv (endpointScalingEquiv e)
  intro x
  apply Finset.prod_congr rfl
  intro ω _
  congr 1











end Wikipedia.SzemeredisTheorem

end
/-!
# Centered moments on one progression face

The CFZ linear-forms condition controls every Boolean subproduct of the
forms belonging to a fixed deleted coordinate.  Inclusion--exclusion then
bounds the product of all centered factors on that face.  This is the
linear-forms estimate that appears at the endpoint of the generalized
von Neumann Cauchy--Schwarz argument.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Under the AP factorial coprimality hypothesis, the centered face moment
is exactly the ordinary box moment of the centered majorant composed with
coordinate sum. -/
theorem solution
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial n))
    (ν : ZMod N → ℝ) (j : Fin (n + 1)) :
    mean (faceCenteredProduct (n + 1) N ν j) =
      boxMoment n (fun y : Fin n → ZMod N =>
        ν (∑ i, y i) - 1) := by
  calc
    mean (faceCenteredProduct (n + 1) N ν j) =
        mean (fun y : Fin n → Bool → ZMod N =>
          ∏ ω : Fin n → Bool,
            (ν (∑ t : Fin n,
              ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
                ZMod N) * y t (ω t))) - 1)) :=
      mean_faceCenteredProduct_eq_weightedCube n N ν j
    _ = cubeFunctionMean n
          (fun y : Fin n → ZMod N =>
            ν (∑ i, y i) - 1) := by
      simpa using
        mean_weightedCube_eq_cubeFunctionMean n
          (fun t => apFaceScalingEquiv hN j t)
          (fun z => ν z - 1)
    _ = cubeMean n
          (fun y : Fin n → ZMod N =>
            ν (∑ i, y i) - 1) :=
      cubeFunctionMean_eq_cubeMean _ _
    _ = boxMoment n
          (fun y : Fin n → ZMod N =>
            ν (∑ i, y i) - 1) :=
      (boxMoment_eq_cubeMean _ _).symm
