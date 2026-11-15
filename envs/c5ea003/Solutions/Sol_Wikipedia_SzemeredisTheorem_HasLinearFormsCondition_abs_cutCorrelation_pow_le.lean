-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasLinearFormsCondition.abs_cutCorrelation_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:56:02.624491+00:00
-- url     : https://prove2.me/submissions/c17a45f2-eb83-4e21-a0db-da5aa38c0712

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HasLinearFormsCondition_hasFaceBooleanSubproductCondition
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_mean_centeredProduct_le_card_mul
import Theorems.Thm_Wikipedia_SzemeredisTheorem_coordinateCutForm_pow_le_boxMoment
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_faceCenteredProduct_eq_boxMoment

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





























































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















































/-- The coordinate theorem specialized to the cut correlation used by the
transference layer. -/
theorem cutCorrelation_pow_le_boxMoment
    {G : Type*} [Fintype G] [Nonempty G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r)
    (hu : IsAbsBoundedCutTest u) :
    cutCorrelation r f g u ^ (2 ^ r) ≤
      boxMoment r (fun x : Fin r → G =>
        f (∑ i, x i) - g (∑ i, x i)) := by
  simpa [cutCorrelation, coordinateCutForm] using
    coordinateCutForm_pow_le_boxMoment r
      (fun x : Fin r → G =>
        f (∑ i, x i) - g (∑ i, x i))
      u hu

/-- Absolute-value form in every positive dimension. -/
theorem abs_cutCorrelation_pow_le_boxMoment
    {G : Type*} [Fintype G] [Nonempty G] [AddCommGroup G]
    (n : ℕ) (f g : G → ℝ)
    (u : CutTestFamily G (n + 1))
    (hu : IsAbsBoundedCutTest u) :
    |cutCorrelation (n + 1) f g u| ^ (2 ^ (n + 1)) ≤
      boxMoment (n + 1)
        (fun x : Fin (n + 1) → G =>
          f (∑ i, x i) - g (∑ i, x i)) := by
  have heven : Even (2 ^ (n + 1)) :=
    even_two.pow_of_ne_zero (Nat.succ_ne_zero n)
  rw [heven.pow_abs]
  exact cutCorrelation_pow_le_boxMoment (n + 1) f g u hu



end Wikipedia.SzemeredisTheorem

end

section






/-!
# Algebraic strong-linear-forms primitives

This file contains the finite algebra behind the strong linear-forms and
densification arguments:

* centered factors `ν - 1`;
* products over Boolean cubes and corner systems;
* exact Boolean inclusion--exclusion expansions;
* cancellation of the constant terms;
* the resulting centered CFZ-moment estimate from the ordinary
  linear-forms condition;
* an `L²` contraction for coordinate-sum fiber convolutions, and a
  hypothesis-driven centered-moment consequence.

No analytic estimate for a sieve majorant is asserted here. Those estimates
must supply the explicit subproduct or moment hypotheses used below.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

















































/-- Cardinality-explicit version of the centered-product bound. -/
theorem abs_mean_centeredProduct_le_two_pow
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [Nonempty ι]
    {a : ι → Ω → ℝ} {η : ℝ}
    (h : HasBooleanSubproductCondition a η) :
    |mean (fun x => centeredProduct (fun i => a i x))| ≤
      (2 : ℝ) ^ Fintype.card ι * η := by
  classical
  simpa [BooleanCube, Fintype.card_fun, Fintype.card_bool] using
    abs_mean_centeredProduct_le_card_mul h

/-! ## Specialization to the CFZ linear-forms system -/



















/-! ## Fiber convolution and second moments -/















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
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl















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

















/-- A quantitative linear-forms condition bounds the centered moment on
each individual face. -/
theorem HasLinearFormsCondition.abs_mean_faceCenteredProduct_le
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition k N ν η)
    (j : Fin k) :
    |mean (faceCenteredProduct k N ν j)| ≤
      (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η := by
  change
    |mean (fun x =>
      centeredProduct
        (fun ω => faceFactorFamily k N ν j ω x))| ≤ _
  exact abs_mean_centeredProduct_le_two_pow
    (h.hasFaceBooleanSubproductCondition j)















/-- A deleted `n`-dimensional Boolean cube has `2 ^ n` vertices. -/
theorem card_deletedCube
    {n : ℕ} (j : Fin (n + 1)) :
    Fintype.card (DeletedCube (n + 1) j) = 2 ^ n := by
  calc
    Fintype.card (DeletedCube (n + 1) j) =
        Fintype.card (Fin n → Bool) :=
      Fintype.card_congr (deletedCubeEquiv j).symm
    _ = 2 ^ n := by
      simp [Fintype.card_bool]

/-- The linear-forms condition supplies the box-moment estimate required by
generalized von Neumann. -/
theorem HasLinearFormsCondition.abs_boxMoment_centeredSum_le
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition (n + 1) N ν η)
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) :
    |boxMoment n (fun y : Fin n → ZMod N =>
      ν (∑ i, y i) - 1)| ≤
        (2 : ℝ) ^ (2 ^ n) * η := by
  have hface := h.abs_mean_faceCenteredProduct_le j
  rw [mean_faceCenteredProduct_eq_boxMoment n N hN ν j,
    card_deletedCube] at hface
  exact hface





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

open Wikipedia.SzemeredisTheorem.HasLinearFormsCondition in
/-- Powered cut-correlation estimate obtained by composing generalized von
Neumann with the fixed-face linear-forms bound. -/
theorem solution
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition (n + 2) N ν η)
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (u : CutTestFamily (ZMod N) (n + 1))
    (hu : IsAbsBoundedCutTest u) :
    |cutCorrelation (n + 1) ν (fun _ => 1) u| ^
        (2 ^ (n + 1)) ≤
      (2 : ℝ) ^ (2 ^ (n + 1)) * η := by
  let j : Fin (n + 2) := 0
  have hvn :=
    abs_cutCorrelation_pow_le_boxMoment
      n ν (fun _ => 1) u hu
  have hbox :=
    h.abs_boxMoment_centeredSum_le hN j
  calc
    |cutCorrelation (n + 1) ν (fun _ => 1) u| ^
          (2 ^ (n + 1)) ≤
        boxMoment (n + 1)
          (fun x : Fin (n + 1) → ZMod N =>
            ν (∑ i, x i) - (fun _ => (1 : ℝ)) (∑ i, x i)) :=
      hvn
    _ = boxMoment (n + 1)
          (fun x : Fin (n + 1) → ZMod N =>
            ν (∑ i, x i) - 1) := by
      rfl
    _ ≤ |boxMoment (n + 1)
          (fun x : Fin (n + 1) → ZMod N =>
            ν (∑ i, x i) - 1)| :=
      le_abs_self _
    _ ≤ (2 : ℝ) ^ (2 ^ (n + 1)) * η :=
      hbox
