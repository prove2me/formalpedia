-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_cutDiscrepancy_model_of_monomialCorrelationBound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:34:42.068304+00:00
-- url     : https://prove2.me/submissions/e28ae087-6f12-40d4-8cee-947eb3e9ab5a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_cutCorrelation_le_of_boolean
import Theorems.Thm_Wikipedia_SzemeredisTheorem_fiberConvolution_pairing_succ
import Theorems.Thm_Wikipedia_SzemeredisTheorem_fiberConvolution_pairing_zero
import Theorems.Thm_Wikipedia_SzemeredisTheorem_hasFiniteDenseModel_of_positivePartCorrelationBound
import Theorems.Thm_Wikipedia_SzemeredisTheorem_hasNormalizedPositivePartCorrelationBound_of_polynomial
import Theorems.Thm_Wikipedia_SzemeredisTheorem_hasPositivePartCorrelationBound_of_normalized

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

@[simp]
theorem fiberConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ) (z : G) :
    fiberConvolution (n + 1) w z =
      mean fun y : Fin n → G => w (sumFiberTuple n z y) :=
  rfl





theorem cutTestProduct_nonneg
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (x : Fin r → G) :
    0 ≤ cutTestProduct u x :=
  Finset.prod_nonneg fun i _ => hu.nonneg i (eraseCoordinate i x)

theorem cutTestProduct_le_one
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (x : Fin r → G) :
    cutTestProduct u x ≤ 1 :=
  Finset.prod_le_one
    (fun i _ => hu.nonneg i (eraseCoordinate i x))
    (fun i _ => hu.le_one i (eraseCoordinate i x))





















theorem fiberConvolution_nonneg_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    (hw : ∀ x, 0 ≤ w x) (z : G) :
    0 ≤ fiberConvolution (n + 1) w z := by
  rw [fiberConvolution_succ]
  exact mean_nonneg fun y => hw (sumFiberTuple n z y)

theorem fiberConvolution_le_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    (hw : ∀ x, w x ≤ 1) (z : G) :
    fiberConvolution (n + 1) w z ≤ 1 := by
  rw [fiberConvolution_succ]
  exact mean_le_of_le_const fun y => hw (sumFiberTuple n z y)



theorem generalizedConvolution_nonneg_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {u : CutTestFamily G (n + 1)}
    (hu : IsBoundedCutTest u) (z : G) :
    0 ≤ generalizedConvolution (n + 1) u z :=
  fiberConvolution_nonneg_succ (cutTestProduct_nonneg hu) z

theorem generalizedConvolution_le_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {u : CutTestFamily G (n + 1)}
    (hu : IsBoundedCutTest u) (z : G) :
    generalizedConvolution (n + 1) u z ≤ 1 :=
  fiberConvolution_le_one_succ (cutTestProduct_le_one hu) z

theorem generalizedConvolution_mem_Icc
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (z : G) :
    generalizedConvolution r u z ∈ Set.Icc (0 : ℝ) 1 := by
  cases r with
  | zero => simp at hr
  | succ n =>
      exact ⟨generalizedConvolution_nonneg_succ hu z,
        generalizedConvolution_le_one_succ hu z⟩

theorem generalizedConvolution_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (z : G) :
    0 ≤ generalizedConvolution r u z :=
  (generalizedConvolution_mem_Icc hr hu z).1

theorem generalizedConvolution_le_one
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (z : G) :
    generalizedConvolution r u z ≤ 1 :=
  (generalizedConvolution_mem_Icc hr hu z).2









/-- Exact disintegration over the coordinate-sum map, including arity zero. -/
theorem fiberConvolution_pairing
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin r → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution r w z) := by
  cases r with
  | zero => exact fiberConvolution_pairing_zero w h
  | succ n => exact fiberConvolution_pairing_succ n w h





/-- A cut correlation is exactly the pairing of `f-g` with its generalized
convolution. -/
theorem cutCorrelation_eq_mean_mul_generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f g u =
      mean (fun z : G =>
        (f z - g z) * generalizedConvolution r u z) := by
  exact fiberConvolution_pairing r (cutTestProduct u)
    (fun z => f z - g z)

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite products and polynomial expansions -/







theorem polynomialCoefficientL1_nonneg (p : ℝ[X]) :
    0 ≤ polynomialCoefficientL1 p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _



















/-! ## Bounded combinations and approximation of positive part -/













/-! ## Quantitative positive-part correlation -/











/-- Homogeneous form of the polynomial dense-model estimate. -/
theorem hasPositivePartCorrelationBound_of_polynomial
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    HasPositivePartCorrelationBound q ν
      (polynomialCoefficientL1 p * η + δ * M) :=
  hasPositivePartCorrelationBound_of_normalized q ν _
    (hasNormalizedPositivePartCorrelationBound_of_polynomial
      hq hδ hp hM hmono)

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Reduction of bounded cut tests to Boolean cut tests

On a finite space, a `[0,1]`-valued cut-test family is a convex mixture of
its Boolean vertices.  Since every monomial in a cut correlation uses each
test coordinate at most once, the correlation is exactly the same convex
mixture of Boolean correlations.  Consequently it is enough to control the
finite family of Boolean cut tests in the dense-model theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite Bernoulli mixtures -/













/-! ## Boolean cut coordinates -/







theorem cutTestFamilyOfBooleanAssignment_bounded
    {G : Type*} {r : ℕ}
    (b : BooleanCutAssignment G r) :
    IsBoundedCutTest (cutTestFamilyOfBooleanAssignment b) := by
  constructor <;> intro i y <;>
    unfold cutTestFamilyOfBooleanAssignment booleanValue <;>
    split <;> norm_num













/-! ## The finite dense-model test family -/



/-- At positive arity every Boolean generalized convolution is
`[0,1]`-valued. -/
theorem booleanCutConvolution_unitBounded
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r)
    (b : BooleanCutAssignment G r) :
    IsUnitBounded (booleanCutConvolution r b) := by
  constructor
  · intro z
    exact generalizedConvolution_nonneg hr
      (cutTestFamilyOfBooleanAssignment_bounded b) z
  · intro z
    exact generalizedConvolution_le_one hr
      (cutTestFamilyOfBooleanAssignment_bounded b) z

/-- The finite Boolean convolution family is pointwise unit bounded at
positive arity. -/
theorem booleanCutConvolution_unitBoundedFamily
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) :
    IsUnitBoundedTestFamily
      (booleanCutConvolution (G := G) r) :=
  fun b => booleanCutConvolution_unitBounded hr b

/-- Pairing with a Boolean generalized convolution is exactly its Boolean
cut correlation. -/
theorem cutCorrelation_boolean_eq_pairing
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ)
    (b : BooleanCutAssignment G r) :
    cutCorrelation r f g
        (cutTestFamilyOfBooleanAssignment b) =
      finitePairing (f - g) (booleanCutConvolution r b) := by
  rw [cutCorrelation_eq_mean_mul_generalizedConvolution]
  rfl

/-- A model matching all finitely many Boolean generalized convolutions
already satisfies the full cut-discrepancy relation against arbitrary
`[0,1]`-valued cut tests. -/
theorem exists_cutDiscrepancy_model_of_finiteBooleanModel
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) {ε : ℝ}
    (hmodel :
      HasFiniteDenseModel
        (booleanCutConvolution (G := G) r) f ε) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe r f g ε := by
  obtain ⟨g, hg, hmatch⟩ := hmodel
  refine ⟨g, hg, ?_⟩
  intro u hu0 hu1
  apply abs_cutCorrelation_le_of_boolean u ⟨hu0, hu1⟩
  intro b
  rw [cutCorrelation_boolean_eq_pairing]
  exact hmatch b

/-- Dense-model theorem in the cut norm.  Its sole pseudorandomness input
is the homogeneous positive-part correlation bound for the finite family
of Boolean generalized convolutions. -/
theorem exists_cutDiscrepancy_model_of_positivePartCorrelationBound
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (r : ℕ) {f ν : G → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hpseudo :
      HasPositivePartCorrelationBound
        (booleanCutConvolution (G := G) r) ν ε) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe r f g ε := by
  apply exists_cutDiscrepancy_model_of_finiteBooleanModel r f
  exact hasFiniteDenseModel_of_positivePartCorrelationBound
    (booleanCutConvolution (G := G) r)
    hε hf0 hfν hpseudo



end Wikipedia.SzemeredisTheorem

end
/-!
# Reduction of bounded cut tests to Boolean cut tests

On a finite space, a `[0,1]`-valued cut-test family is a convex mixture of
its Boolean vertices.  Since every monomial in a cut correlation uses each
test coordinate at most once, the correlation is exactly the same convex
mixture of Boolean correlations.  Consequently it is enough to control the
finite family of Boolean cut tests in the dense-model theorem.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
/-! ## Finite Bernoulli mixtures -/
/-! ## Boolean cut coordinates -/
/-! ## The finite dense-model test family -/

open Wikipedia.SzemeredisTheorem in
/-- Polynomial dense-model theorem in the cut norm.  It replaces the
positive-part hypothesis by finite correlation estimates for products of
Boolean generalized convolutions, with all quantitative losses explicit. -/
theorem solution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (hr : 0 < r)
    {f ν : G → ℝ}
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound
        (booleanCutConvolution (G := G) r)
        ν p.natDegree η) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe r f g
        (polynomialCoefficientL1 p * η + δ * M) := by
  classical
  apply
    exists_cutDiscrepancy_model_of_positivePartCorrelationBound
      r
  · exact add_nonneg
      (mul_nonneg (polynomialCoefficientL1_nonneg p) hη)
      (mul_nonneg hδ hM0)
  · exact hf0
  · exact hfν
  · exact hasPositivePartCorrelationBound_of_polynomial
      (booleanCutConvolution_unitBoundedFamily hr)
      hδ hp hM hmono
