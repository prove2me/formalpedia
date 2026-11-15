-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:59:42.697198+00:00
-- url     : https://prove2.me/theorems/a14e4e17-3003-4c2a-bec0-ef0717a47e3c
-- title:
--   Finite uniform mixtures of bounded generalized convolutions
-- statement:
--   A convolution mixture records a nonempty finite index type and a bounded cut-test family at each index. Over a finite additive commutative group, it evaluates to the uniform mean of the corresponding generalized convolutions.
--
--   The bundle constructs a one-point mixture from a single bounded test and a constant-one mixture at positive arity. It also constructs the product mixture by adjoining the two mixture indices and a zero-sum displacement parameter. The translated product cut test multiplies the first test by the second test shifted along that displacement. This records the finite convex-mixture representation used to establish multiplicative closure.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/ConvolutionClosure.lean#L53-L252

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Multiplicative closure of generalized convolutions

The dense-model proof tests against generalized convolutions.  Products of
these tests remain convex averages of generalized convolutions: two points
in the same coordinate-sum fiber differ by a tuple of sum zero, and fixing
that difference turns the two cut products into one cut product.

This file proves the exact finite identity, packages finite convex mixtures,
and transfers a single cut-discrepancy estimate to every monomial required
by polynomial dense-model duality.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

universe u



/-- The unique zero-sum `(n+1)`-tuple whose tail is `d`. -/
def zeroSumShift
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (d : Fin n → G) : Fin (n + 1) → G :=
  sumFiberTuple n 0 d





/-- For a fixed zero-sum displacement, multiply the two deleted-coordinate
test families after translating the second one. -/
def convolutionProductCutTest
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (u v : CutTestFamily G (n + 1))
    (d : Fin n → G) :
    CutTestFamily G (n + 1) :=
  fun i y =>
    u i y *
      v i (fun t =>
        y t + eraseCoordinate i (zeroSumShift n d) t)

theorem convolutionProductCutTest_bounded
    {G : Type*} [AddCommGroup G] {n : ℕ}
    {u v : CutTestFamily G (n + 1)}
    (hu : IsBoundedCutTest u) (hv : IsBoundedCutTest v)
    (d : Fin n → G) :
    IsBoundedCutTest
      (convolutionProductCutTest n u v d) := by
  constructor
  · intro i y
    exact mul_nonneg (hu.nonneg i y)
      (hv.nonneg i
        (fun t =>
          y t + eraseCoordinate i (zeroSumShift n d) t))
  · intro i y
    exact mul_le_one₀ (hu.le_one i y)
      (hv.nonneg i
        (fun t =>
          y t + eraseCoordinate i (zeroSumShift n d) t))
      (hv.le_one i
        (fun t =>
          y t + eraseCoordinate i (zeroSumShift n d) t))







/-! ## Finite convex mixtures -/

/-- A finite convex average of bounded generalized convolutions.  Uniform
averages suffice because every multiplication step below naturally
introduces one more finite uniform parameter. -/
structure ConvolutionMixture
    (G : Type u) [AddCommGroup G] (r : ℕ) where
  ι : Type u
  indexFintype : Fintype ι
  indexNonempty : Nonempty ι
  tests : ι → CutTestFamily G r
  bounded : ∀ a, IsBoundedCutTest (tests a)

namespace ConvolutionMixture

/-- The function represented by a finite convolution mixture. -/
noncomputable def eval
    {G : Type u} [Fintype G] [AddCommGroup G] {r : ℕ}
    (m : ConvolutionMixture G r) : G → ℝ :=
  letI : Fintype m.ι := m.indexFintype
  fun z => mean (fun a => generalizedConvolution r (m.tests a) z)

/-- A single generalized convolution as a one-point mixture. -/
def pure
    {G : Type u} [AddCommGroup G] {r : ℕ}
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u) :
    ConvolutionMixture G r where
  ι := ULift.{u} Unit
  indexFintype := inferInstance
  indexNonempty := inferInstance
  tests := fun _ => u
  bounded := fun _ => hu



/-- The constant-one function represented as a generalized convolution at
positive arity. -/
def one
    {G : Type u} [AddCommGroup G] (n : ℕ) :
    ConvolutionMixture G (n + 1) :=
  pure
    (fun _ : Fin (n + 1) =>
      fun _ : Fin n → G => (1 : ℝ))
    isBoundedCutTest_one



/-- Multiply two mixtures by adjoining the two mixture indices and the
zero-sum displacement parameter from
`generalizedConvolution_mul_eq_mean`. -/
noncomputable def mul
    {G : Type u} [Fintype G] [AddCommGroup G] (n : ℕ)
    (m₁ m₂ : ConvolutionMixture G (n + 1)) :
    ConvolutionMixture G (n + 1) := by
  letI : Fintype m₁.ι := m₁.indexFintype
  letI : Fintype m₂.ι := m₂.indexFintype
  letI : Nonempty m₁.ι := m₁.indexNonempty
  letI : Nonempty m₂.ι := m₂.indexNonempty
  exact
    { ι := m₁.ι × (m₂.ι × (Fin n → G))
      indexFintype := inferInstance
      indexNonempty := inferInstance
      tests := fun p =>
        convolutionProductCutTest n
          (m₁.tests p.1) (m₂.tests p.2.1) p.2.2
      bounded := fun p =>
        convolutionProductCutTest_bounded
          (m₁.bounded p.1) (m₂.bounded p.2.1) p.2.2 }







end ConvolutionMixture

/-! ## Consequences for dense-model moments -/











end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.ConvolutionMixture.ctorIdx,
    `Wikipedia.SzemeredisTheorem.ConvolutionMixture.mk.inj,
    `Wikipedia.SzemeredisTheorem.ConvolutionMixture.mk.injEq,
    `Wikipedia.SzemeredisTheorem.ConvolutionMixture.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.ConvolutionMixture.noConfusionType,
    `Wikipedia.SzemeredisTheorem.ConvolutionMixture.one.eq_1,
    `Wikipedia.SzemeredisTheorem.convolutionProductCutTest.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


