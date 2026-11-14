-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:49:47.505025+00:00
-- url     : https://prove2.me/theorems/6d89cd04-7799-4eb7-a80f-170a6018336c
-- title:
--   Finite test profiles and dual dense-model predicates
-- statement:
--   The normalized pairing of real functions on a finite space is $\langle f,q\rangle=\mathbb E(fq)$. The dense-model cube consists of the functions taking values in $[0,1]$. Pairing against a fixed test gives a continuous linear functional, and a finite test family gives a vector-valued profile map. The attainable-profile set is the image of the unit cube enlarged by the coordinate error cube $[-\varepsilon,\varepsilon]$.
--
--   The model predicate asks for a unit-bounded $g$ whose pairings with $f-g$ are at most $\varepsilon$ in absolute value for every test. The bundle supplies dual coefficients, their $\ell^1$ norm, finite test combinations, positive parts, and the sign-based error vector and support indicator used in separation.
--
--   The positive-part pseudorandomness condition is one-sided: the pairing of $\nu-1$ with the positive part of a test combination is at most $\varepsilon$ times its coefficient $\ell^1$ norm. A normalized version restricts that norm to one. No absolute-value bound is inserted into these two predicates.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean#L19-L713

import Mathlib.Analysis.LocallyConvex.Separation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Pointwise

/-- Normalized pairing on a finite probability space. -/
noncomputable def finitePairing
    {Ω : Type*} [Fintype Ω] (f q : Ω → ℝ) : ℝ :=
  mean (fun x => f x * q x)

theorem finitePairing_add_left
    {Ω : Type*} [Fintype Ω]
    (f g q : Ω → ℝ) :
    finitePairing (f + g) q =
      finitePairing f q + finitePairing g q := by
  rw [finitePairing, finitePairing, finitePairing, ← mean_add]
  apply congrArg mean
  funext x
  simp only [Pi.add_apply]
  ring







theorem finitePairing_smul_left
    {Ω : Type*} [Fintype Ω]
    (c : ℝ) (f q : Ω → ℝ) :
    finitePairing (c • f) q = c * finitePairing f q := by
  rw [finitePairing, finitePairing, ← mean_smul]
  apply congrArg mean
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring









/-- Pointwise membership in the dense-model cube. -/
def IsUnitBounded {Ω : Type*} (g : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧ ∀ x, g x ≤ 1









/-- The unit cube as a subset of the finite-dimensional function space. -/
def unitCubeSet (Ω : Type*) : Set (Ω → ℝ) :=
  {g | IsUnitBounded g}











/-- Pairing with a fixed test as a linear functional. -/
noncomputable def finitePairingLinearMap
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun f := finitePairing f q
  map_add' f g := finitePairing_add_left f g q
  map_smul' c f := by
    simpa [smul_eq_mul] using finitePairing_smul_left c f q

/-- Pairing is continuous because its domain is finite-dimensional. -/
noncomputable def finitePairingCLM
    {Ω : Type*} [Fintype Ω] (q : Ω → ℝ) :
    (Ω → ℝ) →L[ℝ] ℝ :=
  (finitePairingLinearMap q).toContinuousLinearMap



/-- The vector of pairings against a finite family of tests. -/
noncomputable def finiteTestProfile
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) :
    (Ω → ℝ) →L[ℝ] (τ → ℝ) :=
  ContinuousLinearMap.pi (fun t => finitePairingCLM (q t))



/-- Coordinatewise error cube in the finite profile space. -/
def profileErrorSet (τ : Type*) (ε : ℝ) : Set (τ → ℝ) :=
  Set.Icc (fun _ : τ => -ε) (fun _ => ε)











/-- Profiles attainable by a dense model, enlarged by the permitted
coordinatewise error. -/
noncomputable def denseModelProfileSet
    (Ω τ : Type*) [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ε : ℝ) : Set (τ → ℝ) :=
  finiteTestProfile q '' unitCubeSet Ω + profileErrorSet τ ε









/-- A bounded model matching `f` against every member of a finite test
family to accuracy `ε`. -/
def HasFiniteDenseModel
    {Ω τ : Type*} [Fintype Ω]
    (q : τ → Ω → ℝ) (f : Ω → ℝ) (ε : ℝ) : Prop :=
  ∃ g : Ω → ℝ, IsUnitBounded g ∧
    ∀ t, |finitePairing (f - g) (q t)| ≤ ε





/-- Coordinates of a continuous linear functional on a finite function
space, relative to the standard single-coordinate basis. -/
noncomputable def dualCoefficient
    {τ : Type*} [Fintype τ]
    (L : StrongDual ℝ (τ → ℝ)) (t : τ) : ℝ := by
  classical
  exact L (Pi.single t 1)



/-- The `ℓ¹` size of a coefficient vector. -/
noncomputable def coefficientL1
    {τ : Type*} [Fintype τ] (c : τ → ℝ) : ℝ :=
  ∑ t, |c t|









/-- Linear combination of a finite test family. -/
noncomputable def finiteTestCombination
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) : Ω → ℝ :=
  ∑ t, c t • q t









/-- The error vector which maximizes a dual functional on the
coordinatewise error cube. -/
noncomputable def dualErrorVector
    {τ : Type*} [Fintype τ]
    (ε : ℝ) (L : StrongDual ℝ (τ → ℝ)) : τ → ℝ :=
  fun t => ε *
    ((SignType.sign (dualCoefficient L t) : SignType) : ℝ)





/-- Pointwise positive part. -/
def positivePart {Ω : Type*} (q : Ω → ℝ) : Ω → ℝ :=
  fun x => max (q x) 0















/-- The Boolean vertex of the unit cube which maximizes pairing with `q`. -/
noncomputable def positiveSupportIndicator
    {Ω : Type*} (q : Ω → ℝ) : Ω → ℝ :=
  fun x => if 0 ≤ q x then 1 else 0















/-- The exact dual pseudorandomness hypothesis needed for a finite family
of tests.  It is homogeneous in the coefficients, so no separate
normalization convention is required. -/
def HasPositivePartCorrelationBound
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ) (ε : ℝ) : Prop :=
  ∀ c : τ → ℝ,
    finitePairing (ν - fun _ => 1)
        (positivePart (finiteTestCombination q c)) ≤
      ε * coefficientL1 c

/-- Unit-`ℓ¹` form of the positive-part pseudorandomness hypothesis. -/
def HasNormalizedPositivePartCorrelationBound
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ) (ε : ℝ) : Prop :=
  ∀ c : τ → ℝ, coefficientL1 c = 1 →
    finitePairing (ν - fun _ => 1)
        (positivePart (finiteTestCombination q c)) ≤ ε





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.IsUnitBounded.eq_1,
    `Wikipedia.SzemeredisTheorem.coefficientL1.eq_1,
    `Wikipedia.SzemeredisTheorem.dualCoefficient.eq_1,
    `Wikipedia.SzemeredisTheorem.dualErrorVector.eq_1,
    `Wikipedia.SzemeredisTheorem.finitePairing.eq_1,
    `Wikipedia.SzemeredisTheorem.finiteTestCombination.eq_1,
    `Wikipedia.SzemeredisTheorem.positivePart.eq_1,
    `Wikipedia.SzemeredisTheorem.positiveSupportIndicator.eq_1,
    `Wikipedia.SzemeredisTheorem.unitCubeSet.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


