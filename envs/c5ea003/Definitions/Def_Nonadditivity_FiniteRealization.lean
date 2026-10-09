-- Prove2me | Definitions.Def_Nonadditivity_FiniteRealization
-- name    : Nonadditivity_FiniteRealization
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:48.277355+00:00
-- url     : https://prove2.me/theorems/7e793000-f404-4b32-9a41-0cdd3e280d1d
-- title:
--   Finite real Hilbert space of traceless Hermitian observables
-- statement:
--   For a finite matrix index set $I$, matrices are represented by their entries in the Euclidean complex space $\mathbb C^{I\times I}$, viewed as a real inner product space. The observable subspace consists exactly of traceless Hermitian matrices; its norm is the unnormalized Hilbert–Schmidt norm. The channel adjoint restricted to this space is an actual bounded real linear map into the input matrices with operator norm. The bundle converts bounds on that map into the corresponding concrete matrix certificate.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/FiniteRealization.lean#L32-L145

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/






/-!
# Concrete Hilbert--Schmidt observable space and channel realizations

Observables are represented by their entries in a genuine Euclidean space,
whose norm is proved equal to the trace-defined Hilbert--Schmidt length.
The channel adjoint's output uses the Euclidean operator norm on matrices.
These distinct norms are never selected through competing matrix instances.
-/

noncomputable section

namespace Nonadditivity.FiniteRealization

open Nonadditivity.Entropy Nonadditivity.Channels Nonadditivity.AdjointPurity
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators

set_option backward.isDefEq.respectTransparency false

variable {ι D η : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype D] [DecidableEq D] [Fintype η]

/-- Matrices stored as Euclidean vectors of entries, with the HS norm. -/
abbrev EntrySpace (ι : Type*) := EuclideanSpace ℂ (ι × ι)

def entriesToMatrix (x : EntrySpace ι) : Matrix ι ι ℂ := fun i j => x (i, j)

def matrixToEntries (A : Matrix ι ι ℂ) : EntrySpace ι :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem entriesToMatrix_matrixToEntries (A : Matrix ι ι ℂ) :
    entriesToMatrix (matrixToEntries A) = A := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem matrixToEntries_entriesToMatrix (x : EntrySpace ι) :
    matrixToEntries (entriesToMatrix x) = x := rfl

omit [DecidableEq ι] in
/-- The Euclidean norm of the entry vector is exactly the trace HS length. -/
theorem norm_matrixToEntries_eq_hsLength (A : Matrix ι ι ℂ) :
    ‖matrixToEntries A‖ = hsLength A := by
  have htrace : (A.conjTranspose * A).trace.re = ∑ ij : ι × ι, ‖A ij.1 ij.2‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hnorm := EuclideanSpace.norm_sq_eq (matrixToEntries A)
  have hsq := hsLength_sq A
  rw [htrace] at hsq
  change ‖matrixToEntries A‖ ^ 2 = ∑ ij : ι × ι, ‖A ij.1 ij.2‖ ^ 2 at hnorm
  nlinarith [norm_nonneg (matrixToEntries A), hsLength_nonneg A]

/-- Real-linear conversion is required because Hermitian matrices form a
real vector space. -/
def entriesToMatrixLinear : EntrySpace ι →ₗ[ℝ] Matrix ι ι ℂ where
  toFun := entriesToMatrix
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The concrete real subspace of traceless Hermitian HS observables. -/
def observableSubmodule (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Submodule ℝ (EntrySpace ι) where
  carrier := {x | (entriesToMatrix x).IsHermitian ∧ (entriesToMatrix x).trace = 0}
  zero_mem' := by
    change (entriesToMatrix (0 : EntrySpace ι)).IsHermitian ∧
      (entriesToMatrix (0 : EntrySpace ι)).trace = 0
    change (0 : Matrix ι ι ℂ).IsHermitian ∧ (0 : Matrix ι ι ℂ).trace = 0
    simp
  add_mem' := by
    intro x y hx hy
    constructor
    · change (entriesToMatrix x + entriesToMatrix y).IsHermitian
      exact hx.1.add hy.1
    · change (entriesToMatrix x + entriesToMatrix y).trace = 0
      simp [Matrix.trace_add, hx.2, hy.2]
  smul_mem' := by
    intro r x hx
    have hsmul : entriesToMatrix (r • x) = (r : ℂ) • entriesToMatrix x := rfl
    change (entriesToMatrix (r • x)).IsHermitian ∧ (entriesToMatrix (r • x)).trace = 0
    rw [hsmul]
    constructor
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul, hx.1.eq]
      simp
    · simp [Matrix.trace_smul, hx.2]

abbrev ObservableSpace (ι : Type*) [Fintype ι] [DecidableEq ι] := observableSubmodule ι

def observableMatrix (x : ObservableSpace ι) : Matrix ι ι ℂ := entriesToMatrix x.val

theorem observableMatrix_isHermitian (x : ObservableSpace ι) :
    (observableMatrix x).IsHermitian := x.property.1

theorem observableMatrix_trace_zero (x : ObservableSpace ι) :
    (observableMatrix x).trace = 0 := x.property.2

theorem observable_norm_eq_hsLength (x : ObservableSpace ι) :
    ‖x‖ = hsLength (observableMatrix x) := by
  change ‖x.val‖ = hsLength (entriesToMatrix x.val)
  simpa using norm_matrixToEntries_eq_hsLength (entriesToMatrix x.val)

/-- The channel adjoint restricted to actual HS observables, with operator
norm in its codomain. Continuity follows from the concrete finite dimension. -/
def adjointOnObservables (T : KrausChannel D ι η) :
    ObservableSpace ι →L[ℝ] Matrix D D ℂ :=
  ((T.adjointLinearMap.restrictScalars ℝ).comp
    (entriesToMatrixLinear.comp (observableSubmodule ι).subtype)).toContinuousLinearMap

@[simp] theorem adjointOnObservables_apply (T : KrausChannel D ι η)
    (x : ObservableSpace ι) :
    adjointOnObservables T x = T.adjointMap (observableMatrix x) := rfl

/-- Turn a matrix satisfying the manuscript's test conditions into an actual
element of the finite-dimensional real observable space. -/
def matrixObservable (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (htrace : A.trace = 0) :
    ObservableSpace ι :=
  ⟨matrixToEntries A, by
    change (entriesToMatrix (matrixToEntries A)).IsHermitian ∧
      (entriesToMatrix (matrixToEntries A)).trace = 0
    simpa only [entriesToMatrix_matrixToEntries] using And.intro hA htrace⟩

@[simp] theorem observableMatrix_matrixObservable (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (htrace : A.trace = 0) :
    observableMatrix (matrixObservable A hA htrace) = A := rfl

/-- A norm certificate for the actual restricted continuous map implies
the precise matrix certificate used by the channel entropy theorem. -/
theorem matrix_certificate_of_observable_bound (T : KrausChannel D ι η) (C : ℝ)
    (hbound : ∀ x : ObservableSpace ι, ‖adjointOnObservables T x‖ ≤ C * ‖x‖) :
    ∀ A : Matrix ι ι ℂ, A.IsHermitian → A.trace = 0 →
      ‖T.adjointMap A‖ ≤ C * hsLength A := by
  intro A hA htrace
  have h := hbound (matrixObservable A hA htrace)
  simpa only [adjointOnObservables_apply, observable_norm_eq_hsLength,
    observableMatrix_matrixObservable] using h







end Nonadditivity.FiniteRealization


