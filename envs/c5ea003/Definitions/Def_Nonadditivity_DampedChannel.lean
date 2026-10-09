-- Prove2me | Definitions.Def_Nonadditivity_DampedChannel
-- name    : Nonadditivity_DampedChannel
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:28.277319+00:00
-- url     : https://prove2.me/theorems/fd7eaf19-b5c5-435f-8ac9-661f4a3ad5f7
-- title:
--   Finite Kraus realization of a damped channel
-- statement:
--   For a finite channel $T$ and a Hermitian input matrix $F$ with $I-F^2$ positive semidefinite, the damped channel is $T(FXF)+\operatorname{Tr}((I-F^2)X)I_d/d$, where $d>0$ is the output dimension. Its Kraus family has retained operators $B_kF$ and replacement operators multiplied by the positive square root of $I-F^2$. The bundle proves completeness, the channel map, and adjoint formulas, including the traceless-observable case.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/DampedChannel.lean#L30-L157

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! # A concrete channel obtained by damping its input

The lost input mass is sent to the maximally mixed output. The displayed
formulas follow from an actual finite Kraus family, including its completeness
equation. On traceless observables the adjoint is exactly compression by the
chosen Hermitian contraction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

namespace Nonadditivity.DampedChannel
open Channels Channels.KrausChannel
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

/-- The positive square root of the discarded input mass. -/
def residualRoot (F : Matrix ι ι ℂ) : Matrix ι ι ℂ := CFC.sqrt (1-F*F)

theorem residualRoot_isHermitian (F : Matrix ι ι ℂ) :
    (residualRoot F).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian

theorem residualRoot_mul_self (F : Matrix ι ι ℂ)
    (hres : (1-F*F).PosSemidef) : residualRoot F * residualRoot F = 1-F*F :=
  CFC.sqrt_mul_sqrt_self _ hres.nonneg

/-- Elementary Kraus operators for replacing a state by its trace times I/d. -/
def replacementKraus (z : ο × ι) : Matrix ο ι ℂ :=
  (Real.sqrt (1/(Fintype.card ο:ℝ)):ℂ) • Matrix.single z.1 z.2 1

theorem replacementKraus_adjoint_sum (A : Matrix ο ο ℂ) :
    ∑ z : ο × ι, (replacementKraus z).conjTranspose * A * replacementKraus z =
      ((1/(Fintype.card ο:ℂ))*A.trace) • (1 : Matrix ι ι ℂ) := by
  have ht (a : ο) (i : ι) :
      (replacementKraus (a,i)).conjTranspose * A * replacementKraus (a,i) =
        (1/(Fintype.card ο:ℂ)) • Matrix.single i i (A a a) := by
    simp only [replacementKraus, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.conjTranspose_single,
      Complex.star_def, Complex.conj_ofReal, map_one,
      Matrix.single_mul_mul_single, one_mul, mul_one]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  simp only [Fintype.sum_prod_type, ht, ← Finset.smul_sum]
  ext i j
  by_cases h : i=j
  · subst j
    simp [Matrix.sum_apply, Matrix.single, Matrix.trace, Matrix.smul_apply]
  · have hf (x : ι) : ¬ (x=i ∧ x=j) := fun hx => h (hx.1.symm.trans hx.2)
    simp [Matrix.sum_apply, Matrix.single, Matrix.smul_apply, h, hf]

theorem replacementKraus_map_sum (X : Matrix ι ι ℂ) :
    ∑ z : ο × ι, replacementKraus z * X * (replacementKraus z).conjTranspose =
      ((1/(Fintype.card ο:ℂ))*X.trace) • (1 : Matrix ο ο ℂ) := by
  have ht (a : ο) (i : ι) :
      replacementKraus (a,i) * X * (replacementKraus (a,i)).conjTranspose =
        (1/(Fintype.card ο:ℂ)) • Matrix.single a a (X i i) := by
    simp only [replacementKraus, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.conjTranspose_single,
      Complex.star_def, Complex.conj_ofReal, map_one,
      Matrix.single_mul_mul_single, one_mul, mul_one]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  simp only [Fintype.sum_prod_type, ht, ← Finset.smul_sum]
  ext i j
  by_cases h : i=j
  · subst j
    simp [Matrix.sum_apply, Matrix.single, Matrix.trace, Matrix.smul_apply]
  · have hf (x : ο) : ¬ (x=i ∧ x=j) := fun hx => h (hx.1.symm.trans hx.2)
    simp [Matrix.sum_apply, Matrix.single, Matrix.smul_apply, h, hf]

theorem replacementKraus_complete :
    ∑ z : ο × ι, (replacementKraus z).conjTranspose * replacementKraus z =
      (1 : Matrix ι ι ℂ) := by
  simpa [Matrix.trace_one, Fintype.card_ne_zero] using
    replacementKraus_adjoint_sum (ι := ι) (1 : Matrix ο ο ℂ)

/-- Damping Kraus family: the retained branch and replacement branches. -/
def dampedKraus (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ) :
    κ ⊕ (ο × ι) → Matrix ο ι ℂ
  | Sum.inl k => T.kraus k * F
  | Sum.inr z => replacementKraus z * residualRoot F

/-- A genuine CPTP channel for any Hermitian F with F² ≤ I. -/
def damped (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) :
    KrausChannel ι ο (κ ⊕ (ο × ι)) where
  kraus := dampedKraus T F
  complete := by
    simp only [Fintype.sum_sum_type, dampedKraus, Matrix.conjTranspose_mul,
      hF.eq, (residualRoot_isHermitian F).eq, Matrix.mul_assoc]
    simp only [← Matrix.mul_sum]
    simp only [← Matrix.sum_mul, ← Matrix.mul_assoc]
    rw [T.complete, replacementKraus_complete, Matrix.mul_one, Matrix.mul_one,
      residualRoot_mul_self F hres]
    abel

@[simp] theorem damped_kraus_inl (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) (k : κ) :
    (damped T F hF hres).kraus (Sum.inl k) = T.kraus k * F := rfl

@[simp] theorem damped_kraus_inr (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) (z : ο × ι) :
    (damped T F hF hres).kraus (Sum.inr z) = replacementKraus z * residualRoot F := rfl

/-- The exact Schrödinger map, including the trace of the discarded mass. -/
theorem damped_map (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) (X : Matrix ι ι ℂ) :
    (damped T F hF hres).map X = T.map (F*X*F) +
      ((1/(Fintype.card ο:ℂ))*((1-F*F)*X).trace) • (1 : Matrix ο ο ℂ) := by
  have ht : (residualRoot F * X * residualRoot F).trace = ((1-F*F)*X).trace := by
    rw [Matrix.trace_mul_cycle, residualRoot_mul_self F hres]
  simp only [map, damped, Fintype.sum_sum_type, dampedKraus,
    Matrix.conjTranspose_mul, hF.eq, (residualRoot_isHermitian F).eq]
  simp only [Matrix.mul_assoc]
  rw [show (∑ z : ο × ι, replacementKraus z * (residualRoot F *
      (X * (residualRoot F * (replacementKraus z).conjTranspose)))) =
      ∑ z : ο × ι, replacementKraus z * (residualRoot F * X * residualRoot F) *
        (replacementKraus z).conjTranspose by simp only [Matrix.mul_assoc],
    replacementKraus_map_sum, ht]

/-- The exact Heisenberg map, before imposing trace zero. -/
theorem damped_adjointMap (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) (A : Matrix ο ο ℂ) :
    (damped T F hF hres).adjointMap A = F*T.adjointMap A*F +
      ((1/(Fintype.card ο:ℂ))*A.trace) • (1-F*F) := by
  have he : (damped T F hF hres).adjointMap A = F*T.adjointMap A*F +
      residualRoot F *
        (∑ z : ο × ι, (replacementKraus z).conjTranspose * A * replacementKraus z) *
          residualRoot F := by
    simp only [adjointMap, damped, Fintype.sum_sum_type, dampedKraus,
      Matrix.conjTranspose_mul, hF.eq, (residualRoot_isHermitian F).eq,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  rw [he]
  rw [replacementKraus_adjoint_sum]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    residualRoot_mul_self F hres]

/-- Damping acts by exact compression on every traceless observable. -/
theorem damped_adjointMap_traceless (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef) (A : Matrix ο ο ℂ)
    (hA : A.trace=0) :
    (damped T F hF hres).adjointMap A = F*T.adjointMap A*F := by
  simp [damped_adjointMap, hA]

end Nonadditivity.DampedChannel


