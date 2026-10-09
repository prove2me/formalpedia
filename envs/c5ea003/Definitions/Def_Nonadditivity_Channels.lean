-- Prove2me | Definitions.Def_Nonadditivity_Channels
-- name    : Nonadditivity_Channels
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:21:43.581035+00:00
-- url     : https://prove2.me/theorems/91f24dbc-8562-4202-ae26-b84552597d54
-- title:
--   Finite Kraus quantum channels and their matrix operations
-- statement:
--   A finite Kraus channel is a family of matrices $A_k$ satisfying $\sum_k A_k^*A_k=I$. It acts by $X\mapsto\sum_k A_kXA_k^*$, preserving positivity and trace and therefore mapping density matrices to density matrices. The interface supplies the adjoint under the trace pairing, tensor products, identity and conjugate channels, complementary channels, and random unitary channels. The matrix formulas and completeness proofs accompany these constructions.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/Channels.lean#L28-L334

import Definitions.Def_Nonadditivity_Entropy
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-!
# Concrete finite-dimensional channels

Channels are finite rectangular Kraus families satisfying the actual matrix
completeness equation. Positivity, trace preservation, ancilla positivity,
composition, tensor products and conjugate channels are proved from that data.
No abstract channel-property hypotheses are used to establish these facts.
-/

noncomputable section

namespace Nonadditivity.Channels

open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix
open Nonadditivity.Entropy

variable {ι ο κ μ ν η : Type*}

/-- A finite Kraus realization of a completely positive trace-preserving map. -/
structure KrausChannel (ι ο κ : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype ο] [Fintype κ] where
  kraus : κ → Matrix ο ι ℂ
  complete : ∑ k, (kraus k).conjTranspose * kraus k = 1

namespace KrausChannel

variable [Fintype ι] [DecidableEq ι] [Fintype ο] [Fintype κ]

/-- The Schrödinger map is the finite Kraus sum. -/
def map (T : KrausChannel ι ο κ) (X : Matrix ι ι ℂ) : Matrix ο ο ℂ :=
  ∑ k, T.kraus k * X * (T.kraus k).conjTranspose

@[simp] theorem map_add (T : KrausChannel ι ο κ) (X Y : Matrix ι ι ℂ) :
    T.map (X + Y) = T.map X + T.map Y := by
  simp [map, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

@[simp] theorem map_smul (T : KrausChannel ι ο κ) (c : ℂ) (X : Matrix ι ι ℂ) :
    T.map (c • X) = c • T.map X := by
  simp [map, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

@[simp] theorem map_zero (T : KrausChannel ι ο κ) : T.map 0 = 0 := by simp [map]

/-- The Kraus map as an actual complex linear map. -/
def linearMap (T : KrausChannel ι ο κ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix ο ο ℂ where
  toFun := T.map
  map_add' := T.map_add
  map_smul' := T.map_smul

/-- Positivity is derived from the Kraus matrices by congruence. -/
theorem map_posSemidef (T : KrausChannel ι ο κ) (X : Matrix ι ι ℂ)
    (hX : X.PosSemidef) : (T.map X).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ (fun k _ =>
    hX.mul_mul_conjTranspose_same (T.kraus k))

/-- Trace preservation holds for every input matrix. -/
@[simp] theorem trace_map (T : KrausChannel ι ο κ) (X : Matrix ι ι ℂ) :
    (T.map X).trace = X.trace := by
  calc
    (T.map X).trace = ∑ k, (X * ((T.kraus k).conjTranspose * T.kraus k)).trace := by
      simp only [map, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    _ = (X * (∑ k, (T.kraus k).conjTranspose * T.kraus k)).trace := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
    _ = X.trace := by rw [T.complete, Matrix.mul_one]

/-- Applying a concrete channel produces a concrete density matrix. -/
def output [DecidableEq ο] (T : KrausChannel ι ο κ) (ρ : DensityMatrix ι) :
    DensityMatrix ο where
  matrix := T.map ρ.matrix
  positive := T.map_posSemidef ρ.matrix ρ.positive
  normalized := (T.trace_map ρ.matrix).trans ρ.normalized

@[simp] theorem output_matrix [DecidableEq ο] (T : KrausChannel ι ο κ)
    (ρ : DensityMatrix ι) : (T.output ρ).matrix = T.map ρ.matrix := rfl

/-- A single identity Kraus operator. -/
def identity : KrausChannel ι ι Unit where
  kraus := fun _ => 1
  complete := by simp

@[simp] theorem identity_map (X : Matrix ι ι ℂ) :
    (identity : KrausChannel ι ι Unit).map X = X := by simp [identity, map]

/-- A single unitary Kraus operator. -/
def unitaryChannel (U : unitary (Matrix ι ι ℂ)) : KrausChannel ι ι Unit where
  kraus := fun _ => U
  complete := by simp [← Matrix.star_eq_conjTranspose]

@[simp] theorem unitaryChannel_map (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    (unitaryChannel U).map X = (U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ).conjTranspose := by
  simp [unitaryChannel, map]

/-- The Hilbert–Schmidt adjoint channel on observables. -/
def adjointMap (T : KrausChannel ι ο κ) (Y : Matrix ο ο ℂ) : Matrix ι ι ℂ :=
  ∑ k, (T.kraus k).conjTranspose * Y * T.kraus k

@[simp] theorem adjointMap_add (T : KrausChannel ι ο κ) (X Y : Matrix ο ο ℂ) :
    T.adjointMap (X + Y) = T.adjointMap X + T.adjointMap Y := by
  simp [adjointMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

@[simp] theorem adjointMap_smul (T : KrausChannel ι ο κ) (c : ℂ) (X : Matrix ο ο ℂ) :
    T.adjointMap (c • X) = c • T.adjointMap X := by
  simp [adjointMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- The adjoint on observables as an actual complex linear map. -/
def adjointLinearMap (T : KrausChannel ι ο κ) : Matrix ο ο ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun := T.adjointMap
  map_add' := T.adjointMap_add
  map_smul' := T.adjointMap_smul

/-- The adjoint preserves Hermitian observables, including nonpositive ones. -/
theorem adjointMap_isHermitian (T : KrausChannel ι ο κ) (Y : Matrix ο ο ℂ)
    (hY : Y.IsHermitian) : (T.adjointMap Y).IsHermitian := by
  change Y.conjTranspose = Y at hY
  unfold Matrix.IsHermitian adjointMap
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hY, Matrix.mul_assoc]



@[simp] theorem adjointMap_one [DecidableEq ο] (T : KrausChannel ι ο κ) :
    T.adjointMap 1 = 1 := by simp [adjointMap, T.complete]

/-- The defining trace duality is proved directly, including rectangular Kraus operators. -/
theorem trace_duality (T : KrausChannel ι ο κ) (X : Matrix ι ι ℂ) (Y : Matrix ο ο ℂ) :
    (T.map X * Y).trace = (X * T.adjointMap Y).trace := by
  simp only [map, adjointMap, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    ((T.kraus k * X * (T.kraus k).conjTranspose) * Y).trace =
        (T.kraus k * (X * (T.kraus k).conjTranspose * Y)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((X * (T.kraus k).conjTranspose * Y) * T.kraus k).trace :=
      Matrix.trace_mul_comm _ _
    _ = (X * ((T.kraus k).conjTranspose * Y * T.kraus k)).trace := by
      simp only [Matrix.mul_assoc]

/-- A random unitary channel with any genuine probability distribution. -/
def randomUnitary (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1)
    (U : κ → unitary (Matrix ι ι ℂ)) : KrausChannel ι ι κ where
  kraus := fun k => (Real.sqrt (p k) : ℂ) • (U k : Matrix ι ι ℂ)
  complete := by
    have hTerm (k : κ) :
        ((Real.sqrt (p k) : ℂ) • (U k : Matrix ι ι ℂ)).conjTranspose *
          ((Real.sqrt (p k) : ℂ) • (U k : Matrix ι ι ℂ)) = (p k : ℂ) • (1 : Matrix ι ι ℂ) := by
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [← Matrix.star_eq_conjTranspose]
      simp [← Complex.ofReal_mul, Real.mul_self_sqrt (hp k)]
    simp_rw [hTerm]
    rw [← Finset.sum_smul]
    have hSum : ∑ k, (p k : ℂ) = 1 := by exact_mod_cast hsum
    rw [hSum, one_smul]

/-- The random-unitary channel's map is the advertised convex combination. -/
theorem randomUnitary_map (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : ∑ k, p k = 1) (U : κ → unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    (randomUnitary p hp hsum U).map X =
      ∑ k, (p k : ℂ) • ((U k : Matrix ι ι ℂ) * X * (U k : Matrix ι ι ℂ).conjTranspose) := by
  simp only [map, randomUnitary]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp [← Complex.ofReal_mul, Real.mul_self_sqrt (hp k)]

/-- Uniform mixing of an arbitrary nonempty finite unitary family. -/
def uniformUnitary [Nonempty κ] (U : κ → unitary (Matrix ι ι ℂ)) :
    KrausChannel ι ι κ :=
  randomUnitary (fun _ => 1 / (Fintype.card κ : ℝ)) (fun _ => by positivity)
    (by simp [Fintype.card_ne_zero]) U

/-- The complementary channel swaps the output and environment coordinates
of the Stinespring Kraus tensor. -/
def complementary (T : KrausChannel ι ο κ) : KrausChannel ι κ ο where
  kraus := fun b e a => T.kraus e b a
  complete := by
    ext i j
    have h := congrArg (fun M : Matrix ι ι ℂ => M i j) T.complete
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h ⊢
    rw [Finset.sum_comm]
    exact h



/-- A trace-preserving isometric embedding, with one rectangular Kraus operator. -/
def isometryChannel (V : Matrix ο ι ℂ) (hV : V.conjTranspose * V = 1) :
    KrausChannel ι ο Unit where
  kraus := fun _ => V
  complete := by simpa using hV

/-- The actual Stinespring isometry, retaining both output and environment indices. -/
def stinespring (T : KrausChannel ι ο κ) : Matrix (ο × κ) ι ℂ :=
  fun z a => T.kraus z.2 z.1 a

/-- Kraus completeness proves the Stinespring matrix is isometric. -/
theorem stinespring_isometry (T : KrausChannel ι ο κ) :
    T.stinespring.conjTranspose * T.stinespring = 1 := by
  ext i j
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) T.complete
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  simp only [stinespring, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact h

/-- A genuine joint-output channel, before either subsystem is traced out. -/
def stinespringChannel (T : KrausChannel ι ο κ) : KrausChannel ι (ο × κ) Unit :=
  isometryChannel T.stinespring T.stinespring_isometry

@[simp] theorem stinespringChannel_map (T : KrausChannel ι ο κ) (X : Matrix ι ι ℂ) :
    T.stinespringChannel.map X = T.stinespring * X * T.stinespring.conjTranspose := by
  simp [stinespringChannel, isometryChannel, map]





end KrausChannel

section Operations

variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο]
variable [Fintype κ] [Fintype μ] [DecidableEq μ] [Fintype ν] [Fintype η]

namespace KrausChannel





/-- Tensor channels use the Kronecker products of their Kraus operators. -/
def tensor (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η) :
    KrausChannel (ι × μ) (ο × ν) (κ × η) where
  kraus := fun z => T.kraus z.1 ⊗ₖ S.kraus z.2
  complete := by
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Fintype.sum_prod_type]
    calc
      (∑ k, ∑ l, ((T.kraus k).conjTranspose * T.kraus k) ⊗ₖ
        ((S.kraus l).conjTranspose * S.kraus l)) =
          (∑ k, (T.kraus k).conjTranspose * T.kraus k) ⊗ₖ
            (∑ l, (S.kraus l).conjTranspose * S.kraus l) := by
        ext ⟨a,b⟩ ⟨c,d⟩
        simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
      _ = 1 := by rw [T.complete, S.complete, Matrix.one_kronecker_one]

omit [DecidableEq ο] in
/-- Tensor channels map product inputs to product outputs. -/
theorem tensor_map (T : KrausChannel ι ο κ) (S : KrausChannel μ ν η)
    (X : Matrix ι ι ℂ) (Y : Matrix μ μ ℂ) :
    (T.tensor S).map (X ⊗ₖ Y) = T.map X ⊗ₖ S.map Y := by
  simp only [map, tensor, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Fintype.sum_prod_type]
  ext ⟨a,b⟩ ⟨c,d⟩
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]





/-- Complex conjugation of every Kraus operator. -/
def conjugate (T : KrausChannel ι ο κ) : KrausChannel ι ο κ where
  kraus := fun k => (T.kraus k).map star
  complete := by
    have h := congrArg (fun M : Matrix ι ι ℂ => M.map star) T.complete
    ext i j
    have hij := congrArg (fun M : Matrix ι ι ℂ => M i j) h
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.one_apply,
      Matrix.sum_apply, map_sum, mul_comm] using hij

omit [DecidableEq ο] in
/-- Conjugating both a channel and its input conjugates the output. -/
theorem conjugate_map (T : KrausChannel ι ο κ) (X : Matrix ι ι ℂ) :
    T.conjugate.map (X.map star) = (T.map X).map star := by
  ext i j
  simp [map, conjugate, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply, Matrix.sum_apply, map_sum, mul_comm]

end KrausChannel
end Operations

end Nonadditivity.Channels


