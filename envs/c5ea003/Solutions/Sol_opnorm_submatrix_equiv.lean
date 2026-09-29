-- Prove2me | solution 1 for opnorm_submatrix_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T17:06:38.751088+00:00
-- url     : https://prove2.me/submissions/1f4a8efe-09a9-46b8-b948-834b8aa2bc15

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.NormedSpace

open scoped Matrix.Norms.L2Operator
open Matrix

set_option maxHeartbeats 1000000

/-- Source: the elementary unitary equivalence of Euclidean matrix operators
under simultaneous row and column reindexing. This is the index bridge needed
to instantiate the general Hermitian Rademacher engine on the vectorized
`Fin n₁ × Fin n₂` tangent-coordinate space. -/
theorem solution {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A : Matrix β β ℝ) :
    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A.submatrix e e)))‖
      = ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))‖ := by
  have hconj_vec : ∀ (x : EuclideanSpace ℝ α),
      toEuclideanLin (A.submatrix e e) x =
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).symm
          (toEuclideanLin A ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)) := by
    intro x
    apply (EuclideanSpace.equiv α ℝ).injective
    ext i
    show ((A.submatrix e e) *ᵥ x.ofLp) i = _
    rw [Matrix.submatrix_mulVec_equiv]
    rw [LinearIsometryEquiv.piLpCongrLeft_symm]
    show _ = ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm)
          ((toEuclideanLin A) ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x))).ofLp i
    rw [LinearIsometryEquiv.piLpCongrLeft_apply]
    show _ = (Equiv.piCongrLeft' (fun _ => ℝ) e.symm
        ((toEuclideanLin A) ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x)).ofLp) i
    rw [Equiv.piCongrLeft'_apply]
    show (A *ᵥ (x.ofLp ∘ e.symm)) (e i)
        = (A *ᵥ ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) x).ofLp) (e i)
    rw [LinearIsometryEquiv.piLpCongrLeft_apply]
    rfl
  have hpost : ∀ (f : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ β)
      (g : EuclideanSpace ℝ β ≃ₗᵢ[ℝ] EuclideanSpace ℝ α),
      ‖g.toLinearIsometry.toContinuousLinearMap.comp f‖ = ‖f‖ := by
    intro f g
    refine le_antisymm ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (fun x => ?_)
      simp only [ContinuousLinearMap.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap, g.toLinearIsometry.norm_map]
      exact f.le_opNorm x
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
      have hx : ‖f x‖ = ‖g.toLinearIsometry.toContinuousLinearMap.comp f x‖ := by
        simp only [ContinuousLinearMap.comp_apply,
          LinearIsometry.coe_toContinuousLinearMap, g.toLinearIsometry.norm_map]
      rw [hx]
      exact (g.toLinearIsometry.toContinuousLinearMap.comp f).le_opNorm x
  set g := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e with hg
  have hconj :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A.submatrix e e))
        = (g.symm.toLinearIsometry.toContinuousLinearMap).comp
            ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).comp
              g.toLinearIsometry.toContinuousLinearMap) := by
    refine ContinuousLinearMap.ext (fun x => ?_)
    simp only [LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap]
    exact hconj_vec x
  rw [hconj]
  have hstep := hpost ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).comp
      g.toLinearIsometry.toContinuousLinearMap) g.symm
  rw [hstep]
  rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

