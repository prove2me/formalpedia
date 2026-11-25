-- Prove2me | Theorems.Thm_coordFunOfDet_apply_eq
-- name    : coordFunOfDet_apply_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:47:41.045459+00:00
-- url     : https://prove2.me/theorems/807b46e8-4f11-5dc5-8644-5f6905efa29f
-- title:
--   coord Fun Of Det apply eq: coord Fun Of Det apply eq
-- statement:
--   The defining value of `coordFunOfDet`, in the `div` form of the definition.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Auerbach.lean#L142-L145
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Auerbach.lean#L142-L145

module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_BasicResults_Auerbach
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Module FiniteDimensional Metric
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem coordFunOfDet_apply_eq {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) (i : Fin n) (v : V) :
    coordFunOfDet b₀ e h_det i v = b₀.det (Function.update e i v) / b₀.det e := by sorry
