-- Prove2me | Theorems.Thm_coordFunOfDet_apply
-- name    : coordFunOfDet_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:25:14.329813+00:00
-- url     : https://prove2.me/theorems/6f91c2d3-fa49-48b1-809d-4074ec9fd671
-- title:
--   coord Fun Of Det apply: coord Fun Of Det apply
-- statement:
--   The coord Fun Of Det apply construction uses the coord Fun Of Det apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Auerbach.lean#L147-L155
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Auerbach.lean#L147-L155

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

theorem coordFunOfDet_apply {n : ℕ} (b₀ : Basis (Fin n) ℝ V)
    (e : Fin n → V) (h_det : b₀.det e ≠ 0) (i j : Fin n) :
    coordFunOfDet b₀ e h_det i (e j) = if i = j then 1 else 0 := by sorry
