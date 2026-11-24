-- Prove2me | solution 2 for CayleyCensus.adj_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:47:47.114022+00:00
-- url     : https://prove2.me/submissions/dc092cbb-102e-4901-bb21-bdf86e2e5828

import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments

open CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

namespace CayleyCensus

omit [Fintype G] in
theorem solution {S : Finset G} (hS : InvClosed S) : (adj S).IsSymm := by
  ext x y
  show adj S y x = adj S x y
  unfold adj
  by_cases h : x⁻¹ * y ∈ S
  · have : y⁻¹ * x ∈ S := by
      have hrw : y⁻¹ * x = (x⁻¹ * y)⁻¹ := by group
      rw [hrw]; exact hS h
    simp [h, this]
  · have : y⁻¹ * x ∉ S := by
      intro hc
      apply h
      have hrw : x⁻¹ * y = (y⁻¹ * x)⁻¹ := by group
      rw [hrw]; exact hS hc
    simp [h, this]

end CayleyCensus

open CayleyCensus

omit [Fintype G] in
theorem solution {S : Finset G} (hS : InvClosed S) : (adj S).IsSymm :=
  CayleyCensus.solution hS

#print axioms solution
