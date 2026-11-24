-- Prove2me | solution 2 for CayleyCensus.adjPow_graphAut
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:38:53.813733+00:00
-- url     : https://prove2.me/submissions/30ea8950-16e4-4e7a-a896-22a26d4cf14b

import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments
import Definitions.Def_MachineLearning_CayleyCensusGraphSymmetry

open CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

namespace CayleyCensus

theorem solution {S : Finset G} (φ : G ≃ G)
    (hstep : ∀ x y : G, ((φ x)⁻¹ * φ y ∈ S ↔ x⁻¹ * y ∈ S)) (n : ℕ) (x y : G) :
    (adj S ^ n) (φ x) (φ y) = (adj S ^ n) x y := by
  have hadj : ∀ x y : G, adj S (φ x) (φ y) = adj S x y := by
    intro x y
    show (if (φ x)⁻¹ * φ y ∈ S then 1 else 0) = if x⁻¹ * y ∈ S then 1 else 0
    exact if_congr (hstep x y) rfl rfl
  induction n generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, φ.injective.eq_iff]
  | succ n ih =>
      rw [pow_succ']
      simp only [Matrix.mul_apply]
      rw [← Equiv.sum_comp φ (fun z => adj S (φ x) z * (adj S ^ n) z (φ y))]
      exact Finset.sum_congr rfl fun z _ => by rw [hadj, ih]

end CayleyCensus

open CayleyCensus

theorem solution {S : Finset G} (φ : G ≃ G)
    (hstep : ∀ x y : G, ((φ x)⁻¹ * φ y ∈ S ↔ x⁻¹ * y ∈ S)) (n : ℕ) (x y : G) :
    (adj S ^ n) (φ x) (φ y) = (adj S ^ n) x y :=
  CayleyCensus.solution φ hstep n x y

#print axioms solution
