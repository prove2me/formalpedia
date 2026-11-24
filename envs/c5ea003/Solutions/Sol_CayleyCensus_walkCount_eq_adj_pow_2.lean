-- Prove2me | solution 2 for CayleyCensus.walkCount_eq_adj_pow
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:38:50.273927+00:00
-- url     : https://prove2.me/submissions/c2f26aa9-5476-4bb9-9abd-f33f49c2096a

import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments

open CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

namespace CayleyCensus

omit [Group G] in
private theorem sum_indicator_mul_aux (S : Finset G) (f : G → ℕ) :
    ∑ s : G, (if s ∈ S then 1 else 0) * f s = ∑ s ∈ S, f s := by
  simp [ite_mul, Finset.sum_ite_mem]

theorem solution (S : Finset G) (n : ℕ) (x y : G) :
    (adj S ^ n) x y = walkCount S n (x⁻¹ * y) := by
  induction n generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, walkCount_zero, inv_mul_eq_one]
  | succ n ih =>
      rw [pow_succ']
      rw [Matrix.mul_apply]
      have hstep : ∀ z : G, adj S x z * (adj S ^ n) z y
          = (if x⁻¹ * z ∈ S then 1 else 0) * walkCount S n (z⁻¹ * y) := by
        intro z; rw [ih]; rfl
      rw [Finset.sum_congr rfl (fun z _ => hstep z)]
      have hre : ∑ z : G, (if x⁻¹ * z ∈ S then 1 else 0) * walkCount S n (z⁻¹ * y)
          = ∑ s : G, (if s ∈ S then 1 else 0) * walkCount S n (s⁻¹ * (x⁻¹ * y)) := by
        refine (Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun s => ?_).symm
        have h1 : x⁻¹ * (x * s) = s := by group
        have h2 : (x * s)⁻¹ * y = s⁻¹ * (x⁻¹ * y) := by group
        simp only [Equiv.coe_mulLeft, h1, h2]
      rw [hre, walkCount_succ]
      exact sum_indicator_mul_aux S (fun s => walkCount S n (s⁻¹ * (x⁻¹ * y)))

end CayleyCensus

open CayleyCensus

theorem solution (S : Finset G) (n : ℕ) (x y : G) :
    (adj S ^ n) x y = walkCount S n (x⁻¹ * y) :=
  CayleyCensus.solution S n x y

#print axioms solution
