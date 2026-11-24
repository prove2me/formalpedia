-- Prove2me | solution 2 for CayleyCensus.walkCount_add
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:38:51.255478+00:00
-- url     : https://prove2.me/submissions/4a9e0191-4909-4c72-95fa-a1592c7946d3

import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments

open CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

namespace CayleyCensus

theorem solution (S : Finset G) (m n : ℕ) (g : G) :
    walkCount S (m + n) g = ∑ h : G, walkCount S m h * walkCount S n (h⁻¹ * g) := by
  induction m generalizing g with
  | zero =>
      simp only [Nat.zero_add, walkCount_zero, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ (1 : G)]
      simp
  | succ m ih =>
      have hsucc : m + 1 + n = (m + n) + 1 := by omega
      rw [hsucc, walkCount_succ]
      have hstep : ∀ s : G, walkCount S (m + n) (s⁻¹ * g)
          = ∑ h : G, walkCount S m h * walkCount S n (h⁻¹ * (s⁻¹ * g)) :=
        fun s => ih _
      rw [Finset.sum_congr rfl (fun s _ => hstep s)]
      have hRHS : ∑ h : G, walkCount S (m + 1) h * walkCount S n (h⁻¹ * g)
          = ∑ s ∈ S, ∑ h : G, walkCount S m (s⁻¹ * h) * walkCount S n (h⁻¹ * g) := by
        simp only [walkCount_succ, Finset.sum_mul]
        rw [Finset.sum_comm]
      rw [hRHS]
      refine Finset.sum_congr rfl fun s _ => ?_
      refine (Fintype.sum_equiv (Equiv.mulLeft s⁻¹) _ _ fun h => ?_).symm
      have h2 : (s⁻¹ * h)⁻¹ * (s⁻¹ * g) = h⁻¹ * g := by group
      simp only [Equiv.coe_mulLeft]
      rw [h2]

end CayleyCensus

open CayleyCensus

theorem solution (S : Finset G) (m n : ℕ) (g : G) :
    walkCount S (m + n) g = ∑ h : G, walkCount S m h * walkCount S n (h⁻¹ * g) :=
  CayleyCensus.solution S m n g

#print axioms solution
