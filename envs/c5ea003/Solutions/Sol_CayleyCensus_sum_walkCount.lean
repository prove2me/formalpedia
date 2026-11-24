-- Prove2me | solution 1 for CayleyCensus.sum_walkCount
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:38:51.760027+00:00
-- url     : https://prove2.me/submissions/cc9fa58c-47ca-46ce-9d5c-2abe07a7507b

import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments

open CayleyCensus
variable {G : Type*} [Group G]
open CensusEquiv
variable {S : Finset G}
variable [DecidableEq G]
variable [Fintype G]

namespace CayleyCensus

theorem solution (S : Finset G) (n : ℕ) :
    ∑ g : G, walkCount S n g = S.card ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hswap : ∑ g : G, walkCount S (n + 1) g
          = ∑ s ∈ S, ∑ g : G, walkCount S n (s⁻¹ * g) := by
        simp only [walkCount_succ]
        rw [Finset.sum_comm]
      rw [hswap]
      have hre : ∀ s : G, ∑ g : G, walkCount S n (s⁻¹ * g) = ∑ g : G, walkCount S n g :=
        fun s => Fintype.sum_equiv (Equiv.mulLeft s⁻¹) _ _ fun _ => rfl
      simp only [hre, ih]
      rw [Finset.sum_const, smul_eq_mul]
      ring

end CayleyCensus

open CayleyCensus

theorem solution (S : Finset G) (n : ℕ) :
    ∑ g : G, walkCount S n g = S.card ^ n :=
  CayleyCensus.solution S n

#print axioms solution
