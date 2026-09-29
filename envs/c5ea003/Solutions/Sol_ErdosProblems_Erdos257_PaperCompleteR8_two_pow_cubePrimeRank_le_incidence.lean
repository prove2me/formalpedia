-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.two_pow_cubePrimeRank_le_incidence
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:02:39.768079+00:00
-- url     : https://prove2.me/submissions/0707614b-2fcb-4ef7-a4c8-c260059e4f4c

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DivisorCubeIncidence
import Mathlib

   
                                                 

                                                                 
                                                                          
                                                                           
                                                                     
  
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset







/-- A prime-subset product uniquely identifies that subset. -/
theorem prime_subset_product_injective (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (q : ℕ) (hq : 0 < q) :
    Set.InjOn (fun S : Finset ℕ => q * S.prod id) (P.powerset : Set (Finset ℕ)) := by
  intro S hS T hT hST
  have hSP : S ⊆ P := mem_powerset.mp hS
  have hTP : T ⊆ P := mem_powerset.mp hT
  have hSprime : ∀ p ∈ S, Nat.Prime p := fun p hp => hP p (hSP hp)
  have hTprime : ∀ p ∈ T, Nat.Prime p := fun p hp => hP p (hTP hp)
  have heq : S.prod id = T.prod id := Nat.eq_of_mul_eq_mul_left hq hST
  calc
    S = (S.prod id).primeFactors := (Nat.primeFactors_prod hSprime).symm
    _ = (T.prod id).primeFactors := congrArg Nat.primeFactors heq
    _ = T := Nat.primeFactors_prod hTprime
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (q : ℕ) (P : Finset ℕ) (n : ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hn : 0 < n) (hqn : q ∣ n) :
    2 ^ cubePrimeRank q P n ≤ ((divisorCube q P).filter (fun a => a ∣ n)).card := by
  classical
  obtain ⟨t, rfl⟩ := hqn
  have ht0 : t ≠ 0 := by
    intro ht
    simp only [ht, mul_zero] at hn
    omega
  let B := P.filter (fun p => q * p ∣ q * t)
  have hBP : B ⊆ P := fun p hp => (mem_filter.mp hp).1
  have hBt : B ⊆ t.primeFactors := by
    intro p hp
    obtain ⟨hpP, u, hu⟩ := mem_filter.mp hp
    have htu : t = p * u := Nat.eq_of_mul_eq_mul_left hq (by
      simpa only [mul_assoc] using hu)
    exact Nat.mem_primeFactors.mpr ⟨hP p hpP, ⟨u, htu⟩, ht0⟩
  have hM0 : P.prod id ≠ 0 := (prod_pos (fun p hp => (hP p hp).pos)).ne'
  have hsub : B.powerset.image (fun S => q * S.prod id) ⊆
      (divisorCube q P).filter (fun a => a ∣ q * t) := by
    intro a ha
    obtain ⟨S, hS, rfl⟩ := mem_image.mp ha
    have hSB : S ⊆ B := mem_powerset.mp hS
    have hSP : S ⊆ P := hSB.trans hBP
    have hSt : S ⊆ t.primeFactors := hSB.trans hBt
    have hdivM : S.prod id ∣ P.prod id :=
      Finset.prod_dvd_prod_of_subset _ _ _ hSP
    have hdivt : S.prod id ∣ t :=
      (Finset.prod_dvd_prod_of_subset _ _ _ hSt).trans (Nat.prod_primeFactors_dvd t)
    refine mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_image.mpr ⟨S.prod id, Nat.mem_divisors.mpr ⟨hdivM, hM0⟩, rfl⟩
    · obtain ⟨v, hv⟩ := hdivt
      refine ⟨v, ?_⟩
      rw [hv]
      ring
  have hcard : (B.powerset.image (fun S => q * S.prod id)).card = 2 ^ B.card := by
    rw [card_image_of_injOn, card_powerset]
    exact prime_subset_product_injective B (fun p hp => hP p (hBP hp)) q hq
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact hle
end
