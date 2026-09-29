-- Prove2me | solution 1 for Catalog.Novelty.OrbitalRigidity.numOrbits_mul_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T09:16:59.877588+00:00
-- url     : https://prove2.me/submissions/c4076957-1fda-43c3-b861-511aaabb0e29

import Mathlib
import Definitions.Def_Novelty_OrbitalRigidity
open Classical Catalog.Novelty.OrbitalRigidity MulAction Finset in
theorem solution {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Finite X] (k : ℕ) :
    numOrbits G (Fin k → X) * numOrbits G X ≤ numOrbits G (Fin (k + 1) → X) := by
  haveI : Fintype X := Fintype.ofFinite X
  -- a tuple is fixed iff each coordinate is: `fix_{X^m}(g) = fix(g)^m`
  have hfix : ∀ m : ℕ, ∀ g : G, fixCount (Fin m → X) g = fixCount X g ^ m := by
    intro m g
    unfold fixCount
    rw [← Nat.card_fin m, ← Nat.card_fun, Nat.card_fin]
    refine Nat.card_congr ⟨fun f i => ⟨f.1 i, ?_⟩, fun φ => ⟨fun i => (φ i).1, ?_⟩,
      fun f => rfl, fun φ => rfl⟩
    · have := f.2
      rw [mem_fixedBy] at this ⊢
      exact congrFun this i
    · rw [mem_fixedBy]
      funext i
      exact (φ i).2
  -- Burnside for `X^m` and for `X`
  have hBm : ∀ m : ℕ, ∑ g : G, fixCount X g ^ m = numOrbits G (Fin m → X) * Nat.card G := by
    intro m
    have := sum_card_fixedBy_eq_card_orbits_mul_card_group G (Fin m → X)
    rw [← sum_congr rfl (fun g _ => hfix m g)]
    simp only [fixCount, numOrbits, Nat.card_eq_fintype_card]
    convert this
  have hB1 : ∑ g : G, fixCount X g = numOrbits G X * Nat.card G := by
    have := sum_card_fixedBy_eq_card_orbits_mul_card_group G X
    simp only [fixCount, numOrbits, Nat.card_eq_fintype_card]
    convert this
  -- Chebyshev: `a^k` and `a` are similarly ordered
  have hmono : Monovary (fun g : G => fixCount X g ^ k) (fun g : G => fixCount X g) :=
    fun i j h => Nat.pow_le_pow_left (le_of_lt h) k
  have hcheb := hmono.sum_mul_sum_le_card_mul_sum
  simp only [← pow_succ] at hcheb
  rw [hBm k, hB1, hBm (k + 1), ← Nat.card_eq_fintype_card] at hcheb
  have hG : 0 < Nat.card G * Nat.card G := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hG
  calc numOrbits G (Fin k → X) * numOrbits G X * (Nat.card G * Nat.card G)
      = numOrbits G (Fin k → X) * Nat.card G * (numOrbits G X * Nat.card G) := by ring
    _ ≤ Nat.card G * (numOrbits G (Fin (k + 1) → X) * Nat.card G) := hcheb
    _ = numOrbits G (Fin (k + 1) → X) * (Nat.card G * Nat.card G) := by ring
