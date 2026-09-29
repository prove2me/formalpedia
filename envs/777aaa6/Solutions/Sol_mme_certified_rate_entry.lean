-- Prove2me | solution 1 for mme_certified_rate_entry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:20:38.367013+00:00
-- url     : https://prove2.me/submissions/14601b56-c8ef-4c88-952b-ae7dd9ab53a0

import Mathlib
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_recursive_region_parent_profiles

open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u


namespace MME.Cert

variable {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}

/-- The marginal counts of a region total its split weights. -/
theorem marg_total_G (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3)
    (r : Fin R) : ∑ j, marginalCounts m i r j = ∑ c, m r c := by
  classical
  exact Fintype.sum_fiberwise
    (fun a : RecursiveThinSplit.Split half (parent r) ↦ a.val i) (fun c ↦ m r c)

/-- A regional rate is above a value as soon as all three of its potentials are. -/
theorem regionalRate_lower {W : Type u} [Fintype W]
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → W → ℕ) (T : ℝ)
    (hX : T < coarsePotential m 0 - penaltyPotential n m)
    (hY : T < parentPotential htotal n m (mu 1) - compatibilityPotential 0 (mu 1))
    (hZ : T < parentPotential htotal n m (mu 2) - compatibilityPotential 1 (mu 2)) :
    T < regionalRate htotal n m mu :=
  lt_min hX (lt_min hY hZ)


end MME.Cert

theorem solution :
    (∀ {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
      (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) (r : Fin R),
      ∑ j, marginalCounts m i r j = ∑ c, m r c) ∧
    ∀ {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {W : Type u} [Fintype W]
      (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
      (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
      (mu : Fin 3 → Cell half R parent → W → ℕ) (T : ℝ),
      T < coarsePotential m 0 - penaltyPotential n m →
      T < parentPotential htotal n m (mu 1) - compatibilityPotential 0 (mu 1) →
      T < parentPotential htotal n m (mu 2) - compatibilityPotential 1 (mu 2) →
      T < regionalRate htotal n m mu :=
  ⟨fun {half} {R} {parent} m i r ↦ MME.Cert.marg_total_G m i r,
   fun {half} {R} {parent} {W} _ htotal n m mu T hX hY hZ ↦
     MME.Cert.regionalRate_lower htotal n m mu T hX hY hZ⟩
