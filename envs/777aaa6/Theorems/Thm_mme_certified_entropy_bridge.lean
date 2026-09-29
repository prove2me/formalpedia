-- Prove2me | Theorems.Thm_mme_certified_entropy_bridge
-- name    : mme_certified_entropy_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T21:12:35.808516+00:00
-- url     : https://prove2.me/theorems/c4e24722-017b-4fe2-9084-605bb14baf5b
-- title:
--   Regional-rate potentials as weighted sums of rational entropies
-- statement:
--   Every potential appearing in a regional rate is a weighted sum of entropies of rational
--   distributions.
--
--   Cell frequencies, parent mixtures and normalized marginal counts are all quotients of natural
--   numbers, so each has an exact rational value; this records those rational values, their
--   nonnegativity, and the fact that the real quantities are their casts. It then rewrites the three
--   potentials accordingly: the compatibility-style potential is the sum over parts of the part mass
--   times the entropy of its rational frequency; the parent potential is the sum over regions of the
--   region size times the entropy of the rational parent mixture; and the coarse potential is the sum
--   over regions of the total marginal count times the entropy of its rational normalization.
--
--   Together with a rational floor for the entropy of a rational distribution, this reduces a lower
--   bound on any of these potentials to exact arithmetic.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_region_count_entropy_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_certified_entropy_bounds
open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v

theorem mme_certified_entropy_bridge :
    (∀ {C : Type v} {W : Type u} [Fintype W] (mu : C → W → ℕ) (c : C) (w : W),
      0 ≤ freqQ mu c w ∧ cellFrequency mu c w = ((freqQ mu c w : ℚ) : ℝ)) ∧
    (∀ {C : Type v} {W : Type u} [Fintype C] [Fintype W] (mu : C → W → ℕ),
      RegionRealization.potential mu =
        ∑ c, ((∑ w, mu c w : ℕ) : ℝ) * entropy (fun w ↦ ((freqQ mu c w : ℚ) : ℝ))) ∧
    (∀ {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
      (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
      (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
      (mu : Cell half R parent → W → ℕ) (r : Fin R) (w : Fin 2 → W),
      0 ≤ mixQ htotal n m mu r w ∧
        parentMixture htotal n m mu r w = ((mixQ htotal n m mu r w : ℚ) : ℝ)) ∧
    (∀ {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
      (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
      (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
      (mu : Cell half R parent → W → ℕ),
      parentPotential htotal n m mu =
        ∑ r, ((n r : ℕ) : ℝ) * entropy (fun w ↦ ((mixQ htotal n m mu r w : ℚ) : ℝ))) ∧
    (∀ {W : Type u} [Fintype W] (x : W → ℕ) (w : W), 0 ≤ normQ x w) ∧
    ∀ {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
      (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3),
      (∀ r, 0 < ∑ j, marginalCounts m i r j) →
      coarsePotential m i =
        ∑ r, ((∑ j, marginalCounts m i r j : ℕ) : ℝ) *
          entropy (fun j ↦ ((normQ (marginalCounts m i r) j : ℚ) : ℝ)) := by sorry
