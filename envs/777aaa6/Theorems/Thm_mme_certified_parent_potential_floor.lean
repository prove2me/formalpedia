-- Prove2me | Theorems.Thm_mme_certified_parent_potential_floor
-- name    : mme_certified_parent_potential_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T05:03:33.320178+00:00
-- url     : https://prove2.me/theorems/41da494b-6ccf-4e83-85e1-b5eb43b34ccf
-- title:
--   Certified rational floor for any parent potential
-- statement:
--   A certified rational floor for any parent potential, from per-region tables of reference exponents.
--
--   For a rational distribution and a choice of reference for each letter, the Gibbs bound together with
--   certified enclosures of the four prime logarithms gives a rational lower bound on the entropy. This
--   records that bound as a single expression, and then lifts it: given a reference table and a rational
--   floor for each region, the region sizes weighted by those floors are a lower bound for the whole
--   parent potential.
--
--   The statement is generic in the half-size, the number of regions, the parent shapes and the alphabet,
--   so one instance serves every level of the recursion.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Theorems.Thm_mme_certified_entropy_rational_floor
import Theorems.Thm_mme_certified_entropy_bridge

open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

theorem mme_certified_parent_potential_floor :
    (∀ {W : Type u} [Fintype W] (p : W → ℚ), (∀ w, 0 ≤ p w) → ∀ e : W → Fin 4 → ℤ,
      ((regFloorG p e : ℚ) : ℝ) ≤ entropy (fun w ↦ ((p w : ℚ) : ℝ))) ∧
    ∀ {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
      (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
      (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
      (mu : Cell half R parent → W → ℕ)
      (e : Fin R → (Fin 2 → W) → Fin 4 → ℤ) (f : Fin R → ℚ),
      (∀ r, f r ≤ regFloorG (mixQ htotal n m mu r) (e r)) →
      (∑ r : Fin R, ((n r : ℕ) : ℝ) * ((f r : ℚ) : ℝ)) ≤ parentPotential htotal n m mu := by sorry
