-- Prove2me | Definitions.Def_mme_certified_entropy_bridge_data
-- name    : mme_certified_entropy_bridge_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T21:11:44.302037+00:00
-- url     : https://prove2.me/theorems/421dec43-34fd-43e1-b321-6a5b2c99ec2d
-- title:
--   Rational values of cell frequencies, parent mixtures and normalizations
-- statement:
--   Exact rational values of the quantities appearing in a regional rate: the cell frequency of a word, the parent mixture of a pair of words, and the normalization of a family of natural masses.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Mathlib
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_region_count_entropy_data
import Definitions.Def_mme_modern_entropy_data

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v

namespace MME.Cert

/-- The rational cell frequency. -/
def freqQ {C : Type v} {W : Type u} [Fintype W] (mu : C → W → ℕ) (c : C) (w : W) : ℚ :=
  (mu c w : ℚ) / ((∑ v, mu c v : ℕ) : ℚ)

/-- The rational parent mixture. -/
def mixQ {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (r : Fin R) (w : Fin 2 → W) : ℚ :=
  (∑ c, (m r c : ℚ) * freqQ mu ⟨r, c⟩ (w 0) *
    freqQ mu ⟨r, complement (htotal r) c⟩ (w 1)) / (n r : ℚ)

/-- The rational normalization of a family of natural masses. -/
def normQ {W : Type u} [Fintype W] (x : W → ℕ) (w : W) : ℚ := (x w : ℚ) / ((∑ v, x v : ℕ) : ℚ)

end MME.Cert


