-- Prove2me | Theorems.Thm_mme_certified_potential_ceiling
-- name    : mme_certified_potential_ceiling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T05:09:04.704001+00:00
-- url     : https://prove2.me/theorems/9516d3c4-582a-46ae-b89d-9fb24ef17c1d
-- title:
--   Certified rational ceiling for a compatibility-style potential
-- statement:
--   A certified rational ceiling for a compatibility-style potential.
--
--   The Gibbs bound has an upper half as well as a lower one: against a reference, an entropy is at most
--   the total reference mass minus the total weight, minus the reference log-moment. With certified
--   enclosures of the four prime logarithms, and taking each logarithm coefficient at the endpoint its
--   sign calls for, that becomes a rational expression.
--
--   Summing over the parts of a partition bounds the whole potential above. This is what a subtracted
--   potential needs, as against the floor used for the potentials that are added.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_generic_ceiling_data
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_region_count_entropy_data
import Theorems.Thm_mme_certified_entropy_rational_floor
import Theorems.Thm_mme_certified_entropy_bridge

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v

theorem mme_certified_potential_ceiling :
    (∀ {W : Type u} [Fintype W] (p : W → ℚ), (∀ w, 0 ≤ p w) → ∀ e : W → Fin 4 → ℤ,
      entropy (fun w ↦ ((p w : ℚ) : ℝ)) ≤ ((regCeilG p e : ℚ) : ℝ)) ∧
    ∀ {C : Type v} {W : Type u} [Fintype C] [Fintype W] (mu : C → W → ℕ)
      (e : C → W → Fin 4 → ℤ) (g : C → ℚ),
      (∀ c, regCeilG (freqQ mu c) (e c) ≤ g c) →
      RegionRealization.potential mu ≤ ∑ c, ((∑ w, mu c w : ℕ) : ℝ) * ((g c : ℚ) : ℝ) := by sorry
