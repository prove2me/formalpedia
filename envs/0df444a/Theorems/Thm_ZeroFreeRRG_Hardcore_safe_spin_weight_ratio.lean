-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_safe_spin_weight_ratio
-- name    : ZeroFreeRRG.Hardcore.safe_spin_weight_ratio
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:18:10.097162+00:00
-- url     : https://prove2.me/theorems/94dcdf9f-922b-43ab-af70-21e5c9cb2d24
-- title:
--   Uniform one-vertex safe-spin weight bound
-- statement:
--   For each positive-parameter hardcore or Potts model and fixed degree d, there is a safe spin a and a positive constant K such that, for every finite configuration-model multigraph, configuration, and vertex, the original configuration weight is at most K times the weight after setting that vertex to a. Loops and parallel edges are included.
-- source:
--   Chunyang Wang et al., Zero-freeness for random regular graphs up to the replica symmetry breaking threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, proof of Lemma 4.20, Step 1 (supporting argument).

import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_edge_nonnegative
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_has_safe_spin
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_interaction_symmetric
import Theorems.Thm_ZeroFreeRRG_Hardcore_finite_factor_ratio_bound
import Theorems.Thm_ZeroFreeRRG_Hardcore_changed_factors_product_bound
import Theorems.Thm_ZeroFreeRRG_Hardcore_incident_edge_reps_card_le_degree
import Mathlib
set_option autoImplicit false
open AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.safe_spin_weight_ratio (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) (d : ℕ) :
    ∃ (a₀ : m.Spin) (K : ℝ), 0 < K ∧
      ∀ (n : ℕ) (M : Matching n d) (σ : Fin n → m.Spin) (v : Fin n),
        weight m t M σ ≤ K * weight m t M (Function.update σ v a₀) := by sorry
