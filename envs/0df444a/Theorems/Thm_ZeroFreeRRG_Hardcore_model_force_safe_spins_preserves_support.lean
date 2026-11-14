-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_model_force_safe_spins_preserves_support
-- name    : ZeroFreeRRG.Hardcore.model_force_safe_spins_preserves_support
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:11:21.753+00:00
-- url     : https://prove2.me/theorems/9418da07-6e65-4183-b996-c057f6e33143
-- title:
--   Safe-spin forcing preserves support in both models
-- statement:
--   Each positive-parameter hardcore or Potts model has a safe spin such that forcing any set of vertices to this spin preserves the support of every configuration-model weight, including loops and multiple edges.
-- source:
--   Chunyang Wang et al., Zero-freeness for random regular graphs up to the replica symmetry breaking threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, proof of Lemma 4.20, Step 1 (supporting argument).

import Theorems.Thm_ZeroFreeRRG_Hardcore_model_has_safe_spin
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_interaction_symmetric
import Theorems.Thm_ZeroFreeRRG_Hardcore_force_safe_spins_preserves_support
import Mathlib
set_option autoImplicit false
open AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.model_force_safe_spins_preserves_support (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) :
    ∃ a₀ : m.Spin, ∀ (d n : ℕ) (M : Matching n d)
      (σ : Fin n → m.Spin) (S : Finset (Fin n)),
      weight m t M σ ≠ 0 →
      weight m t M (fun v => if v ∈ S then a₀ else σ v) ≠ 0 := by sorry
