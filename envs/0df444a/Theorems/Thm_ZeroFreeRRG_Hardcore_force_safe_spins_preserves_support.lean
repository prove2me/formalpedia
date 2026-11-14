-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_force_safe_spins_preserves_support
-- name    : ZeroFreeRRG.Hardcore.force_safe_spins_preserves_support
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:04:14.010295+00:00
-- url     : https://prove2.me/theorems/ce4923dd-c28e-4162-8260-8b71f0f9ca04
-- title:
--   Forcing safe spins on any vertex set preserves support
-- statement:
--   Under nonzero vertex weights and nonzero interactions of a safe spin in both orientations, forcing the safe spin at every vertex of any finite set preserves nonzero configuration weight on the configuration multigraph.
-- source:
--   Auxiliary support fact for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, Step 1, p. 77.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.force_safe_spins_preserves_support (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ : Fin n → m.Spin) (S : Finset (Fin n)) (a₀ : m.Spin)
    (hπ : ∀ a, m.pi t a ≠ 0)
    (hsafeL : ∀ a, m.M t a₀ a ≠ 0) (hsafeR : ∀ a, m.M t a a₀ ≠ 0)
    (hw : weight m t M σ ≠ 0) :
    weight m t M (fun v => if v ∈ S then a₀ else σ v) ≠ 0 := by sorry
