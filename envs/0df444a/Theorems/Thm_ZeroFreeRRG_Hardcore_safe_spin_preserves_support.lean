-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_safe_spin_preserves_support
-- name    : ZeroFreeRRG.Hardcore.safe_spin_preserves_support
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:04:16.264147+00:00
-- url     : https://prove2.me/theorems/711f6853-89ce-4875-aa61-e15c9c0efc51
-- title:
--   A safe-spin update preserves a supported multigraph configuration
-- statement:
--   If all vertex weights are nonzero and a spin interacts nontrivially in both orientations with every spin, replacing a single vertex by that spin preserves nonzero configuration weight. The proof counts every matched edge occurrence, including loops and parallel edges.
-- source:
--   Auxiliary support fact for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Appendix E.3, Step 1, p. 77.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.safe_spin_preserves_support (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ : Fin n → m.Spin) (v : Fin n) (a₀ : m.Spin)
    (hπ : ∀ a, m.pi t a ≠ 0)
    (hsafeL : ∀ a, m.M t a₀ a ≠ 0) (hsafeR : ∀ a, m.M t a a₀ ≠ 0)
    (hw : weight m t M σ ≠ 0) :
    weight m t M (Function.update σ v a₀) ≠ 0 := by sorry
