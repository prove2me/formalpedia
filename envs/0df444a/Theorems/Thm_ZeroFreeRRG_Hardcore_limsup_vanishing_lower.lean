-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_limsup_vanishing_lower
-- name    : ZeroFreeRRG.Hardcore.limsup_vanishing_lower
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:58:48.218195+00:00
-- url     : https://prove2.me/theorems/48ae60f4-03e5-44fa-a88e-5e0b1a577c54
-- title:
--   Limsup comparison under a vanishing lower perturbation
-- statement:
--   If $g$ tends to zero along a nontrivial filter and $A+g\le B$ eventually, then the extended-real limsup of $A$ is at most that of $B$.
-- source:
--   Auxiliary step for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 31, Lemma 4.20, equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
set_option autoImplicit false
open Set Filter Topology MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.limsup_vanishing_lower {α : Type} (F : Filter α) [F.NeBot] (A B g : α → ℝ)
    (hg : Tendsto g F (𝓝 0)) (hbound : ∀ᶠ x in F, A x + g x ≤ B x) :
    limsup (fun x => (A x : EReal)) F ≤ limsup (fun x => (B x : EReal)) F := by sorry
