-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_parameterized_rectangle_probes
-- name    : Couret.InterIA.Cubic.parameterized_rectangle_probes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:12.100852+00:00
-- url     : https://prove2.me/theorems/59a4947d-3d2e-4b48-b59a-685e54eda964
-- title:
--   Two coordinates separate an injective rectangular family
-- statement:
--   Let $F\subseteq A$, and let $q:A\to\mathbb R^I$ be injective on $F$. Suppose $g:\{0,1\}^2\to F$ is injective and covers $F$, and suppose $H,U,V\in\mathbb R^I$ satisfy $q(g(p_1,p_2))=H+p_1U+p_2V$. Then
--
--   $$\exists Q\subseteq I,\quad |Q|\le2,\quad [a,b\in F\land q(a)|_Q=q(b)|_Q\Longrightarrow a=b].$$
--
--   The selected coordinates are fixed for the entire four-element family.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/FamilyProbes.lean, lines 36–59; source file SHA-256 8c5f51f0ef01603a2bc3c05c7055e3debcf5483f04be2859b58a6f23e53799db; theorem Couret.InterIA.Cubic.parameterized_rectangle_probes

import Definitions.Def_Couret_FamilyProbes_3ad92faa6d56
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Theorems.Thm_Couret_InterIA_Cubic_rectangle_two_coordinates
import Definitions.Def_Couret_RectangleProbes_c3e716b02120
import Mathlib.Data.Set.Card

set_option autoImplicit false
namespace Couret.InterIA.Cubic

theorem parameterized_rectangle_probes {α ι : Type*}
    (q : α → ι → ℝ) (F : Set α) (g : Bool × Bool → α)
    (hg : Function.Injective g) (hmem : ∀ p, g p ∈ F)
    (hcover : ∀ A ∈ F, ∃ p, g p=A) (hinj : Set.InjOn q F)
    (H U V : ι → ℝ) (hrect : ∀ p, q (g p)=rectangle H U V p) :
    ∃ Q : Finset ι, Q.card≤2 ∧ Separates q F Q := by sorry


end Couret.InterIA.Cubic
