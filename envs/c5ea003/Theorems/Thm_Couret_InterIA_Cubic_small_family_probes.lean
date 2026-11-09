-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_small_family_probes
-- name    : Couret.InterIA.Cubic.small_family_probes
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:59.448271+00:00
-- url     : https://prove2.me/theorems/062b4e91-be06-439e-9a1b-6b54c41b5ee3
-- title:
--   At most two coordinates separate a family of size one or two
-- statement:
--   Let $q:A\to\mathbb R^I$ be injective on $F\subseteq A$, with $|F|=1$ or $|F|=2$. Then
--
--   $$\exists Q\subseteq I,\quad |Q|\le2,\quad q|_Q\text{ is injective on }F.$$
--
--   An empty set of coordinates suffices for a singleton; one coordinate suffices for two elements.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/FamilyProbes.lean, lines 10–34; source file SHA-256 8c5f51f0ef01603a2bc3c05c7055e3debcf5483f04be2859b58a6f23e53799db; theorem Couret.InterIA.Cubic.small_family_probes

import Definitions.Def_Couret_FamilyProbes_3ad92faa6d56
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Definitions.Def_Couret_RectangleProbes_c3e716b02120
import Mathlib.Data.Set.Card

set_option autoImplicit false
namespace Couret.InterIA.Cubic

theorem small_family_probes {α ι : Type*} (q : α → ι → ℝ) (F : Set α)
    (hinj : Set.InjOn q F) (hcard : F.ncard=1 ∨ F.ncard=2) :
    ∃ Q : Finset ι, Q.card≤2 ∧ Separates q F Q := by sorry




end Couret.InterIA.Cubic
