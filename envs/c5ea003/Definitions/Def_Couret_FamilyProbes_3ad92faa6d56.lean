-- Prove2me | Definitions.Def_Couret_FamilyProbes_3ad92faa6d56
-- name    : Couret_FamilyProbes_3ad92faa6d56
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:43.614197+00:00
-- url     : https://prove2.me/theorems/ec01c6ae-86b9-486a-944b-d618e4b7182d
-- title:
--   Finite probe banks that separate a family
-- statement:
--   For a real-valued reading function $q(\alpha,i)$, a family $F$ of objects and a finite probe set $Q$, separation means $$a,b\in F,\quad q(a,i)=q(b,i)\ (i\in Q)\Longrightarrow a=b.$$ This abstracts fixed probe selection independently of the concrete support or convolution model.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/FamilyProbes.lean; source file SHA-256 8c5f51f0ef01603a2bc3c05c7055e3debcf5483f04be2859b58a6f23e53799db

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Definitions.Def_Couret_RectangleProbes_c3e716b02120
import Mathlib.Data.Set.Card

set_option autoImplicit false
namespace Couret.InterIA.Cubic

def Separates {α ι : Type*} (q : α → ι → ℝ) (F : Set α) (Q : Finset ι) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (∀ z ∈ Q, q A z=q B z) → A=B





end Couret.InterIA.Cubic


