-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_four_not_translation
-- name    : Couret.STROBO2TORS.orderedSquare_symmDiff_four_not_translation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:52:41.611308+00:00
-- url     : https://prove2.me/theorems/d4e30119-2ee3-4d47-b6a0-ee4263a27724
-- title:
--   A four-point symmetric difference forces a nontranslation collision
-- statement:
--   Let $G$ be any abelian group and $S,T$ be three-element supports with equal ordered-square profiles and $|S\triangle T|=4$. Then
--
--   $$\nexists u\in G,\quad T=S+u.$$
--
--   No zero-free or finiteness assumption is needed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSymmetricDifference.lean, lines 144–151; source file SHA-256 d2245cfcaf7a8e9c103986041000c22c2175007288175c21f6895f18416929fa; theorem Couret.STROBO2TORS.orderedSquare_symmDiff_four_not_translation

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_four_iff
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.SymmDiff

set_option autoImplicit false

/-!
Refinement of the ordered-square classification by symmetric-difference
cardinality. The supports have cardinality three; zero is permitted.
The ambient abelian group need not be finite.
This module classifies the delta=2,4,6 cases; it does not count their pairs.
-/

open scoped symmDiff

namespace Couret.STROBO2TORS

section FiniteSets

variable {α : Type*} [DecidableEq α]













end FiniteSets

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem orderedSquare_symmDiff_four_not_translation
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3)
    (hsq : ∀ z, orderedSquare S z = orderedSquare T z)
    (hdelta : (S ∆ T).card = 4) :
    ¬ ∃ v, T = translateSupport S v := by sorry



end Couret.STROBO2TORS
