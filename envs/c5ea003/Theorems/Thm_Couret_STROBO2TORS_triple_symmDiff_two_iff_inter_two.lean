-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_two_iff_inter_two
-- name    : Couret.STROBO2TORS.triple_symmDiff_two_iff_inter_two
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:53:11.346634+00:00
-- url     : https://prove2.me/theorems/4bd6facf-5d9d-4937-8cbb-a440128a7729
-- title:
--   Distance two means two common points for triples
-- statement:
--   For three-element finite subsets $S,T$ of any type with decidable equality, $$|S\triangle T|=2\iff|S\cap T|=2.$$ No group structure or finiteness of the ambient type is needed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSymmetricDifference.lean, lines 38–42; source file SHA-256 d2245cfcaf7a8e9c103986041000c22c2175007288175c21f6895f18416929fa; theorem Couret.STROBO2TORS.triple_symmDiff_two_iff_inter_two

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_balance
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

theorem triple_symmDiff_two_iff_inter_two
    (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    (S ∆ T).card = 2 ↔ (S ∩ T).card = 2 := by sorry










end FiniteSets

variable {G : Type*} [AddCommGroup G] [DecidableEq G]












end Couret.STROBO2TORS
