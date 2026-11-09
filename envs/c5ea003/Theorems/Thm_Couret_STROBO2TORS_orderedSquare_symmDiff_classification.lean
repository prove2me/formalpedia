-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_classification
-- name    : Couret.STROBO2TORS.orderedSquare_symmDiff_classification
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:52:44.494207+00:00
-- url     : https://prove2.me/theorems/bae6b6a4-2fd8-48cd-bfbf-9ed4337543c5
-- title:
--   Square collisions classified by symmetric difference
-- statement:
--   Let $G$ be an abelian group. Write $Q_S$ for ordered-sum counts and $S+u=\{x+u:x\in S\}$. Let $S,T$ be distinct three-element supports. Then $$Q_S=Q_T\iff (|S\triangle T|=2\land O(S,T))\lor(|S\triangle T|=4\land E(S,T))\lor(|S\triangle T|=6\land(O(S,T)\lor E(S,T))),$$ where $O,E$ are the defined ordinary and exceptional partner relations. No finiteness of $G$ is needed. The ordinary relation $O(S,T)$ means $T=S+u$ for some $u$ with $2u=0$. The exceptional relation $E(S,T)$ means that for some $a,b,d,u$ with $2d=2u=0$, $d\ne0$, $2a\ne2b$, and $3(b-a)\in\{0,d\}$, one has $S=\{a,b,b+d\}$ and $T=\{a,2b-a,2b-a+d\}+u$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSymmetricDifference.lean, lines 122–142; source file SHA-256 d2245cfcaf7a8e9c103986041000c22c2175007288175c21f6895f18416929fa; theorem Couret.STROBO2TORS.orderedSquare_symmDiff_classification

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_four_iff
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_two_iff
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_cases
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

theorem orderedSquare_symmDiff_classification
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3) (hST : S ≠ T) :
    (∀ z, orderedSquare S z = orderedSquare T z) ↔
      ((S ∆ T).card = 2 ∧ OrdinaryPartner S T) ∨
      ((S ∆ T).card = 4 ∧ ExceptionalPartner S T) ∨
      ((S ∆ T).card = 6 ∧ (OrdinaryPartner S T ∨ ExceptionalPartner S T)) := by sorry





end Couret.STROBO2TORS
