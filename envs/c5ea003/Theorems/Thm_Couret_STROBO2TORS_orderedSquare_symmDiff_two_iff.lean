-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_two_iff
-- name    : Couret.STROBO2TORS.orderedSquare_symmDiff_two_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:33.629147+00:00
-- url     : https://prove2.me/theorems/4df6d76a-2f25-467a-b5bd-39a921bbe0b3
-- title:
--   Distance-two collisions are ordinary partners
-- statement:
--   Let $G$ be an abelian group. Write $Q_S$ for ordered-sum counts and $S+u=\{x+u:x\in S\}$. For three-element supports $S,T$, $$Q_S=Q_T\text{ and }|S\triangle T|=2\iff O(S,T)\text{ and }|S\cap T|=2.$$ Equality of supports is automatically excluded by either side. The ordinary relation $O(S,T)$ means $T=S+u$ for some $u$ with $2u=0$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSymmetricDifference.lean, lines 74–87; source file SHA-256 d2245cfcaf7a8e9c103986041000c22c2175007288175c21f6895f18416929fa; theorem Couret.STROBO2TORS.orderedSquare_symmDiff_two_iff

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalPartner_inter_card_ne_two
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_two_iff_inter_two
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

theorem orderedSquare_symmDiff_two_iff
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3) :
    ((∀ z, orderedSquare S z = orderedSquare T z) ∧ (S ∆ T).card = 2) ↔
      OrdinaryPartner S T ∧ (S ∩ T).card = 2 := by sorry











end Couret.STROBO2TORS
