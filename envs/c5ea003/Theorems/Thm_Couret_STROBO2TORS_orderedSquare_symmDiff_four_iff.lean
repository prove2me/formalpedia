-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_four_iff
-- name    : Couret.STROBO2TORS.orderedSquare_symmDiff_four_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:28.988116+00:00
-- url     : https://prove2.me/theorems/924e4c09-c578-4acf-aee5-d753e8991f7e
-- title:
--   Delta-four collisions are exactly singleton-overlap exceptional pairs
-- statement:
--   Let $G$ be an abelian group. Let $S,T\subseteq G$ each have three elements. Call them exceptional partners if $S=\{a,b,b+d\}$ and $T=\{a,2b-a,2b-a+d\}+u$ for some $d\ne0$ with $2d=2u=0$, $2a\ne2b$ and $3(b-a)\in\{0,d\}$. Then
--
--   $$\bigl(Q_S=Q_T\text{ and }|S\triangle T|=4\bigr)\Longleftrightarrow\bigl(S,T\text{ exceptional partners and }|S\cap T|=1\bigr),$$
--
--   where $Q$ counts ordered pair sums. This isolates the nontranslation delta-four case.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSymmetricDifference.lean, lines 89–107; source file SHA-256 d2245cfcaf7a8e9c103986041000c22c2175007288175c21f6895f18416929fa; theorem Couret.STROBO2TORS.orderedSquare_symmDiff_four_iff

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryPartner_inter_card_eq_zero_or_two
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













end FiniteSets

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem orderedSquare_symmDiff_four_iff
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3) :
    ((∀ z, orderedSquare S z = orderedSquare T z) ∧ (S ∆ T).card = 4) ↔
      ExceptionalPartner S T ∧ (S ∩ T).card = 1 := by sorry









end Couret.STROBO2TORS
