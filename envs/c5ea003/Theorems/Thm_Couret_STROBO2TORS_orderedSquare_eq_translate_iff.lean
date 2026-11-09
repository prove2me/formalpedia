-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_orderedSquare_eq_translate_iff
-- name    : Couret.STROBO2TORS.orderedSquare_eq_translate_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:17.835308+00:00
-- url     : https://prove2.me/theorems/64b9aa5f-9afa-4a37-8f1a-dbc73b4f561f
-- title:
--   A common translation preserves square equality
-- statement:
--   Let G be an abelian group, S,T finite subsets, and S+a={x+a:x in S}. Let Q_S(z) count ordered pairs in S^2 summing to z, including diagonals. For every a in G, $$Q_{S+a}=Q_{T+a}\iff Q_S=Q_T.$$ This is equality at all labelled group elements, not equality at a single z.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeIncidence.lean#L60-L72, lines 60–72; source file SHA-256 ec8e64c1d4e0a5241d222480d0c92763461631f7d53eb941a4a6af3dfad66a5e; theorem Couret.STROBO2TORS.orderedSquare_eq_translate_iff

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeIncidence_e3b7fd015f51
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsDeltaCount_79a5ff554435
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Translation and incidence transfer from unrestricted collision pairs to pairs
whose two supports avoid zero. The incidence argument does not assume that
translation acts freely. This module adds to the historical certificates.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem orderedSquare_eq_translate_iff (S T : Finset G) (a : G) :
    (∀ z : G, orderedSquare (translateSupport S a) z =
      orderedSquare (translateSupport T a) z) ↔
    (∀ z : G, orderedSquare S z = orderedSquare T z) := by sorry


section Finite

variable [Fintype G]


























end Finite

end Couret.STROBO2TORS
