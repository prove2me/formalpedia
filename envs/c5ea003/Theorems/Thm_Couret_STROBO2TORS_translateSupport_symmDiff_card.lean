-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_translateSupport_symmDiff_card
-- name    : Couret.STROBO2TORS.translateSupport_symmDiff_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:17.271613+00:00
-- url     : https://prove2.me/theorems/e500d042-9d02-4641-83a9-d158c0f2400b
-- title:
--   Translation preserves symmetric-difference size
-- statement:
--   Let G be an abelian group, S,T finite subsets, and S+a={x+a:x in S}. Let Q_S(z) count ordered pairs in S^2 summing to z, including diagonals. For every a in G, $$|(S+a)\triangle(T+a)|=|S\triangle T|.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeIncidence.lean#L37-L39, lines 37–39; source file SHA-256 ec8e64c1d4e0a5241d222480d0c92763461631f7d53eb941a4a6af3dfad66a5e; theorem Couret.STROBO2TORS.translateSupport_symmDiff_card

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

theorem translateSupport_symmDiff_card (S T : Finset G) (a : G) :
    (translateSupport S a ∆ translateSupport T a).card = (S ∆ T).card := by sorry








section Finite

variable [Fintype G]


























end Finite

end Couret.STROBO2TORS
