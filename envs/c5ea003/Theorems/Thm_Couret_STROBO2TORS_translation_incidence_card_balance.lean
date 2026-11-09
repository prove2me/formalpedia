-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_translation_incidence_card_balance
-- name    : Couret.STROBO2TORS.translation_incidence_card_balance
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:29.281187+00:00
-- url     : https://prove2.me/theorems/3e9c79ed-2691-42ba-8b97-2ec74811dfd6
-- title:
--   Subtraction-free translation incidence balance
-- statement:
--   Let G be a finite abelian group with n=|G|, X any finite type with decidable equality, C:X→Finset(G), and for each a in G a bijection t_a:X→X. Suppose C(t_a(x))=C(x)+a for every a,x and every carrier C(x) has the same natural cardinality u. Put Z={x in X:0 notin C(x)}. No composition law for the bijections and no free-action premise is required. Then $$n|Z|+u|X|=n|X|.$$ This avoids subtraction and remains valid when X is empty.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeIncidence.lean#L118-L139, lines 118–139; source file SHA-256 ec8e64c1d4e0a5241d222480d0c92763461631f7d53eb941a4a6af3dfad66a5e; theorem Couret.STROBO2TORS.translation_incidence_card_balance

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
import Theorems.Thm_Couret_STROBO2TORS_translation_incidence_card
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



















section Finite

variable [Fintype G]

theorem translation_incidence_card_balance
    {X : Type*} [Fintype X] [DecidableEq X]
    (carrier : X → Finset G) (shift : G → X ≃ X)
    (hshift : ∀ a x, carrier (shift a x) = translateSupport (carrier x) a)
    (u : ℕ) (hcard : ∀ x, (carrier x).card = u) :
    Fintype.card G * ((Finset.univ : Finset X).filter
      (fun x => 0 ∉ carrier x)).card + u * Fintype.card X =
      Fintype.card G * Fintype.card X := by sorry























end Finite

end Couret.STROBO2TORS
