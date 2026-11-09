-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_graph_eq_bot_of_union_card_gt
-- name    : Couret.STROBO2TORS.graph_eq_bot_of_union_card_gt
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:52:06.968747+00:00
-- url     : https://prove2.me/theorems/ed383501-52d0-4509-8a97-124afebcbad1
-- title:
--   A prescribed union larger than the ambient type forbids edges
-- statement:
--   Let G be a finite type with decidable equality, Gamma any simple graph on its finite subsets, and u natural. If every edge S--T has |S union T|=u and |G|<u, then $$\Gamma=\bot.$$ No group structure, translation invariance or decidable-adjacency premise is required for this theorem.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeIncidence.lean#L244-L256, lines 244–256; source file SHA-256 ec8e64c1d4e0a5241d222480d0c92763461631f7d53eb941a4a6af3dfad66a5e; theorem Couret.STROBO2TORS.graph_eq_bot_of_union_card_gt

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



















section Finite

variable [Fintype G]

omit [AddCommGroup G] in

theorem graph_eq_bot_of_union_card_gt (Γ : SimpleGraph (Finset G)) (u : ℕ)
    (hunion : ∀ S T, Γ.Adj S T → (S ∪ T).card = u)
    (hn : Fintype.card G < u) : Γ = ⊥ := by sorry









end Finite

end Couret.STROBO2TORS
