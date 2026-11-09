-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeGraph_balance_edges
-- name    : Couret.STROBO2TORS.zeroFreeGraph_balance_edges
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:58:06.880206+00:00
-- url     : https://prove2.me/theorems/70a673a7-dc99-4f8d-974f-d43522171ef2
-- title:
--   Universal edge-incidence balance
-- statement:
--   Let G be a finite abelian group with n=|G|, Gamma a simple graph on finite subsets of G with decidable adjacency, and Gamma^0 its restriction retaining an edge S--T exactly when 0 is in neither S nor T. Assume common translation by every a preserves Gamma adjacency in both directions, and |S union T|=u for every edge, where u is a fixed natural. $$n|E(\Gamma^0)|+u|E(\Gamma)|=n|E(\Gamma)|.$$ Empty edge families are allowed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeIncidence.lean#L220-L242, lines 220–242; source file SHA-256 ec8e64c1d4e0a5241d222480d0c92763461631f7d53eb941a4a6af3dfad66a5e; theorem Couret.STROBO2TORS.zeroFreeGraph_balance_edges

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
import Theorems.Thm_Couret_STROBO2TORS_translation_incidence_card_balance
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeGraph_dart_filter_card
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

theorem zeroFreeGraph_balance_edges (Γ : SimpleGraph (Finset G))
    [DecidableRel Γ.Adj] (u : ℕ)
    (htrans : ∀ S T a, Γ.Adj (translateSupport S a) (translateSupport T a) ↔
      Γ.Adj S T)
    (hunion : ∀ S T, Γ.Adj S T → (S ∪ T).card = u) :
    Fintype.card G * (zeroFreeGraph Γ).edgeFinset.card + u * Γ.edgeFinset.card =
      Fintype.card G * Γ.edgeFinset.card := by sorry











end Finite

end Couret.STROBO2TORS
