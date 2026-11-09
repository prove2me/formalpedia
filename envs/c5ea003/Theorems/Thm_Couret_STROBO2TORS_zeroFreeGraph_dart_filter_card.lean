-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeGraph_dart_filter_card
-- name    : Couret.STROBO2TORS.zeroFreeGraph_dart_filter_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:29:54.656707+00:00
-- url     : https://prove2.me/theorems/d3870de4-8288-47c3-a778-310d735773ac
-- title:
--   Zero-free darts are the zero-avoiding original darts
-- statement:
--   Let G be a finite abelian group with n=|G|, Gamma a simple graph on finite subsets of G with decidable adjacency, and Gamma^0 its restriction retaining an edge S--T exactly when 0 is in neither S nor T. Then $$|\{d\in\operatorname{Dart}(\Gamma):0\notin d_1\cup d_2\}|=|\operatorname{Dart}(\Gamma^0)|.$$ This counts directed darts, not unordered edges.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeIncidence.lean#L170-L195, lines 170–195; source file SHA-256 ec8e64c1d4e0a5241d222480d0c92763461631f7d53eb941a4a6af3dfad66a5e; theorem Couret.STROBO2TORS.zeroFreeGraph_dart_filter_card

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

theorem zeroFreeGraph_dart_filter_card (Γ : SimpleGraph (Finset G))
    [DecidableRel Γ.Adj] :
    ((Finset.univ : Finset Γ.Dart).filter
      (fun d => 0 ∉ d.fst ∪ d.snd)).card =
      Fintype.card (zeroFreeGraph Γ).Dart := by sorry















end Finite

end Couret.STROBO2TORS
