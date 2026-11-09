-- Prove2me | Definitions.Def_Couret_Strobo2TorsZeroFreeIncidence_e3b7fd015f51
-- name    : Couret_Strobo2TorsZeroFreeIncidence_e3b7fd015f51
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:55.30154+00:00
-- url     : https://prove2.me/theorems/eefaddca-7f0a-4108-bb2b-7ab4a91662f9
-- title:
--   Zero-free graph restriction and translation of darts
-- statement:
--   Given a simple graph on finite subsets of an additive commutative group, zeroFreeGraph keeps the same vertex type and requires both endpoints to avoid zero in addition to the original adjacency. Vertices containing zero therefore become isolated. For a supplied adjacency invariance under simultaneous translation, dartTranslateEquiv maps each oriented edge by translating both endpoints by a and uses translation by −a as inverse. This construction does not assume translation acts freely. The bundle also records translation by zero and inverse-translation cancellation; finiteness is not imposed as a mathematical precondition of these local support operations.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c61de6daf8df99da6574d627b45941403594956/research/strobo-2tors-2026-10-12/lean/Strobo2TorsZeroFreeIncidence.lean; source file SHA-256 ec8e64c1d4e0a5241d222480d0c92763461631f7d53eb941a4a6af3dfad66a5e

import Aesop
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

@[simp] theorem translateSupport_zero (S : Finset G) : translateSupport S 0 = S := by
  simp [translateSupport]

@[simp] theorem translateSupport_neg_cancel (S : Finset G) (a : G) :
    translateSupport (translateSupport S a) (-a) = S := by
  rw [translateSupport_add, add_neg_cancel, translateSupport_zero]















section Finite

variable [Fintype G]





/-- Induced restriction to zero-free vertices, keeping the ambient vertex type. -/
def zeroFreeGraph (Γ : SimpleGraph (Finset G)) : SimpleGraph (Finset G) where
  Adj S T := Γ.Adj S T ∧ 0 ∉ S ∧ 0 ∉ T
  symm := by
    intro S T h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    constructor
    intro S h
    exact Γ.irrefl h.1

noncomputable instance zeroFreeGraph_decidableRel (Γ : SimpleGraph (Finset G)) :
    DecidableRel (zeroFreeGraph Γ).Adj := Classical.decRel _

/-- Simultaneous translation gives an equivalence of oriented edges. -/
def dartTranslateEquiv (Γ : SimpleGraph (Finset G))
    (htrans : ∀ S T a, Γ.Adj (translateSupport S a) (translateSupport T a) ↔
      Γ.Adj S T) (a : G) : Γ.Dart ≃ Γ.Dart where
  toFun d := ⟨(translateSupport d.fst a, translateSupport d.snd a),
    (htrans d.fst d.snd a).mpr d.adj⟩
  invFun d := ⟨(translateSupport d.fst (-a), translateSupport d.snd (-a)),
    (htrans d.fst d.snd (-a)).mpr d.adj⟩
  left_inv d := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext <;> simp
  right_inv d := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext <;> simp [translateSupport_add]
















end Finite

end Couret.STROBO2TORS


