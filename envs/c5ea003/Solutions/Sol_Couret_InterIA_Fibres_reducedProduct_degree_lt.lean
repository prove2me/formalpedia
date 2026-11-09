-- Prove2me | solution 1 for Couret.InterIA.Fibres.reducedProduct_degree_lt
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:54.139443+00:00
-- url     : https://prove2.me/submissions/b9a01843-3e5b-4192-800a-eb21833fcfcd

import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial



theorem p2m_local_reducedProduct_degree_lt (m r s : ℕ) (hr : r < m) (hs : s < m)
    (a b : ℝ) : (reducedProduct m r s a b).degree < (m : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  have hm : 0 < m := by omega
  have hk0 : k ≠ 0 := by omega
  have hkr : r ≠ k := by omega
  have hks : s ≠ k := by omega
  by_cases hsmall : r+s < m
  · have hsum : r+s ≠ k := by omega
    simp [reducedProduct, hsmall, coeff_monomial, coeff_one, hk0, hkr, hks, hsum]
  · have hsum : r+s-m ≠ k := by omega
    simp [reducedProduct, hsmall, coeff_monomial, coeff_one, hk0, hkr, hks, hsum]















end Couret.InterIA.Fibres

theorem solution : ∀ (m r s : Nat),
  @LT.lt.{0} Nat instLTNat r m →
    @LT.lt.{0} Nat instLTNat s m →
      ∀ (a b : Real),
        @LT.lt.{0} (WithBot.{0} Nat)
          (@Preorder.toLT.{0} (WithBot.{0} Nat) (@WithBot.instPreorder.{0} Nat Nat.instPreorder))
          (@Polynomial.degree.{0} Real Real.semiring (Couret.InterIA.Fibres.reducedProduct m r s a b))
          (@Nat.cast.{0} (WithBot.{0} Nat) (@WithBot.natCast.{0} Nat instNatCastNat) m) := @_root_.Couret.InterIA.Fibres.p2m_local_reducedProduct_degree_lt

