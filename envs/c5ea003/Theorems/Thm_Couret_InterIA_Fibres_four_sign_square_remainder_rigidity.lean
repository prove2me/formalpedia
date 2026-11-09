-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_four_sign_square_remainder_rigidity
-- name    : Couret.InterIA.Fibres.four_sign_square_remainder_rigidity
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:38.187947+00:00
-- url     : https://prove2.me/theorems/d2e1924f-040e-4bf4-a2f9-0521fcfc8eea
-- title:
--   Four-term sign rigidity from equal negacyclic square remainders
-- statement:
--   Let $m\in\mathbb N$, let $i,j,k,l<m$ be pairwise distinct, and let $a,b,c,d\in\mathbb R$ be nonzero. Set $P=aX^i+bX^j+cX^k+dX^l$ and let $Q$ be obtained by independently choosing either sign for each of these four terms. If the remainders of $P^2$ and $Q^2$ on division by $X^m+1$ are equal, then
--
--   $$Q=P\quad\text{or}\quad Q=-P.$$
--
--   Thus negacyclic square data permits only a global sign for these four-term polynomials.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/FourSignRigidity.lean, lines 163–185; source file SHA-256 7457f510d3cb5dc7da1d3bc7f820517db19363da66a96ff0fd98a3e1f65bb956; theorem Couret.InterIA.Fibres.four_sign_square_remainder_rigidity

import Definitions.Def_Couret_FourSignRigidity_4bbe2289ca60
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Fibres_four_sign_square_rigidity
import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial

theorem four_sign_square_remainder_rigidity (m i j k l : ℕ)
    (hi : i < m) (hj : j < m) (hk : k < m) (hl : l < m)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (e0 e1 e2 e3 : Bool)
    (heq : ((monomial i a+monomial j b+monomial k c+monomial l d)^2) %ₘ (X^m+1) =
      ((signed e0 (monomial i a)+signed e1 (monomial j b)+
        signed e2 (monomial k c)+signed e3 (monomial l d))^2) %ₘ (X^m+1)) :
    signed e0 (monomial i a)+signed e1 (monomial j b)+
      signed e2 (monomial k c)+signed e3 (monomial l d) =
      monomial i a+monomial j b+monomial k c+monomial l d ∨
    signed e0 (monomial i a)+signed e1 (monomial j b)+
      signed e2 (monomial k c)+signed e3 (monomial l d) =
      -(monomial i a+monomial j b+monomial k c+monomial l d) := by sorry


end Couret.InterIA.Fibres
