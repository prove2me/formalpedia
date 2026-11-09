-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_four_sign_square_rigidity
-- name    : Couret.InterIA.Fibres.four_sign_square_rigidity
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:04.841057+00:00
-- url     : https://prove2.me/theorems/28e9868e-c80a-4bf7-8d27-307765e026da
-- title:
--   Four monomials admit only a global sign under square congruence
-- statement:
--   Let $m,i,j,k,l\in\mathbb N$ with four pairwise distinct exponents $i,j,k,l<m$, and let $a,b,c,d$ be nonzero real numbers. Put $P=aX^i+bX^j+cX^k+dX^l$, and form $Q$ by independently retaining or negating its four terms. If $X^m+1$ divides $P^2-Q^2$, then
--
--   $$Q=P\quad\text{or}\quad Q=-P.$$
--
--   Thus independent sign changes preserving the square modulo this negacyclic modulus reduce to a single global sign.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/FourSignRigidity.lean, lines 122–161; source file SHA-256 7457f510d3cb5dc7da1d3bc7f820517db19363da66a96ff0fd98a3e1f65bb956; theorem Couret.InterIA.Fibres.four_sign_square_rigidity

import Definitions.Def_Couret_FourSignRigidity_4bbe2289ca60
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_Couret_InterIA_Fibres_four_partition_rigidity
import Theorems.Thm_Couret_InterIA_Fibres_modulus_coprime_monomial
import Theorems.Thm_Couret_InterIA_Fibres_negacyclic_binomial_product_not_dvd
import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial

theorem four_sign_square_rigidity (m i j k l : ℕ)
    (hi : i < m) (hj : j < m) (hk : k < m) (hl : l < m)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (e0 e1 e2 e3 : Bool)
    (heq : (X^m+1 : ℝ[X]) ∣
      (monomial i a+monomial j b+monomial k c+monomial l d)^2 -
      (signed e0 (monomial i a)+signed e1 (monomial j b)+
       signed e2 (monomial k c)+signed e3 (monomial l d))^2) :
    signed e0 (monomial i a)+signed e1 (monomial j b)+
      signed e2 (monomial k c)+signed e3 (monomial l d) =
      monomial i a+monomial j b+monomial k c+monomial l d ∨
    signed e0 (monomial i a)+signed e1 (monomial j b)+
      signed e2 (monomial k c)+signed e3 (monomial l d) =
      -(monomial i a+monomial j b+monomial k c+monomial l d) := by sorry




end Couret.InterIA.Fibres
