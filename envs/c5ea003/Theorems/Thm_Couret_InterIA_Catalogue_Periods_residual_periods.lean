-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Periods_residual_periods
-- name    : Couret.InterIA.Catalogue.Periods.residual_periods
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:32:37.698833+00:00
-- url     : https://prove2.me/theorems/0493b2c7-9017-40fa-90bc-0d6597afe139
-- title:
--   Orders of residual periods
-- statement:
--   For every natural $m$, two-element finite subset $C\subseteq R=\operatorname{ZMod}(2m)$, $a,b\in R$, and nonzero $\delta\in Q=\operatorname{ZMod}(m)$, define $F=\sum_{c\in C}X^{\pi(c)}+X^{\pi(a)}+X^{\pi(b)}$ in $\mathbb Z[Q]$, where $\pi:R\to Q$ is the canonical cast and $X^xX^y=X^{x+y}$. If $F=X^\delta F$, then the additive order of $\delta$ is $2$ or $4$. The case $m=0$ is quantified, with both rings of residues interpreted as $\mathbb Z$; no distinctness among the projected atoms is assumed.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientPeriods.lean, lines 63–70; source file SHA-256 bd9057bd807a1c77c8c1dc1a052c267cfc2bf47a18692508e9871acc4ea527c8; theorem Couret.InterIA.Catalogue.Periods.residual_periods

import Definitions.Def_Couret_QuotientPeriods_cf8d74422994
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_residual_four_atoms
import Definitions.Def_Couret_QuotientResidual_b532f552ee0f
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Periods
open Finset Couret.InterIA.Catalogue Couret.InterIA.Parity Couret.InterIA.Projection
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem residual_periods (m : ℕ) (C : Finset (ZMod (2*m))) (hC : C.card=2)
    (a b : ZMod (2*m)) (δ : ZMod m) (hδ : δ ≠ 0)
    (he : residual m C a b=A δ*residual m C a b) :
    addOrderOf δ=2 ∨ addOrderOf δ=4 := by sorry






end Couret.InterIA.Catalogue.Periods
