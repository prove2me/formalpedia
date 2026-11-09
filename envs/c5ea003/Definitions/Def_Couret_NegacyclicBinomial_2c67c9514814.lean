-- Prove2me | Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814
-- name    : Couret_NegacyclicBinomial_2c67c9514814
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:07.488265+00:00
-- url     : https://prove2.me/theorems/a9dee3e7-347c-4407-bd5f-f8307af341cd
-- title:
--   Reduced product modulo a negacyclic relation
-- statement:
--   For natural $m,r,s$ and real $a,b$, define $$R=1+aX^r+bX^s+\begin{cases}abX^{r+s}&r+s<m,\\-abX^{r+s-m}&r+s\ge m.\end{cases}$$ This explicit polynomial represents the wrapped cross term under $X^m=-1$, including the boundary $r+s=m$.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/NegacyclicBinomial.lean; source file SHA-256 588e3d124d25fde2fdb187a567942b85fcf8e96074f04925453df69fbe86d890

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

/-- Canonical reduced coefficient polynomial of two normalised real binomials. -/
noncomputable def reducedProduct (m r s : ℕ) (a b : ℝ) : ℝ[X] :=
  1 + monomial r a + monomial s b +
    if r+s < m then monomial (r+s) (a*b)
    else monomial (r+s-m) (-(a*b))

















end Couret.InterIA.Fibres


