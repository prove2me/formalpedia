-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_residual_invariant
-- name    : Couret.InterIA.Catalogue.residual_invariant
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:31:24.598936+00:00
-- url     : https://prove2.me/theorems/48bbb7e9-916d-47a6-9d29-256a3e6cb292
-- title:
--   Residual invariance
-- statement:
--   For every positive natural $m$, finite subset $C\subseteq R=\mathbb Z/(2m)\mathbb Z$, and $a,b\in R$, let $\pi$ be reduction modulo $m$ and $F=\sum_{c\in C}X^{\pi(c)}+X^{\pi(a)}+X^{\pi(b)}$ in the integer group ring of $\mathbb Z/m\mathbb Z$, whose basis multiplies by $X^yX^z=X^{y+z}$. If $(X^{\pi(a)}-X^{\pi(b)})F=0$, then $F=X^{\pi(b-a)}F$. The set $C$ may be empty and $a=b$ is allowed.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientResidual.lean, lines 39–55; source file SHA-256 29c3ae2cbecdf646a84bc5ab6931803cdc7db5ad9705778c5cd73f60b149f4bb; theorem Couret.InterIA.Catalogue.residual_invariant

import Definitions.Def_Couret_QuotientResidual_b532f552ee0f
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_L4Assembly_154a326d9c14

set_option autoImplicit false
namespace Couret.InterIA.Catalogue
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.GroupRing
open Couret.InterIA.Projection

theorem residual_invariant (m : ℕ) (hm : 0 < m) (C : Finset (ZMod (2*m)))
    (a b : ZMod (2*m))
    (he : (A (projection m a)-A (projection m b))*residual m C a b=0) :
    residual m C a b=A (projection m (b-a))*residual m C a b := by sorry












end Couret.InterIA.Catalogue
