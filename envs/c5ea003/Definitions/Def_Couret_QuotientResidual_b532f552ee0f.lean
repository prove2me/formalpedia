-- Prove2me | Definitions.Def_Couret_QuotientResidual_b532f552ee0f
-- name    : Couret_QuotientResidual_b532f552ee0f
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:05:39.268732+00:00
-- url     : https://prove2.me/theorems/cf8ca4ad-60a4-42cc-8320-f08f92da1eba
-- title:
--   Catalogue residual in the quotient group ring
-- statement:
--   Defines the unit point mass at a residue modulo $m$ and the residual $\pi_*(1_C)+\delta_{\pi(a)}+\delta_{\pi(b)}$ for a support $C$ modulo $2m$. This packages the quotient group-ring element used to compare lifted collision configurations.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientResidual.lean; source file SHA-256 29c3ae2cbecdf646a84bc5ab6931803cdc7db5ad9705778c5cd73f60b149f4bb

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

noncomputable def A {m : ℕ} (x : ZMod m) : AddMonoidAlgebra ℤ (ZMod m) :=
  AddMonoidAlgebra.single x 1

noncomputable def residual (m : ℕ) (C : Finset (ZMod (2*m))) (a b : ZMod (2*m)) :
    AddMonoidAlgebra ℤ (ZMod m) := push m (indicator C)+A (projection m a)+A (projection m b)

















end Couret.InterIA.Catalogue


