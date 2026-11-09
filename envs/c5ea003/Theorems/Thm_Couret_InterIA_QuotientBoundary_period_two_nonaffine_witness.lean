-- Prove2me | Theorems.Thm_Couret_InterIA_QuotientBoundary_period_two_nonaffine_witness
-- name    : Couret.InterIA.QuotientBoundary.period_two_nonaffine_witness
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:50:10.015501+00:00
-- url     : https://prove2.me/theorems/0d4a6c38-aad1-4e26-a678-8c917a3b110a
-- title:
--   period two nonaffine witness
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. For S={0,1,2,5} and T={0,2,3,7} in ℤ/8ℤ, all three assertions hold: S,T are not affinely equivalent; Q(S,z)=Q(T,z) for every z∈ℤ/8ℤ; and the reduction modulo 4 of (3−1)∈ℤ/8ℤ has additive order 2.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/BoundaryQuotient.lean, lines 14–32; source file SHA-256 918aaf1b65a103f033a7562bf2ae93c603e2345f4ec10a87cdf95cb70e98f7e9; theorem Couret.InterIA.QuotientBoundary.period_two_nonaffine_witness

import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.QuotientBoundary
open Couret.InterIA.Parity

theorem period_two_nonaffine_witness :
    ¬ Couret.InterIA.NormalForm.AffineEquivalent
      ({0,1,2,5} : Finset (ZMod 8)) {0,2,3,7} ∧
    (∀ z : ZMod 8, orderedSquare ({0,1,2,5} : Finset (ZMod 8)) z =
      orderedSquare ({0,2,3,7} : Finset (ZMod 8)) z) ∧
    addOrderOf (Couret.InterIA.Projection.projection 4 ((3 : ZMod 8)-1))=2 := by sorry


end Couret.InterIA.QuotientBoundary
