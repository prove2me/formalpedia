-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Exact_ordered_square_affine_at
-- name    : Couret.InterIA.Catalogue.Exact.ordered_square_affine_at
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:52.490111+00:00
-- url     : https://prove2.me/theorems/123412d0-7ceb-4742-8e19-f60df5383983
-- title:
--   Affine transport of an ordered square coefficient
-- statement:
--   For every natural $n$, finite subset $S\subseteq R=\operatorname{ZMod}(n)$, unit $u\in R^\times$ and $v,z\in R$, the number of ordered pairs in $(uS+v)^2$ summing to $uz+2v$ equals the number of ordered pairs in $S^2$ summing to $z$. This includes empty $S$ and $n=0$, where $R=\mathbb Z$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/ReferenceCatalogueConverse.lean, lines 13–32; source file SHA-256 b8960db280a86d8c11a71df15e18d41866b1c6a5e978040912f6676f87ebfbd0; theorem Couret.InterIA.Catalogue.Exact.ordered_square_affine_at

import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_unit_affine_injective
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport

theorem ordered_square_affine_at {n : ℕ} (S : Finset (ZMod n))
    (u : (ZMod n)ˣ) (v z : ZMod n) :
    orderedSquare (S.image (fun x => (u : ZMod n)*x+v)) ((u : ZMod n)*z+(v+v))=
      orderedSquare S z := by sorry
















end Couret.InterIA.Catalogue.Exact
