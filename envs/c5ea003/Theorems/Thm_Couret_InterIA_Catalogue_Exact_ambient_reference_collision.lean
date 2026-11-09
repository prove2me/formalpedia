-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Exact_ambient_reference_collision
-- name    : Couret.InterIA.Catalogue.Exact.ambient_reference_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:37.594526+00:00
-- url     : https://prove2.me/theorems/07169494-fa5d-4845-bfaf-38965b1c9467
-- title:
--   ambient reference collision
-- statement:
--   For every natural number $n$ and finite subsets $S,T$ of $ℤ/nℤ$, suppose there exist integers $d,b>0$ with $n=4db$ and $b≡2$ modulo $4$, a unit $u$ modulo $n$, and a residue $v$, such that $(uS+v,uT+v)$ is, in either order, the pair obtained by sending $\{0,b,1,1+2b\}$ and $\{0,b,1+b,1+3b\}$ from $ℤ/(4b)ℤ$ to $ℤ/nℤ$ by $z↦d\operatorname{val}(z)$, with $\operatorname{val}$ the least nonnegative representative. Then $|S|=|T|=4$, the ordered-pair sum counts agree at every residue, and no unit $a$ and residue $c$ have $aS+c=T$. The hypothesis excludes $n=0$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/ReferenceCatalogueConverse.lean, lines 117–126; source file SHA-256 b8960db280a86d8c11a71df15e18d41866b1c6a5e978040912f6676f87ebfbd0; theorem Couret.InterIA.Catalogue.Exact.ambient_reference_collision

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
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_affine_equivalent_symm
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_common_affine_equivalent_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_dilated_reference_collision
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_square_pair_affine_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Parameters_affine_image_card
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport

theorem ambient_reference_collision (n : ℕ) (S T : Finset (ZMod n))
    (h : AmbientReferenceForm n S T) : FourCollision S T := by sorry


end Couret.InterIA.Catalogue.Exact
