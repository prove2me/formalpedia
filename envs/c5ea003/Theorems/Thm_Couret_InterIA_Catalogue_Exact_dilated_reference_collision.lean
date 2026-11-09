-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Exact_dilated_reference_collision
-- name    : Couret.InterIA.Catalogue.Exact.dilated_reference_collision
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:13:59.386107+00:00
-- url     : https://prove2.me/theorems/a5ae10fe-92a3-426b-9fbe-ef38f9d4659c
-- title:
--   Dilated reference collision
-- statement:
--   For natural numbers $n,d,b$ with $n=4db$, $d>0$, $b>0$ and $b\bmod4=2$, let $S,T\subseteq\mathbb Z/n\mathbb Z$ be the images of $\{0,b,1,1+2b\}$ and $\{0,b,1+b,1+3b\}$ in $\mathbb Z/(4b)\mathbb Z$ under $z\mapsto d\operatorname{val}(z)$ modulo $n$, where $\operatorname{val}$ is the least nonnegative representative. Then $|S|=|T|=4$, their ordered-pair sum counts agree at every element, and no unit $u$ and element $v$ satisfy $uS+v=T$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/ReferenceCatalogueConverse.lean, lines 94–115; source file SHA-256 b8960db280a86d8c11a71df15e18d41866b1c6a5e978040912f6676f87ebfbd0; theorem Couret.InterIA.Catalogue.Exact.dilated_reference_collision

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
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_scaled_parameter_admissible
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_nonaffine_iff_gcd
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_patternA_dilate
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_patternB_dilate
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_patterns_collision
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternA_card_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternB_card_iff
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport

theorem dilated_reference_collision (n d b : ℕ) (hn : n=4*(d*b))
    (hd : 0 < d) (hb : 0 < b) (hm : b%4=2) :
    FourCollision ((patternA b 1).image (dilate n d))
      ((patternB b 1).image (dilate n d)) := by sorry




end Couret.InterIA.Catalogue.Exact
