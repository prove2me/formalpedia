-- Prove2me | Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347
-- name    : Couret_QuarterPrimitiveReduction_b041ef56a347
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:14:47.638205+00:00
-- url     : https://prove2.me/theorems/debac2d0-002c-403e-b253-807a149a90a2
-- title:
--   Representative-based dilation between cyclic moduli
-- statement:
--   For natural $n,d$ and $z\in\mathbb Z/b\mathbb Z$, define the dilation by taking the standard natural representative of $z$ and reducing its multiple in the target modulus:
--
--   $$\operatorname{dilate}_{n,d}(z)=d\,\operatorname{val}(z)\pmod n.$$
--
--   This is a concrete function for primitive reduction arguments. The definition alone imposes no divisibility assumptions making it an additive map.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPrimitiveReduction.lean; source file SHA-256 04116ba5236184358d50490faa8000ec249e62fb1c5665b6d82deee453cd3c82

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
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Primitive
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Arithmetic

/-- The concrete dilation of reduced residue representatives into the original group. -/
def dilate (n d : ℕ) {b : ℕ} (z : ZMod b) : ZMod n := (d*z.val : ℕ)













end Couret.InterIA.Catalogue.Quarter.Primitive


