-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_dilate_nat
-- name    : Couret.InterIA.Catalogue.Quarter.Primitive.dilate_nat
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:41:08.649859+00:00
-- url     : https://prove2.me/theorems/0a9d1544-7269-42d1-9637-86aa8df47897
-- title:
--   dilate nat
-- statement:
--   For all natural numbers $d,b,a$ with $d>0$, let $z$ be the cast of $a$ to $ℤ/(4b)ℤ$. Multiply $\operatorname{val}(z)$ by $d$ and cast the result to $ℤ/(4db)ℤ$; the result equals the cast of $da$. For $b>0$, $\operatorname{val}$ is the least nonnegative representative. The case $b=0$ is included: both rings are $ℤ$, $\operatorname{val}(z)=|z|$, and since $z=a≥0$ the formula reduces to $da=da$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPrimitiveReduction.lean, lines 12–18; source file SHA-256 04116ba5236184358d50490faa8000ec249e62fb1c5665b6d82deee453cd3c82; theorem Couret.InterIA.Catalogue.Quarter.Primitive.dilate_nat

import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_scaled_cast_eq
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Primitive
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem dilate_nat (d b a : ℕ) (hd : 0 < d) :
    dilate (4*(d*b)) d (a : ZMod (4*b))=(d*a : ℕ) := by sorry












end Couret.InterIA.Catalogue.Quarter.Primitive
