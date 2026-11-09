-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Affine_unit_mul_add_order
-- name    : Couret.InterIA.Catalogue.Affine.unit_mul_add_order
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:32:26.738947+00:00
-- url     : https://prove2.me/theorems/c12a9967-7a9d-4633-b087-5c1b2ce396ca
-- title:
--   unit mul add order
-- statement:
--   Here ℤ/0ℤ means ℤ, so modulus zero is included. For every natural n, every unit u of ℤ/nℤ and every x∈ℤ/nℤ, the additive order of ux equals the additive order of x, with additive order defined as 0 for an element of infinite additive order.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/CyclicStepNormalisation.lean, lines 8–22; source file SHA-256 56cce8151cfebd4ef854f2c3a199f2449366340bb19ea338b9c03a0bd52c731a; theorem Couret.InterIA.Catalogue.Affine.unit_mul_add_order

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts

theorem unit_mul_add_order (n : ℕ) (u : (ZMod n)ˣ) (x : ZMod n) :
    addOrderOf ((u : ZMod n)*x)=addOrderOf x := by sorry








end Couret.InterIA.Catalogue.Affine
