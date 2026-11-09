-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Affine_cyclic_step_unit_normalisation
-- name    : Couret.InterIA.Catalogue.Affine.cyclic_step_unit_normalisation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:54.701464+00:00
-- url     : https://prove2.me/theorems/64643b38-eb7f-433d-879d-7c6893f53b88
-- title:
--   cyclic step unit normalisation
-- statement:
--   For every integer $n>0$, residue $r∈ℤ/nℤ$, and natural number $k$ equal to the additive order of $r$, there exist an integer $q>0$ and a unit $u$ modulo $n$ such that $n=kq$ and $r=uq$ modulo $n$. The additive order is the least positive annihilating integer; although $k=0$ is quantified, it cannot satisfy the hypothesis in this finite group.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/CyclicStepNormalisation.lean, lines 24–42; source file SHA-256 56cce8151cfebd4ef854f2c3a199f2449366340bb19ea338b9c03a0bd52c731a; theorem Couret.InterIA.Catalogue.Affine.cyclic_step_unit_normalisation

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
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_unit_mul_add_order
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts

theorem cyclic_step_unit_normalisation (n : ℕ) (hn : 0 < n) (r : ZMod n) (k : ℕ)
    (ho : addOrderOf r=k) :
    ∃ q : ℕ, 0 < q ∧ n=k*q ∧ ∃ u : (ZMod n)ˣ, r=(u : ZMod n)*(q : ZMod n) := by sorry






end Couret.InterIA.Catalogue.Affine
