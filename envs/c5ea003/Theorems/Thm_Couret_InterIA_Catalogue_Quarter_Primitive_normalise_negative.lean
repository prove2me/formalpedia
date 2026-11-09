-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_normalise_negative
-- name    : Couret.InterIA.Catalogue.Quarter.Primitive.normalise_negative
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:42:59.049803+00:00
-- url     : https://prove2.me/theorems/ea0835a0-544d-4abd-bca6-375535ebedb8
-- title:
--   normalise negative
-- statement:
--   Write $P_q(x)=\{0,q,x,x+2q\}$, $B_q(x)=\{0,q,x+q,x+3q\}$ and $D_q=\{0,q,2q,3q\}$ in $ℤ/(4q)ℤ$. For every natural number $q$, residue $x∈ℤ/(4q)ℤ$, and unit $u$, if $uq=-q$ and $ux=1$, then $uP_q(x)+q=B_q(1)$ and $uB_q(x)+q=P_q(1)$. Neither positivity of $q$ nor admissibility of $x$ is assumed; $q=0$ is included in $ℤ$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPrimitiveNormalisation.lean, lines 36–51; source file SHA-256 887d1f22b7114913eff0206bd9fb0b0b10e19d86cf09f8c53729d69597242304; theorem Couret.InterIA.Catalogue.Quarter.Primitive.normalise_negative

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_four_quarters_zero
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Primitive
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter.AffineCriterion

theorem normalise_negative (q : ℕ) (x : ZMod (4*q)) (u : (ZMod (4*q))ˣ)
    (huq : (u : ZMod (4*q))*q= -q) (hux : (u : ZMod (4*q))*x=1) :
    (patternA q x).image (fun z => (u : ZMod (4*q))*z+q)=patternB q 1 ∧
    (patternB q x).image (fun z => (u : ZMod (4*q))*z+q)=patternA q 1 := by sorry






end Couret.InterIA.Catalogue.Quarter.Primitive
