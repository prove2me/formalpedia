-- Prove2me | Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
-- name    : Couret_QuarterArithmeticCore_9ead8b9209d0
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:14:27.789984+00:00
-- url     : https://prove2.me/theorems/3e840727-d5a3-4e70-92eb-c01e2598ddb3
-- title:
--   A simultaneous unit action on quarter-period coordinates
-- statement:
--   Defines the existence of a unit $u$ modulo $4q$ satisfying $uq=eq$ and $ux=x+kq$. The parameters $q,x,e,k$ are natural numbers interpreted in the indicated residue ring. This records the arithmetic system used in quarter-period affine normalization.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterArithmeticCore.lean; source file SHA-256 82693435b82358edeca13f5b4d237954c592a51649c16be781ec5926b1273c45

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
import Definitions.Def_Couret_QuarterAffineCriterion_d1003281e8a6
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic

/-- e=1,3 and k=1,3,0,2 encode systems I,II,III,IV. -/
def System (q x e k : ℕ) : Prop :=
  ∃ u : (ZMod (4*q))ˣ,
    (u : ZMod (4*q))*(q : ZMod (4*q))=e*q ∧
    (u : ZMod (4*q))*(x : ZMod (4*q))=x+k*q







end Couret.InterIA.Catalogue.Quarter.Arithmetic


