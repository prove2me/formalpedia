-- Prove2me | Definitions.Def_Couret_QuarterAffineCriterion_d1003281e8a6
-- name    : Couret_QuarterAffineCriterion_d1003281e8a6
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:14:06.729163+00:00
-- url     : https://prove2.me/theorems/53e12b82-74ae-470c-ac19-32f6facbac6e
-- title:
--   Four affine systems for quarter-period supports
-- statement:
--   For $x\in\mathbb Z/(4q)\mathbb Z$ and a unit $u$, the predicate consists of four systems: if $uq=q$, require $ux=x+q$ or $ux=x+3q$; if $uq=-q$, require $ux=x$ or $ux=x+2q$.
--
--   This finite disjunction records the multiplier equations used to test affine equivalence in the quarter-period case.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterAffineCriterion.lean; source file SHA-256 7575c3b014a769e070202229a8e9d2abee0368ed94316d08f50628cef77847e5

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
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm

def FourSystems (q : ℕ) (x : ZMod (4*q)) (u : (ZMod (4*q))ˣ) : Prop :=
  ((u : ZMod (4*q))*q=q ∧
    ((u : ZMod (4*q))*x=x+q ∨ (u : ZMod (4*q))*x=x+3 • (q : ZMod (4*q)))) ∨
  ((u : ZMod (4*q))*q= -q ∧
    ((u : ZMod (4*q))*x=x ∨ (u : ZMod (4*q))*x=x+2 • (q : ZMod (4*q))))

















end Couret.InterIA.Catalogue.Quarter.AffineCriterion


