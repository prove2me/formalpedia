-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_QuarterBoundary_even_q_admissible_affine
-- name    : Couret.InterIA.Catalogue.QuarterBoundary.even_q_admissible_affine
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:01.774024+00:00
-- url     : https://prove2.me/theorems/decf90d6-7815-4eb2-bfdc-1b75d045b2b9
-- title:
--   even q admissible affine
-- statement:
--   The natural number $4$ is even; the residue $1∈ℤ/16ℤ$ lies outside $\{0,4,8,12\}$; and there exist a unit $u$ modulo $16$ and residue $v$ such that $u\{0,4,1,9\}+v=\{0,4,5,13\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterBoundaryControls.lean, lines 21–26; source file SHA-256 46320fa4777e97f608759251930dffe73055959b3994fdef4da4481afead4868; theorem Couret.InterIA.Catalogue.QuarterBoundary.even_q_admissible_affine

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
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
namespace Couret.InterIA.Catalogue.QuarterBoundary
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm Couret.InterIA.Parity

theorem even_q_admissible_affine :
    Even (4 : ℕ) ∧ (1 : ZMod (4*4)) ∉ badParameters 4 ∧
    AffineEquivalent (patternA 4 1) (patternB 4 1) := by sorry


end Couret.InterIA.Catalogue.QuarterBoundary
