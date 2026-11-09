-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_pair_separations
-- name    : Couret.InterIA.Catalogue.Quarter.admissible_pair_separations
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:32:58.214108+00:00
-- url     : https://prove2.me/theorems/9bea2708-398f-400b-9697-e6431006818f
-- title:
--   Admissible pair separations
-- statement:
--   For every natural $q$ and $x\in\operatorname{ZMod}(4q)$ with $x\notin\{0,q,2q,3q\}$, one has $x\ne0$, $x\ne q$, $x+2q\ne0$ and $x+2q\ne q$. The case $q=0$ is included, with $\operatorname{ZMod}(0)=\mathbb Z$ and the excluded set equal to $\{0\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPatterns.lean, lines 60–77; source file SHA-256 9b8c9c084f6777ce5ceb009e93059cec597e0b75776aa3c220bc02c5f8961a7b; theorem Couret.InterIA.Catalogue.Quarter.admissible_pair_separations

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_four_quarters_zero
import Definitions.Def_Couret_AffineParameterControls_321393084939

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter
open Finset Couret.InterIA.Catalogue.Parameters Couret.InterIA.Parity

theorem admissible_pair_separations (q : ℕ) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) :
    x ≠ 0 ∧ x ≠ q ∧ x+2 • (q : ZMod (4*q)) ≠ 0 ∧ x+2 • (q : ZMod (4*q)) ≠ q := by sorry










end Couret.InterIA.Catalogue.Quarter
