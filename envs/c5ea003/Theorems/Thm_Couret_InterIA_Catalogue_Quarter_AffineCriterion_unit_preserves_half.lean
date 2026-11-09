-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_unit_preserves_half
-- name    : Couret.InterIA.Catalogue.Quarter.AffineCriterion.unit_preserves_half
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:33:02.604125+00:00
-- url     : https://prove2.me/theorems/ac7d488f-b731-47d9-9652-9ad75ef7ea5d
-- title:
--   Units preserve the half element
-- statement:
--   For every positive natural $q$ and unit $u\in(\mathbb Z/(4q)\mathbb Z)^\times$, $u(2q)=2q$ in $\mathbb Z/(4q)\mathbb Z$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterAffineGeometry.lean, lines 12–29; source file SHA-256 4fc9cdbc6c8581db933863c792c5b7374b8c41f0609ff0ee3db720e92e88e383; theorem Couret.InterIA.Catalogue.Quarter.AffineCriterion.unit_preserves_half

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_four_quarters_zero
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_two_quarters_ne_zero
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Finset Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm

theorem unit_preserves_half (q : ℕ) (hq : 0 < q) (u : (ZMod (4*q))ˣ) :
    (u : ZMod (4*q))*(2 • (q : ZMod (4*q)))=2 • (q : ZMod (4*q)) := by sorry










end Couret.InterIA.Catalogue.Quarter.AffineCriterion
