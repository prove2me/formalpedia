-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Lifts_odd_quarter_half_mul
-- name    : Couret.InterIA.Catalogue.Lifts.odd_quarter_half_mul
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:12.578057+00:00
-- url     : https://prove2.me/theorems/15c1610b-30ff-425a-9d20-6ae8a7d2df57
-- title:
--   odd quarter half mul
-- statement:
--   For every integer $m>0$ with $m≡2$ modulo $4$ and every $r∈ℤ/(2m)ℤ$ satisfying $2r=m$, the ring product $mr$ equals $m$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/PeriodTwoAffine.lean, lines 15–39; source file SHA-256 cc86608effa2553f8b9ea7ce56e9e7307d0f98817bbef21c3e7da274c8fc54e9; theorem Couret.InterIA.Catalogue.Lifts.odd_quarter_half_mul

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.NormalForm

theorem odd_quarter_half_mul (m : ℕ) (hm : 0 < m) (hmod : m%4=2)
    (r : ZMod (2*m)) (hr : r+r=m) : (m : ZMod (2*m))*r=m := by sorry




end Couret.InterIA.Catalogue.Lifts
