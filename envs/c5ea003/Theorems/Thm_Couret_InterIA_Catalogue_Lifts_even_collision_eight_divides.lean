-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Lifts_even_collision_eight_divides
-- name    : Couret.InterIA.Catalogue.Lifts.even_collision_eight_divides
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:03:01.449754+00:00
-- url     : https://prove2.me/theorems/6c984d00-9721-4b2e-aa79-5351e6e0505a
-- title:
--   even collision eight divides
-- statement:
--   For every positive integer $m$ and finite subsets $S,T$ of $R=ℤ/(2m)ℤ$, assume $|S|=|T|=4$, that for every $z∈R$ the numbers of ordered pairs in $S²$ and $T²$ summing to $z$ agree, and that there are no unit $u∈R$ and $v∈R$ with $uS+v=T$. Then $8∣2m$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/EightDivisibility.lean, lines 23–44; source file SHA-256 c1e24c538efdd8579ea1a9504cf3b8fecf6a89850119729cc137f53baf1d1fc4; theorem Couret.InterIA.Catalogue.Lifts.even_collision_eight_divides

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
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
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_two_lift_affine
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_two_orbit_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Orbits_collision_orbit_shapes
import Theorems.Thm_Couret_InterIA_QuotientBridge_even_L4_four_divides_order
import Theorems.Thm_Couret_InterIA_QuotientBridge_period_four_eight_divides
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Orbits
open Couret.InterIA.Parity

theorem even_collision_eight_divides (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) : 8 ∣ 2*m := by sorry




end Couret.InterIA.Catalogue.Lifts
