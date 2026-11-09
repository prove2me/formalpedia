-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Lifts_cyclic_collision_eight_divides
-- name    : Couret.InterIA.Catalogue.Lifts.cyclic_collision_eight_divides
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:08:30.695203+00:00
-- url     : https://prove2.me/theorems/f5e2327a-8dde-4f8d-90a8-71eb84c04b76
-- title:
--   cyclic collision eight divides
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. For every natural n≥4 and finite S,T⊆ℤ/nℤ with |S|=|T|=4, Q(S,z)=Q(T,z) for every z∈ℤ/nℤ, and S,T not affinely equivalent, 8 divides n.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/EightDivisibility.lean, lines 46–56; source file SHA-256 c1e24c538efdd8579ea1a9504cf3b8fecf6a89850119729cc137f53baf1d1fc4; theorem Couret.InterIA.Catalogue.Lifts.cyclic_collision_eight_divides

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
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_even_collision_eight_divides
import Theorems.Thm_Couret_InterIA_NormalForm_cyclic_four_L4
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Orbits
open Couret.InterIA.Parity

theorem cyclic_collision_eight_divides (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) : 8 ∣ n := by sorry


end Couret.InterIA.Catalogue.Lifts
