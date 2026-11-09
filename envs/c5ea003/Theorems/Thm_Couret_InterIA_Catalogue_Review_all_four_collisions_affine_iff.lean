-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Review_all_four_collisions_affine_iff
-- name    : Couret.InterIA.Catalogue.Review.all_four_collisions_affine_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:23.420646+00:00
-- url     : https://prove2.me/theorems/557f41f5-94b0-4392-8047-839ee09bd4ca
-- title:
--   When all four-point collisions are affine
-- statement:
--   For every natural $n\ge4$, the assertion that for all finite subsets $S,T\subseteq\mathbb Z/n\mathbb Z$ with $|S|=|T|=4$ and equal numbers of ordered pairs summing to each $z$, there exist a unit $u$ and residue $v$ with $uS+v=T$, is equivalent to $8$ not dividing $n$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/ClassificationSummary.lean, lines 20–29; source file SHA-256 082a39afd00e22e7c7513a3b073bc6c896365fbccfaecd5761670e30b9e30098; theorem Couret.InterIA.Catalogue.Review.all_four_collisions_affine_iff

import Aesop
import Definitions.Def_Couret_CyclicCatalogueEquivalence_bddddc095b9c
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Basic
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
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_dilated_reference_collision
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_cyclic_collision_eight_divides
import Definitions.Def_Couret_CyclicCatalogueEquivalence_bddddc095b9c

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Review
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Exact Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive

theorem all_four_collisions_affine_iff (n : ℕ) (hn : 4 ≤ n) :
    (∀ S T : Finset (ZMod n), S.card=4 → T.card=4 →
      (∀ z, orderedSquare S z=orderedSquare T z) → AffineEquivalent S T) ↔ ¬ 8 ∣ n := by sorry


end Couret.InterIA.Catalogue.Review
