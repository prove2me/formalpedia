-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_singleton_collision_product_odd_annihilator_iff
-- name    : Couret.InterIA.SingletonNecessity.singleton_collision_product_odd_annihilator_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:24:53.952981+00:00
-- url     : https://prove2.me/theorems/5e986b24-64d3-4920-a8ae-9284da0936b2
-- title:
--   Odd factors do not change singleton-collision existence
-- statement:
--   Let $P,H$ be abelian groups and $k\ge0$ with $(2k+1)y=0$ for every $y\in H$. The product $P\times H$ admits two four-element supports with singleton intersection and equal ordered-sum counts if and only if $P$ does: $$\operatorname{Collision}_1(P\times H)\iff\operatorname{Collision}_1(P).$$ No finiteness assumption is made on either group.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/PrimaryReduction.lean, lines 75–82; source file SHA-256 ab87827fa5f33af12f833abbff68b1c49c6fbcf94b8b26736a01d6fd13dd2745; theorem Couret.InterIA.SingletonNecessity.singleton_collision_product_odd_annihilator_iff

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_c4_square_embedding_product_factor
import Theorems.Thm_Couret_InterIA_SingletonNecessity_four_torsion_trivial_of_odd_annihilator
import Theorems.Thm_Couret_InterIA_SingletonNecessity_singleton_collision_iff_contains_c4_square
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary Couret.InterIA.Parity
variable {P H : Type*} [AddCommGroup P] [AddCommGroup H]

theorem singleton_collision_product_odd_annihilator_iff
    [DecidableEq P] [DecidableEq H] (k : ℕ)
    (hH : ∀ y : H, (2*k+1) • y=0) :
    (∃ A B : Finset (P × H), A.card=4 ∧ B.card=4 ∧ (A ∩ B).card=1 ∧
      ∀ z, orderedSquare A z=orderedSquare B z) ↔
    (∃ A B : Finset P, A.card=4 ∧ B.card=4 ∧ (A ∩ B).card=1 ∧
      ∀ z, orderedSquare A z=orderedSquare B z) := by sorry


end Couret.InterIA.SingletonNecessity
