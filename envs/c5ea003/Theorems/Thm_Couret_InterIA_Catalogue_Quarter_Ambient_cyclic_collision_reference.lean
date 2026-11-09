-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_cyclic_collision_reference
-- name    : Couret.InterIA.Catalogue.Quarter.Ambient.cyclic_collision_reference
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:32:06.505733+00:00
-- url     : https://prove2.me/theorems/13212460-19cf-4dc1-a0eb-360fa4757885
-- title:
--   Ambient reference form for a collision
-- statement:
--   For every natural $n\ge4$ and four-element subsets $S,T\subseteq R=\mathbb Z/n\mathbb Z$ whose ordered-pair sum counts agree everywhere and for which no unit $u$ and $v\in R$ satisfy $uS+v=T$, there exist a positive natural $m$ with $n=2m$, $t\in\{0,m\}$, positive naturals $d,b$ with $n=4db$ and $b\bmod4=2$, a unit $U\in R^\times$ and $V\in R$, such that $US+V$ and $U(T+t)+V$, in either order, are the images of $\{0,b,1,1+2b\}$ and $\{0,b,1+b,1+3b\}$ from $\mathbb Z/(4b)\mathbb Z$ under $z\mapsto d\operatorname{val}(z)$ modulo $n$, where $\operatorname{val}$ is the least nonnegative representative.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/AmbientCollisionAssembly.lean, lines 62–75; source file SHA-256 5644ce4fd9e8bafd6f25e78efbcd512000a4dad8e6841d2bcb4e0131600ca136; theorem Couret.InterIA.Catalogue.Quarter.Ambient.cyclic_collision_reference

import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541
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
import Theorems.Thm_Couret_InterIA_Catalogue_AffineTransport_unilateral_translation_equivalent_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Eighth_nonaffine_collision_two_form
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_cyclic_collision_eight_divides
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_normalised_patterns_reference_form
import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Ambient
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive Couret.InterIA.Catalogue.Parameters
open Couret.InterIA.Catalogue.AffineTransport Couret.InterIA.Parity

theorem cyclic_collision_reference (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hna : ¬ AffineEquivalent S T) :
    ∃ m : ℕ, 0 < m ∧ n=2*m ∧ ∃ t : ZMod n, (t=0 ∨ t=m) ∧
      AmbientReferenceForm n S (T.image (fun z => z+t)) := by sorry


end Couret.InterIA.Catalogue.Quarter.Ambient
