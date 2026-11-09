-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Exact_cyclic_collision_catalogue_iff
-- name    : Couret.InterIA.Catalogue.Exact.cyclic_collision_catalogue_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:37:44.8662+00:00
-- url     : https://prove2.me/theorems/a64dc3cd-ba36-4a96-8766-97779be2a17c
-- title:
--   Exact cyclic collision catalogue
-- statement:
--   For every natural $n\ge4$ and finite subsets $S,T$ of $R=\mathbb Z/n\mathbb Z$, the following are equivalent: both sets have cardinality $4$, their numbers of ordered pairs summing to $z$ agree for every $z\in R$, and there is no unit $u$ and $v\in R$ with $uS+v=T$; and there exist a positive natural $m$ with $n=2m$ and $t\in\{0,m\}$, positive naturals $d,b$ with $n=4db$ and $b\bmod4=2$, a unit $U\in R^\times$ and $V\in R$ such that the two sets $US+V$ and $U(T+t)+V$, in either order, are the images of $\{0,b,1,1+2b\}$ and $\{0,b,1+b,1+3b\}$ from $\mathbb Z/(4b)\mathbb Z$ under $z\mapsto d\operatorname{val}(z)$ in $R$, where $\operatorname{val}$ is the least nonnegative representative.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/CyclicCatalogueEquivalence.lean, lines 40–54; source file SHA-256 95b4e1f9e11870b2601da7a449b4e7e19d0c727e91663c1bc23225c4a62f333f; theorem Couret.InterIA.Catalogue.Exact.cyclic_collision_catalogue_iff

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
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_ambient_reference_collision
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_four_collision_shift_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Ambient_cyclic_collision_reference
import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
import Definitions.Def_Couret_InteriaC4m_265d5cdb2807

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Ambient

theorem cyclic_collision_catalogue_iff (n : ℕ) (hn : 4 ≤ n) (S T : Finset (ZMod n)) :
    FourCollision S T ↔
      ∃ m : ℕ, 0 < m ∧ n=2*m ∧ ∃ t : ZMod n, (t=0 ∨ t=m) ∧
        AmbientReferenceForm n S (T.image (fun z => z+t)) := by sorry










end Couret.InterIA.Catalogue.Exact
