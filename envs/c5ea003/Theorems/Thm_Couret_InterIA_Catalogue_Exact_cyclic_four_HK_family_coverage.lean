-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Exact_cyclic_four_HK_family_coverage
-- name    : Couret.InterIA.Catalogue.Exact.cyclic_four_HK_family_coverage
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:52:45.40256+00:00
-- url     : https://prove2.me/theorems/a29f8fbe-77e6-4bac-b99a-84710e677b7f
-- title:
--   cyclic four HK family coverage
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. For every natural n≥4 and finite S,T⊆ℤ/nℤ with |S|=|T|=4 and Q(S,z)=Q(T,z) for every z, either S and T are affinely equivalent, or there exist a natural b≥2 with 4b dividing n, a unit u∈ℤ/nℤ, and v,t∈ℤ/nℤ with 2t=0 satisfying the following. Put k=n/(4b), E={0,1,b,2b+1}⊆ℤ/(4b)ℤ, F={0,b,b+1,3b+1}⊆ℤ/(4b)ℤ, and f(z)=u(k·val(z))+v∈ℤ/nℤ, where val is the least nonnegative representative. Either S=f(E) and T=f(F)+t, or S=f(F) and T=f(E)+t. The quotient is natural-number division, exact here by divisibility.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/CyclicCatalogueEquivalence.lean, lines 114–122; source file SHA-256 95b4e1f9e11870b2601da7a449b4e7e19d0c727e91663c1bc23225c4a62f333f; theorem Couret.InterIA.Catalogue.Exact.cyclic_four_HK_family_coverage

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
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_cyclic_four_historical_catalogue_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_historical_catalogue_generates_family
import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
import Definitions.Def_Couret_InteriaC4m_265d5cdb2807

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Ambient

theorem cyclic_four_HK_family_coverage (n : ℕ) (hn : 4 ≤ n) (S T : Finset (ZMod n))
    (hS : S.card=4) (hT : T.card=4) (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    AffineEquivalent S T ∨ ClassicalFamilyCatalogue n S T := by sorry


end Couret.InterIA.Catalogue.Exact
