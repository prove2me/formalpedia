-- Prove2me | Definitions.Def_Couret_CyclicCatalogueEquivalence_bddddc095b9c
-- name    : Couret_CyclicCatalogueEquivalence_bddddc095b9c
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:17:18.472809+00:00
-- url     : https://prove2.me/theorems/8be262db-506b-4e55-9aa5-48fa9ea59980
-- title:
--   Historical and classical cyclic collision catalogues
-- statement:
--   Three predicates encode the reference normal form, its allowed half-turn adjustment, and the forward classical-family generator. They use positive cyclic dilations, common affine automorphisms, an optional support swap, and a two-torsion translation. The historical reference form requires $n=4db$ with $d,b>0$ and $b\equiv2\pmod4$; the classical generator requires $b\ge2$ and $4b\mid n$. This bundle retains those different presentations explicitly.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/CyclicCatalogueEquivalence.lean; source file SHA-256 95b4e1f9e11870b2601da7a449b4e7e19d0c727e91663c1bc23225c4a62f333f

import Aesop
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
import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
import Definitions.Def_Couret_InteriaC4m_265d5cdb2807

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Ambient





def HistoricalReferenceForm (n : ℕ) (S T : Finset (ZMod n)) : Prop :=
  ∃ d b : ℕ, 0 < d ∧ 0 < b ∧ n=4*(d*b) ∧ b%4=2 ∧
    ∃ u : (ZMod n)ˣ, ∃ v : ZMod n,
      (S.image (fun z => (u : ZMod n)*z+v)=(Couret.InterIA.C4m.T b).image (dilate n d) ∧
       T.image (fun z => (u : ZMod n)*z+v)=(Couret.InterIA.C4m.U b).image (dilate n d)) ∨
      (S.image (fun z => (u : ZMod n)*z+v)=(Couret.InterIA.C4m.U b).image (dilate n d) ∧
       T.image (fun z => (u : ZMod n)*z+v)=(Couret.InterIA.C4m.T b).image (dilate n d))

def HistoricalCatalogue (n : ℕ) (S T : Finset (ZMod n)) : Prop :=
  ∃ m : ℕ, 0 < m ∧ n=2*m ∧ ∃ t : ZMod n, (t=0 ∨ t=m) ∧
    HistoricalReferenceForm n S (T.image (fun z => z+t))







/-- The FAMILY_C4M generator in the original protocol, with the actual n/(4b) injection. -/
def ClassicalFamilyCatalogue (n : ℕ) (S T : Finset (ZMod n)) : Prop :=
  ∃ b : ℕ, 2 ≤ b ∧ 4*b ∣ n ∧ ∃ u : (ZMod n)ˣ, ∃ v t : ZMod n, t+t=0 ∧
    ((S=((Couret.InterIA.C4m.T b).image (dilate n (n/(4*b)))).image (fun z => (u : ZMod n)*z+v) ∧
     T=(((Couret.InterIA.C4m.U b).image (dilate n (n/(4*b)))).image (fun z => (u : ZMod n)*z+v)).image (fun z => z+t)) ∨
    (S=((Couret.InterIA.C4m.U b).image (dilate n (n/(4*b)))).image (fun z => (u : ZMod n)*z+v) ∧
     T=(((Couret.InterIA.C4m.T b).image (dilate n (n/(4*b)))).image (fun z => (u : ZMod n)*z+v)).image (fun z => z+t)))





end Couret.InterIA.Catalogue.Exact


