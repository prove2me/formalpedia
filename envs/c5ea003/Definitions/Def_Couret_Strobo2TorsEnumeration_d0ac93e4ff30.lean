-- Prove2me | Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
-- name    : Couret_Strobo2TorsEnumeration_d0ac93e4ff30
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:22.471684+00:00
-- url     : https://prove2.me/theorems/fdd8d059-cab5-4645-afc3-5d55ebb7c917
-- title:
--   Exceptional triple parameters and finite fibre families
-- statement:
--   The parameter support is
--
--   $$P(a,d,v)=\{a,a+v,a+v+d\}.$$
--
--   For a finite abelian group, exceptional parameters range over $G\times(G[2]\setminus\{0\})\times(G[3]\setminus\{0\})$. The bundle defines exceptional supports by square-fibre size $2|G[2]|$, their distinct fibres, the doubling image, nonzero three-torsion sign pairs, all triple supports and square fibres, and ordinary fibres of size $|G[2]|$. These definitions provide the finite parameter spaces for enumeration.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]





def paramSupport (p : (G × G) × G) : Finset G :=
  {p.1.1, p.1.1 + p.2, (p.1.1 + p.2) + p.1.2}









section Finite

variable [Fintype G]

def threeTorsion : Finset G := Finset.univ.filter (fun v => (v + v) + v = 0)

def exceptionalParams : Finset ((G × G) × G) :=
  (Finset.univ.product ((twoTorsion : Finset G).erase 0)).product
    ((threeTorsion : Finset G).erase 0)

def exceptionalSupports : Finset (Finset G) :=
  Finset.univ.powerset.filter (fun S => S.card = 3 ∧
    (squareFibre S).card = 2 * (twoTorsion : Finset G).card)

def exceptionalFibres : Finset (Finset (Finset G)) :=
  (exceptionalSupports : Finset (Finset G)).image squareFibre





























def doublingImages : Finset G := (Finset.univ : Finset G).image (fun a => a + a)









def threeSignPairs : Finset (Finset G) :=
  ((threeTorsion : Finset G).erase 0).image (fun v => ({v, -v} : Finset G))

















def tripleSupports : Finset (Finset G) := Finset.powersetCard 3 (Finset.univ : Finset G)

def allSquareFibres : Finset (Finset (Finset G)) :=
  (tripleSupports : Finset (Finset G)).image squareFibre

def ordinaryFibres : Finset (Finset (Finset G)) :=
  (allSquareFibres : Finset (Finset (Finset G))).filter
    (fun F => F.card = (twoTorsion : Finset G).card)



















end Finite
end Couret.STROBO2TORS


