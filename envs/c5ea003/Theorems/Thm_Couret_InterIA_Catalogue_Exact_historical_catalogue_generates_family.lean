-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Exact_historical_catalogue_generates_family
-- name    : Couret.InterIA.Catalogue.Exact.historical_catalogue_generates_family
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:18.06814+00:00
-- url     : https://prove2.me/theorems/f7b62bb7-e962-4e17-8855-a8de15f60a2b
-- title:
--   historical catalogue generates family
-- statement:
--   For every natural number $n$ and finite subsets $S,T$ of $ℤ/nℤ$, suppose there exist integers $m>0$, $d>0$, $b>0$ with $n=2m=4db$ and $b≡2$ modulo $4$, a residue $t∈\{0,m\}$, a unit $u∈ℤ/nℤ$, and $v∈ℤ/nℤ$, such that the ordered pair $(uS+v,u(T+t)+v)$ is, in either order, the pair of images of $\{0,1,b,2b+1\}$ and $\{0,b,b+1,3b+1\}$ from $ℤ/(4b)ℤ$ under $z↦d\operatorname{val}(z)$ in $ℤ/nℤ$, where $\operatorname{val}$ is the least nonnegative representative. Then there exist a natural number $b≥2$ with $4b∣n$, a unit $a$ modulo $n$, and residues $v,t$ with $2t=0$, such that $S$ is the image of one of $\{0,1,b,2b+1\}$ and $\{0,b,b+1,3b+1\}$ from $ℤ/(4b)ℤ$ under $z↦a((n/(4b))\operatorname{val}(z))+v$, and $T$ is the image of the other under the same map followed by translation by $t$. The hypothesis implies $n>0$; no condition $b≡2$ modulo $4$ is imposed on the conclusion’s chosen $b$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/CyclicCatalogueEquivalence.lean, lines 72–112; source file SHA-256 95b4e1f9e11870b2601da7a449b4e7e19d0c727e91663c1bc23225c4a62f333f; theorem Couret.InterIA.Catalogue.Exact.historical_catalogue_generates_family

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
import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
import Definitions.Def_Couret_InteriaC4m_265d5cdb2807

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Ambient

theorem historical_catalogue_generates_family (n : ℕ) (S T : Finset (ZMod n))
    (h : HistoricalCatalogue n S T) : ClassicalFamilyCatalogue n S T := by sorry




end Couret.InterIA.Catalogue.Exact
