-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_preimage
-- name    : Couret.STROBO2TORS.exceptionalFibres_preimage
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:48.806254+00:00
-- url     : https://prove2.me/theorems/e3233c84-517d-4196-bbef-77bbfcc6780f
-- title:
--   An exceptional fibre is its support preimage
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For every exceptional fibre $F$, $$\{S\in\mathcal S_{\mathrm{exc}}:F(S)=F\}=F,$$ where $\mathcal S_{\mathrm{exc}}$ is the exceptional support family. Thus every support of that fibre is exceptional and the filtered preimage contains no others.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 252–277; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.exceptionalFibres_preimage

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem exceptionalFibres_preimage (F : Finset (Finset G))
    (hF : F ∈ (exceptionalFibres : Finset (Finset (Finset G)))) :
    exceptionalSupports.filter (fun S : Finset G => squareFibre S = F) = F := by sorry


























































end Finite
end Couret.STROBO2TORS
