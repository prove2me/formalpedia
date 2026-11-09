-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_paramSupport_inter_twoTorsion_card
-- name    : Couret.STROBO2TORS.paramSupport_inter_twoTorsion_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:43:33.036102+00:00
-- url     : https://prove2.me/theorems/af29210a-e066-4a93-ac94-2a8251ea6f72
-- title:
--   Two-torsion profile of a parameter support
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For $a,d,v\in G$ with $2d=0\ne d$, $3v=0\ne v$, $$|P(a,d,v)\cap H|=\begin{cases}1&2a=0,\\2&2a\ne0\text{ and }2(a+v)=0,\\0&\text{otherwise}.\end{cases}$$
--
--   The first branch has priority. Here $P(a,d,v)=\{a,a+v,a+v+d\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 61–68; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.paramSupport_inter_twoTorsion_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_inter_twoTorsion
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem paramSupport_inter_twoTorsion_card (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    (paramSupport ((a, d), v) ∩ (twoTorsion : Finset G)).card =
      if a + a = 0 then 1 else if (a + v) + (a + v) = 0 then 2 else 0 := by sorry






































































end Finite
end Couret.STROBO2TORS
