-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalParams_zero_card
-- name    : Couret.STROBO2TORS.exceptionalParams_zero_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:41.26042+00:00
-- url     : https://prove2.me/theorems/d1f4cf72-70ef-4fd0-8518-943e06bfe7cd
-- title:
--   Exceptional parameters whose support contains zero
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Write $P(a,d,v)=\{a,a+v,a+v+d\}$. The number of triples $(a,d,v)$ with $a\in G$, $d\in H\setminus\{0\}$, $v\in G[3]\setminus\{0\}$ and $0\in P(a,d,v)$ is
--
--   $$3(h-1)(t-1).$$
--
--   This counts parameters, not fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 167–212; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.exceptionalParams_zero_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_zero_lifts_card
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem exceptionalParams_zero_card :
    ((exceptionalParams : Finset ((G × G) × G)).filter
      (fun p => 0 ∈ paramSupport p)).card =
      3 * ((twoTorsion : Finset G).card - 1) * ((threeTorsion : Finset G).card - 1) := by sorry
















































end Finite
end Couret.STROBO2TORS
