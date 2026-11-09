-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports
-- name    : Couret.STROBO2TORS.mem_exceptionalSupports
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:15.193202+00:00
-- url     : https://prove2.me/theorems/46deef1d-83c5-4795-96cf-b24517ef4ece
-- title:
--   Exceptional supports are triples with an exceptional partner
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. A finite support $S$ is exceptional exactly when $|S|=3$ and there exist $a,b,d,u\in G$ with $2d=0$, $d\ne0$, $2a\ne2b$, $2u=0$, $3(b-a)\in\{0,d\}$, $S=\{a,b,b+d\}$ and an exceptional partner $T=\{a,2b-a,2b-a+d\}+u$. In symbols,
--
--   $$S\in E\iff|S|=3\land\exists T,\operatorname{ExceptionalPartner}(S,T).$$
--
--   This identifies the finite enumeration with the partner relation.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 152–160; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.mem_exceptionalSupports

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_two_h_iff_exception
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem mem_exceptionalSupports (S : Finset G) :
    S ∈ exceptionalSupports ↔ S.card = 3 ∧ ∃ T : Finset G, ExceptionalPartner S T := by sorry












































































end Finite
end Couret.STROBO2TORS
