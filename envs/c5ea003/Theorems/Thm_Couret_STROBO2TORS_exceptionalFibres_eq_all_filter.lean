-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_eq_all_filter
-- name    : Couret.STROBO2TORS.exceptionalFibres_eq_all_filter
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:48:16.711209+00:00
-- url     : https://prove2.me/theorems/e828f4c6-cd4f-4523-8659-7e5df9152457
-- title:
--   Exceptional fibres are precisely the full fibres of size twice the two-torsion
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $\mathcal F$ be all full triple square fibres and $\mathcal E$ the exceptional fibres obtained from exceptional supports. Then
--
--   $$\mathcal E=\{F\in\mathcal F:|F|=2h\}.$$
--
--   This identifies the geometric exceptional construction by its cardinality.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 465–479; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.exceptionalFibres_eq_all_filter

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem exceptionalFibres_eq_all_filter :
    (exceptionalFibres : Finset (Finset (Finset G))) =
      allSquareFibres.filter (fun F => F.card = 2 * (twoTorsion : Finset G).card) := by sorry














end Finite
end Couret.STROBO2TORS
