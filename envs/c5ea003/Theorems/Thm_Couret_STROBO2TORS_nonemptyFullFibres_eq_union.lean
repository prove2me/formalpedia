-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_nonemptyFullFibres_eq_union
-- name    : Couret.STROBO2TORS.nonemptyFullFibres_eq_union
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:15:32.296794+00:00
-- url     : https://prove2.me/theorems/dd5c7985-9f75-48d8-bea5-fce7aad8349a
-- title:
--   Full fibres surviving removal of zero split into two branches
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $\mathcal F_+$ be the full fibres $F$ with $F^*\ne\varnothing$, and let $\mathcal O_+$ be the ordinary ones with that property. Then
--
--   $$\mathcal F_+=\mathcal O_+\cup\mathcal E.$$
--
--   Every exceptional fibre survives, whereas empty ordinary reductions are removed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFreeAll.lean, lines 89–115; source file SHA-256 57e0e6b2919f605519cfad328e82e56477cae03c002010fa3c4fd6a8c218120b; theorem Couret.STROBO2TORS.nonemptyFullFibres_eq_union

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_withoutZero_card_ge_two
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem nonemptyFullFibres_eq_union :
    (nonemptyFullFibres : Finset (Finset (Finset G))) =
      ordinaryNonemptyFibres ∪ exceptionalFibres := by sorry




















/-! ## Profile invariance under two-torsion translation

These statements are prerequisites for counting the ordinary fibres by
their number j of support elements in the two-torsion subgroup. They do
not by themselves prove the closed binomial formula. -/















/-! ## Binomial enumeration of profile supports -/













end Finite
end Couret.STROBO2TORS
