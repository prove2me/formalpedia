-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_paramSupport_inter_twoTorsion
-- name    : Couret.STROBO2TORS.paramSupport_inter_twoTorsion
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:28.839664+00:00
-- url     : https://prove2.me/theorems/63e6efc4-d5dc-4241-a1ed-6cdfbb95c81d
-- title:
--   The two-torsion points in an exceptional parametrized support
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $P(a,d,v)=\{a,a+v,a+v+d\}$, where $2d=0$, $3v=0$ and $v\ne0$. Then
--
--   $$P(a,d,v)\cap H=\begin{cases}\{a\}&2a=0,\\\{a+v,a+v+d\}&2a\ne0\land2(a+v)=0,\\\varnothing&\text{otherwise}.\end{cases}$$
--
--   No condition $d\ne0$ is required, so the displayed pair may collapse.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsZeroFree.lean, lines 41–59; source file SHA-256 5b8447d710c8e734bf9ff71c397ece8eebe34e569041c803c65dea8a9c580a24; theorem Couret.STROBO2TORS.paramSupport_inter_twoTorsion

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
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

theorem paramSupport_inter_twoTorsion (a d v : G)
    (hd : d + d = 0) (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    paramSupport ((a, d), v) ∩ (twoTorsion : Finset G) =
      if a + a = 0 then {a}
      else if (a + v) + (a + v) = 0 then {a + v, (a + v) + d} else ∅ := by sorry








































































end Finite
end Couret.STROBO2TORS
