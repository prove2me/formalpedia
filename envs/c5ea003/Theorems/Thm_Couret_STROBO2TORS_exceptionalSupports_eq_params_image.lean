-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_eq_params_image
-- name    : Couret.STROBO2TORS.exceptionalSupports_eq_params_image
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:53.206602+00:00
-- url     : https://prove2.me/theorems/b95322f9-e19e-42d9-8f42-9ceb817417f5
-- title:
--   All exceptional supports have the canonical torsion parametrization
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. With $P(a,d,v)=\{a,a+v,a+v+d\}$, the exceptional triple supports are exactly
--
--   $$\{P(a,d,v):a\in G,\ d\in H\setminus\{0\},\ v\in G[3]\setminus\{0\}\}.$$
--
--   This normalizes exceptional differences to nonzero three-torsion.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 195–209; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.exceptionalSupports_eq_params_image

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_difference_normalization
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_mem_exceptionalSupports
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem exceptionalSupports_eq_params_image :
    (exceptionalSupports : Finset (Finset G)) = exceptionalParams.image paramSupport := by sorry






































































end Finite
end Couret.STROBO2TORS
