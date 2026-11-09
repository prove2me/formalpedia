-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_paramSupport_both_zero_iff
-- name    : Couret.STROBO2TORS.paramSupport_both_zero_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:41.967263+00:00
-- url     : https://prove2.me/theorems/dd2c2900-a459-4ebd-99d0-5ff1394ede11
-- title:
--   Both reflected supports contain zero only at the zero anchor and shift
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. Let $P(a,d,v)=\{a,a+v,a+v+d\}$, with $2d=0$, $3v=0$, $v\ne0$, and $2u=0$. Then
--
--   $$[0\in P(a,d,v)\land0\in P(a,d,-v)+u]\iff[a=0\land u=0].$$
--
--   The direction $d$ is allowed to be zero.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsPairCount.lean, lines 81–133; source file SHA-256 f6c997c461f640aab1856a21d5adfad3e6bfdbf876e67e5783b3ba87b26827cd; theorem Couret.STROBO2TORS.paramSupport_both_zero_iff

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_double_eq_neg
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]

theorem paramSupport_both_zero_iff (a d v u : G)
    (hd : d+d=0) (hv : (v+v)+v=0) (hv0 : v ≠ 0) (hu : u+u=0) :
    (0 ∈ paramSupport ((a,d),v) ∧
      0 ∈ translateSupport (paramSupport ((a,d),-v)) u) ↔ a=0 ∧ u=0 := by sorry



























attribute [local instance] Classical.propDecidable





























end Finite
end Couret.STROBO2TORS
