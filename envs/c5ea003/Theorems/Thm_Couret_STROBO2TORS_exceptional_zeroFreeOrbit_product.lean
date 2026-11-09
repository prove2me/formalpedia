-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptional_zeroFreeOrbit_product
-- name    : Couret.STROBO2TORS.exceptional_zeroFreeOrbit_product
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:51:54.806867+00:00
-- url     : https://prove2.me/theorems/a5a176f5-eeb1-483b-8496-f29f2bf652b8
-- title:
--   Product of zero-free orbit sizes for an exceptional pair
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Put $P(a,d,v)=\{a,a+v,a+v+d\}$. Let $d\in H\setminus\{0\}$, $v\in K\setminus\{0\}$ and $a\in G$. Put $Z(S)=|\{T\in\mathcal O(S):0\notin T\}|$. Then
--
--   $$Z(P(a,d,v))Z(P(a,d,-v))=\begin{cases}(h-1)^2,&2a=0,\\h(h-2),&2a\ne0\text{ and }(2(a+v)=0\text{ or }2(a-v)=0),\\h^2,&\text{otherwise}.\end{cases}$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsPairCount.lean, lines 223–251; source file SHA-256 f6c997c461f640aab1856a21d5adfad3e6bfdbf876e67e5783b3ba87b26827cd; theorem Couret.STROBO2TORS.exceptional_zeroFreeOrbit_product

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
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_card
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_inter_twoTorsion_card
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_double_eq_neg
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrbit_card
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]

theorem exceptional_zeroFreeOrbit_product (a d v : G)
    (hd : d+d=0) (hd0 : d ≠ 0) (hv : (v+v)+v=0) (hv0 : v ≠ 0) :
    (zeroFreeOrbit (paramSupport ((a,d),v))).card *
      (zeroFreeOrbit (paramSupport ((a,d),-v))).card =
      if a+a=0 then ((twoTorsion : Finset G).card-1)^2
      else if (a+v)+(a+v)=0 ∨ (a + -v)+(a + -v)=0 then
        (twoTorsion : Finset G).card * ((twoTorsion : Finset G).card-2)
      else (twoTorsion : Finset G).card^2 := by sorry

















attribute [local instance] Classical.propDecidable





























end Finite
end Couret.STROBO2TORS
