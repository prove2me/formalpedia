-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalOffsets
-- name    : Couret.STROBO2TORS.mem_exceptionalOffsets
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:45.282511+00:00
-- url     : https://prove2.me/theorems/dc631f88-d475-413d-a6d0-9240ce006cbf
-- title:
--   Membership in the exceptional-offset union
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. For arbitrary $v,d\in G$, let $E_d=(G[3]\setminus\{0\})\cup((G[3]\setminus\{0\})+d)$. Then
--
--   $$v\in E_d\iff\exists w\ne0,\quad3w=0\land(v=w\lor v=w+d).$$
--
--   This membership statement imposes no torsion condition on $d$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 484–502; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.mem_exceptionalOffsets

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]


















































/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/

theorem mem_exceptionalOffsets (v d : G) :
    v ∈ exceptionalOffsets d ↔
      ∃ w : G, (w + w) + w = 0 ∧ w ≠ 0 ∧
        (v = w ∨ v = w + d) := by sorry










end Finite
end Couret.STROBO2TORS
