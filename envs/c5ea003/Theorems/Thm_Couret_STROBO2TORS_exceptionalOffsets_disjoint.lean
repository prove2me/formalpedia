-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalOffsets_disjoint
-- name    : Couret.STROBO2TORS.exceptionalOffsets_disjoint
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:34.302008+00:00
-- url     : https://prove2.me/theorems/43ffb9b3-a64a-4d0f-8c28-a6b600848f13
-- title:
--   A nonzero half-turn separates the nonzero three-torsion offsets
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. For $d\in H\setminus\{0\}$,
--
--   $$(G[3]\setminus\{0\})\cap((G[3]\setminus\{0\})+d)=\varnothing.$$
--
--   This justifies adding the two offset counts without overlap.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 543–559; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.exceptionalOffsets_disjoint

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

theorem exceptionalOffsets_disjoint (d : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) :
    Disjoint (nonzeroThreeTorsion : Finset G)
      ((nonzeroThreeTorsion : Finset G).image (fun w => w + d)) := by sorry




end Finite
end Couret.STROBO2TORS
