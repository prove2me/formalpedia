-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_paired_squareFibre_eq
-- name    : Couret.STROBO2TORS.paired_squareFibre_eq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:45:13.90216+00:00
-- url     : https://prove2.me/theorems/fd6d87af-a2c4-4936-96ef-26d678daffc1
-- title:
--   The complete square fibre of a paired triple
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. For $a,b,d\in G$ with $d\ne0$, $2d=0$ and $2a\ne2b$, put $S=\{a,b,b+d\}$ and $T=\{a,2b-a,2b-a+d\}$. Then
--
--   $$F(S)=\begin{cases}O(S)\cup O(T)&3(b-a)\in\{0,d\},\\O(S)&\text{otherwise}.\end{cases}$$
--
--   This includes every three-element support with the same ordered square.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 272–282; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.paired_squareFibre_eq

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_paired_squareFibre
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]

theorem paired_squareFibre_eq (a b d : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) (hab : a + a ≠ b + b) :
    squareFibre ({a, b, b + d} : Finset G) =
      if ((b - a) + (b - a)) + (b - a) = 0 ∨
        ((b - a) + (b - a)) + (b - a) = d then
        torsionOrbit ({a, b, b + d} : Finset G) ∪
          torsionOrbit ({a, b + b - a, (b + b - a) + d} : Finset G)
      else torsionOrbit ({a, b, b + d} : Finset G) := by sorry























/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS
