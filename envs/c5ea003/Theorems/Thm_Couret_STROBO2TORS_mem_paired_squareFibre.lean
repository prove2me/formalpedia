-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_mem_paired_squareFibre
-- name    : Couret.STROBO2TORS.mem_paired_squareFibre
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:41:12.116116+00:00
-- url     : https://prove2.me/theorems/7658ea01-e4c9-43a6-8a82-1a3ee346e6ca
-- title:
--   Membership in the square fibre of a paired triple
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $a,b,d\in G$ satisfy $2d=0$, $d\ne0$, $2a\ne2b$. Put $S=\{a,b,b+d\}$ and $R=\{a,2b-a,2b-a+d\}$. For every finite support $T$,
--
--   $$T\in\mathcal F(S)\Longleftrightarrow T\in\mathcal O(S)\ \text{or}\ \bigl(3(b-a)\in\{0,d\}\text{ and }T\in\mathcal O(R)\bigr).$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 240–270; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.mem_paired_squareFibre

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_paired_partner_fixed_source
import Theorems.Thm_Couret_STROBO2TORS_paired_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_reflected_orderedSquare_eq
import Theorems.Thm_Couret_STROBO2TORS_reflected_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]

theorem mem_paired_squareFibre (a b d : G)
    (hd : d + d = 0) (hd0 : d ≠ 0) (hab : a + a ≠ b + b) (T : Finset G) :
    T ∈ squareFibre ({a, b, b + d} : Finset G) ↔
      T ∈ torsionOrbit ({a, b, b + d} : Finset G) ∨
      ((((b - a) + (b - a)) + (b - a) = 0 ∨
         ((b - a) + (b - a)) + (b - a) = d) ∧
        T ∈ torsionOrbit ({a, b + b - a, (b + b - a) + d} : Finset G)) := by sorry

























/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS
