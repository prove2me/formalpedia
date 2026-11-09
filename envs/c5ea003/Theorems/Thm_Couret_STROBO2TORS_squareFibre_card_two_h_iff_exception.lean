-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_two_h_iff_exception
-- name    : Couret.STROBO2TORS.squareFibre_card_two_h_iff_exception
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:51:55.683245+00:00
-- url     : https://prove2.me/theorems/4df7b9f0-0264-430d-82b0-9061903da3e7
-- title:
--   Double-sized fibres characterize exceptional partners
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For a three-element support $S$, $$|F(S)|=2h\iff\exists T,\ E(S,T).$$
--
--   This relates the numerical fibre size to exceptional partner existence. The exceptional relation $E(S,T)$ means that for some $a,b,d,u$ with $2d=2u=0$, $d\ne0$, $2a\ne2b$, and $3(b-a)\in\{0,d\}$, one has $S=\{a,b,b+d\}$ and $T=\{a,2b-a,2b-a+d\}+u$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 332–348; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.squareFibre_card_two_h_iff_exception

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_paired_orbits_disjoint
import Theorems.Thm_Couret_STROBO2TORS_paired_squareFibre_eq
import Theorems.Thm_Couret_STROBO2TORS_paired_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_reflected_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_eq_orbit_of_no_exception
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]

theorem squareFibre_card_two_h_iff_exception (S : Finset G) (hS : S.card = 3) :
    (squareFibre S).card = 2 * (twoTorsion : Finset G).card ↔
      ∃ T : Finset G, ExceptionalPartner S T := by sorry











/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS
