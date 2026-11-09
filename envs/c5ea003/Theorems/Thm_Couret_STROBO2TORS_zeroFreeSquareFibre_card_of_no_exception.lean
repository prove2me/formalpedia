-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeSquareFibre_card_of_no_exception
-- name    : Couret.STROBO2TORS.zeroFreeSquareFibre_card_of_no_exception
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:29.462879+00:00
-- url     : https://prove2.me/theorems/705880ba-0f5d-46ba-b895-2b4b93822535
-- title:
--   Zero-free square fibre count without an exceptional partner
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. If $|S|=3$ and $S$ has no exceptional partner, then
--
--   $$|\mathcal F(S)^\circ|=h-|S\cap H|.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsCardinality.lean, lines 397–404; source file SHA-256 43bb7bc977683362729a3aa2f7c214abefd9138f3283fb79ee93f0a1da784093; theorem Couret.STROBO2TORS.zeroFreeSquareFibre_card_of_no_exception

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_eq_orbit_of_no_exception
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrbit_card
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























section Finite

variable [Fintype G]

theorem zeroFreeSquareFibre_card_of_no_exception (S : Finset G) (hS : S.card = 3)
    (hne : ∀ T : Finset G, ¬ ExceptionalPartner S T) :
    (zeroFreeSquareFibre S).card = (twoTorsion : Finset G).card -
      (S ∩ (twoTorsion : Finset G)).card := by sorry





/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS
