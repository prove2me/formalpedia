-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryFibre_eq_orbit
-- name    : Couret.STROBO2TORS.ordinaryFibre_eq_orbit
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:01:30.920795+00:00
-- url     : https://prove2.me/theorems/3a06f24b-d185-443c-b41c-1546f3111bc9
-- title:
--   Every ordinary fibre is a torsion orbit
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. For any ordinary fibre $F$,
--
--   $$\exists S\subseteq G:\quad |S|=3,\qquad F=\mathcal O(S).$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsOrdinaryProfiles.lean, lines 57–71; source file SHA-256 8256c216c05e31a8b906a7995786f22d09fd15ab7049e1a9f6c0763f1c34c435; theorem Couret.STROBO2TORS.ordinaryFibre_eq_orbit

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_zeroFree_size
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_two_h_iff_exception
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_eq_orbit_of_no_exception
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem ordinaryFibre_eq_orbit (F : Finset (Finset G))
    (hF : F ∈ (ordinaryFibres : Finset (Finset (Finset G)))) :
    ∃ S : Finset G, S.card = 3 ∧ F = torsionOrbit S := by sorry








end Finite
end Couret.STROBO2TORS
