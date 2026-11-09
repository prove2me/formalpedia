-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_sub_div
-- name    : Couret.STROBO2TORS.ordinaryFibresProfile_card_sub_div
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:26:35.944807+00:00
-- url     : https://prove2.me/theorems/b4a75dbf-f65d-4c4c-a16a-864d2bd3cb7a
-- title:
--   Ordinary fibre count at a fixed torsion profile
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. For $0\le j\le3$, let $\mathcal U_j$ be ordinary fibres containing a support $S$ with $|S\cap H|=j$, and let $E_j$ be exceptional supports of that profile. Then
--
--   $$|\mathcal U_j|=\frac{\binom hj\binom{n-h}{3-j}-|E_j|}{h}.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsOrdinaryCount.lean, lines 178–201; source file SHA-256 36abdb7751662075f2a7470be2d1ccb52e577e35046510b06cdd5f29e66531f2; theorem Couret.STROBO2TORS.ordinaryFibresProfile_card_sub_div

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinarySupportsProfile_card_eq_mul
import Theorems.Thm_Couret_STROBO2TORS_tripleSupportsProfile_card
import Theorems.Thm_Couret_STROBO2TORS_tripleSupportsProfile_ordinary_exceptional
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem ordinaryFibresProfile_card_sub_div (j : ℕ) (hj : j ≤ 3) :
    (ordinaryFibresProfile (G := G) j).card =
      (((twoTorsion : Finset G).card.choose j) *
        ((Fintype.card G - (twoTorsion : Finset G).card).choose (3 - j)) -
        (exceptionalSupportsProfile (G := G) j).card) /
        (twoTorsion : Finset G).card := by sorry






/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS
