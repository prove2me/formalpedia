-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinarySupportsProfile_card_eq_mul
-- name    : Couret.STROBO2TORS.ordinarySupportsProfile_card_eq_mul
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:00.450921+00:00
-- url     : https://prove2.me/theorems/572b3e6f-c651-4d48-9155-6826aa02fb80
-- title:
--   Ordinary support counts equal fibre counts times two-torsion size
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. For each $j\in\mathbb N$, let $S_j$ be the ordinary triple supports with exactly $j$ elements in $H$, and $\mathcal O_j$ the ordinary fibres with that profile. Then
--
--   $$|S_j|=h|\mathcal O_j|.$$
--
--   This is a profile-preserving passage from supports to fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsOrdinaryCount.lean, lines 104–126; source file SHA-256 36abdb7751662075f2a7470be2d1ccb52e577e35046510b06cdd5f29e66531f2; theorem Couret.STROBO2TORS.ordinarySupportsProfile_card_eq_mul

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinarySupportsProfile_image
import Theorems.Thm_Couret_STROBO2TORS_ordinarySupportsProfile_preimage
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem ordinarySupportsProfile_card_eq_mul (j : ℕ) :
    (ordinarySupportsProfile (G := G) j).card =
      (twoTorsion : Finset G).card *
        (ordinaryFibresProfile (G := G) j).card := by sorry
















/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS
