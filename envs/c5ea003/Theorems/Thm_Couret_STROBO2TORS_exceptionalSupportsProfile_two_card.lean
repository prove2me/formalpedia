-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_two_card
-- name    : Couret.STROBO2TORS.exceptionalSupportsProfile_two_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:49.96661+00:00
-- url     : https://prove2.me/theorems/0a4ab600-dbe3-4c39-a446-62269f5ae38b
-- title:
--   Number of exceptional supports with two two-torsion points
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. The number of exceptional three-element supports $S$ with $|S\cap H|=2$ is
--
--   $$h(h-1)(t-1).$$
--
--   The profile restriction is exact.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsOrdinaryCount.lean, lines 439–463; source file SHA-256 36abdb7751662075f2a7470be2d1ccb52e577e35046510b06cdd5f29e66531f2; theorem Couret.STROBO2TORS.exceptionalSupportsProfile_two_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_eq_params_image
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_one_card
import Theorems.Thm_Couret_STROBO2TORS_exceptional_param_genuine
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_injective_on_exceptionalParams
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_inter_twoTorsion_card
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

























/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/

theorem exceptionalSupportsProfile_two_card :
    (exceptionalSupportsProfile (G := G) 2).card =
      (twoTorsion : Finset G).card *
        ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1) := by sorry


/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS
