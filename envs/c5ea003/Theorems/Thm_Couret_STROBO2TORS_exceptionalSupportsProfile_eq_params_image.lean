-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_eq_params_image
-- name    : Couret.STROBO2TORS.exceptionalSupportsProfile_eq_params_image
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:10:22.497944+00:00
-- url     : https://prove2.me/theorems/1754e689-c081-4407-98d9-daf02c5a74a5
-- title:
--   The canonical parametrization preserves two-torsion profiles
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. For $j\in\mathbb N$, the exceptional supports with exactly $j$ points in $H$ are
--
--   $$\{P(a,d,v):d\in H\setminus\{0\},\ v\in G[3]\setminus\{0\},\ |P(a,d,v)\cap H|=j\}.$$
--
--   Here $a$ ranges over $G$ and $P(a,d,v)=\{a,a+v,a+v+d\}$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsOrdinaryCount.lean, lines 239–265; source file SHA-256 36abdb7751662075f2a7470be2d1ccb52e577e35046510b06cdd5f29e66531f2; theorem Couret.STROBO2TORS.exceptionalSupportsProfile_eq_params_image

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_eq_params_image
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupportsProfile
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

























/-! ## Exceptional-support strata through their unique parameters -/

theorem exceptionalSupportsProfile_eq_params_image (j : ℕ) :
    (exceptionalSupportsProfile (G := G) j) =
      (exceptionalParamsProfile (G := G) j).image paramSupport := by sorry




/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/





end Finite
end Couret.STROBO2TORS
