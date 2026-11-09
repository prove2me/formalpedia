-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_top_size_nonempty_iff
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_top_size_nonempty_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:33.396386+00:00
-- url     : https://prove2.me/theorems/a7b13dab-4324-485f-95e3-fac09d8eeb03
-- title:
--   Exact criterion for attaining the largest zero-free fibre size
-- statement:
--   Let $G$ be a finite abelian group, $N=|G|$, $H=G[2]=\{u:2u=0\}$, $h=|H|$, $t=|G[3]|$, and $D=|2G|$. Write $R_S(z)$ for the ordered pair-sum count of a finite support $S$, $F(S)=\{T:|T|=3,R_T=R_S\}$, $O(S)=\{S+u:u\in H\}$, and $F^*=\{S\in F:0\notin S\}$. Ordinary full fibres have size $h$, exceptional full fibres size $2h$. All displayed subtractions are natural subtraction, truncated at zero, and all quotients are integer division. There exists a nonempty zero-free full triple square fibre of size $2h$ exactly when
--
--   $$D>3,\qquad h>1,\qquad t>1.$$
--
--   All three conditions are necessary.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsMaximum.lean, lines 71–81; source file SHA-256 27aa6c02d9eb6f3a53aeb5b66640fa36aa2dc35441d6179ac79eb791d573ade2; theorem Couret.STROBO2TORS.zeroFreeFullFibres_top_size_nonempty_iff

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_full_nonempty_iff
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_top_filter_eq_exceptional
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem zeroFreeFullFibres_top_size_nonempty_iff :
    ((zeroFreeFullFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = 2 * (twoTorsion : Finset G).card)).Nonempty ↔
      3 < (doublingImages : Finset G).card ∧
      1 < (twoTorsion : Finset G).card ∧
      1 < (threeTorsion : Finset G).card := by sorry


end Finite
end Couret.STROBO2TORS
