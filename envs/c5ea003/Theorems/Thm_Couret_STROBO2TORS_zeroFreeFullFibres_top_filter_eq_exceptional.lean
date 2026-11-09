-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_top_filter_eq_exceptional
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_top_filter_eq_exceptional
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:59.266412+00:00
-- url     : https://prove2.me/theorems/cf64954f-b22d-471b-8443-0b4bf4116e27
-- title:
--   Full-size observed zero-free fibres are exceptional
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. Let $\mathcal Z$ be the observed nonempty zero-free full fibres and $\mathcal E^\circ$ the zero-free images of exceptional fibres. Then
--
--   $$\{R\in\mathcal Z:|R|=2h\}=\{R\in\mathcal E^\circ:|R|=2h\}.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsMaximum.lean, lines 46–69; source file SHA-256 27aa6c02d9eb6f3a53aeb5b66640fa36aa2dc35441d6179ac79eb791d573ade2; theorem Couret.STROBO2TORS.zeroFreeFullFibres_top_filter_eq_exceptional

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_card_le_twoTorsion
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem zeroFreeFullFibres_top_filter_eq_exceptional :
    ((zeroFreeFullFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = 2 * (twoTorsion : Finset G).card)) =
    ((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
      (fun R => R.card = 2 * (twoTorsion : Finset G).card)) := by sorry




end Finite
end Couret.STROBO2TORS
