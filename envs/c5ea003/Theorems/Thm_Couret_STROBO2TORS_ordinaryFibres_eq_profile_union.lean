-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_eq_profile_union
-- name    : Couret.STROBO2TORS.ordinaryFibres_eq_profile_union
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:26:06.358909+00:00
-- url     : https://prove2.me/theorems/2aab6204-e6e7-49fa-a45f-82779d6eb7fb
-- title:
--   Four profiles exhaust ordinary fibres
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. The ordinary fibre family satisfies $$\mathcal O=\mathcal O_0\cup\mathcal O_1\cup\mathcal O_2\cup\mathcal O_3.$$
--
--   The index is the number of support points in the two-torsion subgroup.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsClosedHistogram.lean, lines 25–69; source file SHA-256 584fb4d377d4eb190f2bc36949a4c3596cb755c509c4441a3e6c1c3c26d6477c; theorem Couret.STROBO2TORS.ordinaryFibres_eq_profile_union

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_zeroFree_size
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem ordinaryFibres_eq_profile_union :
    (ordinaryFibres : Finset (Finset (Finset G))) =
      ordinaryFibresProfile 0 ∪
        (ordinaryFibresProfile 1 ∪
          (ordinaryFibresProfile 2 ∪ ordinaryFibresProfile 3)) := by sorry










end Finite
end Couret.STROBO2TORS
