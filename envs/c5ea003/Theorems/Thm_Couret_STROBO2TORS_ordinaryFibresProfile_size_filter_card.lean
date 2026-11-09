-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_size_filter_card
-- name    : Couret.STROBO2TORS.ordinaryFibresProfile_size_filter_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:26:26.100704+00:00
-- url     : https://prove2.me/theorems/9d5d5934-38e6-45e5-bd7f-c9069ab3e8c0
-- title:
--   Survival size in each ordinary profile
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For natural profile $j$ and size $k$, let $\mathcal O_j$ be the ordinary fibre profile and $F^\circ$ its zero-free part. Then $$|\{F\in\mathcal O_j:|F^\circ|=k\}|=\begin{cases}|\mathcal O_j|&h-j=k,\\0&h-j\ne k.\end{cases}$$ No bound on $j$ is required, and $h-j$ is truncated subtraction.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsClosedHistogram.lean, lines 71–101; source file SHA-256 584fb4d377d4eb190f2bc36949a4c3596cb755c509c4441a3e6c1c3c26d6477c; theorem Couret.STROBO2TORS.ordinaryFibresProfile_size_filter_card

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_zeroFree_card
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem ordinaryFibresProfile_size_filter_card (j k : ℕ) :
    ((ordinaryFibresProfile (G := G) j).filter
      (fun F => (withoutZero F).card = k)).card =
      if (twoTorsion : Finset G).card - j = k then
        (ordinaryFibresProfile (G := G) j).card else 0 := by sorry








end Finite
end Couret.STROBO2TORS
