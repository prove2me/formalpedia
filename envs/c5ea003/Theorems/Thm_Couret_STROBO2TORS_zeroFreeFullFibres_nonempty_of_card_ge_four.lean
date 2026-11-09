-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_nonempty_of_card_ge_four
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_nonempty_of_card_ge_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:45.710026+00:00
-- url     : https://prove2.me/theorems/c8341cd1-2ec4-40cd-a418-656ce39df38f
-- title:
--   At least four group elements give an observed zero-free fibre
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. If $n\ge4$, $$\mathcal F^\circ\ne\varnothing.$$
--
--   This is nonemptiness of the family itself.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsMaximumCases.lean, lines 153–176; source file SHA-256 1bfee4188b3c47a03a161a1e69038d93494311971f5cf01ae94bd27298727282; theorem Couret.STROBO2TORS.zeroFreeFullFibres_nonempty_of_card_ge_four

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_tripleSupports
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeFullFibres_nonempty_of_card_ge_four
    (hn : 4 ≤ Fintype.card G) :
    (zeroFreeFullFibres : Finset (Finset (Finset G))).Nonempty := by sorry









end Finite
end Couret.STROBO2TORS
