-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_support_card_and_zero
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_support_card_and_zero
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:31.435727+00:00
-- url     : https://prove2.me/theorems/e51eb451-9e14-4780-9420-e806a19ff84c
-- title:
--   Supports in an observed zero-free fibre are zero-free triples
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. For $F\in\mathcal F^\circ$ and $S\in F$, $$|S|=3,\qquad0\notin S.$$
--
--   This unpacks the support constraints after fibre restriction.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsMaximumCases.lean, lines 198–215; source file SHA-256 1bfee4188b3c47a03a161a1e69038d93494311971f5cf01ae94bd27298727282; theorem Couret.STROBO2TORS.zeroFreeFullFibres_support_card_and_zero

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

theorem zeroFreeFullFibres_support_card_and_zero
    (F : Finset (Finset G))
    (hF : F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))))
    (S : Finset G) (hS : S ∈ F) :
    S.card = 3 ∧ 0 ∉ S := by sorry





end Finite
end Couret.STROBO2TORS
