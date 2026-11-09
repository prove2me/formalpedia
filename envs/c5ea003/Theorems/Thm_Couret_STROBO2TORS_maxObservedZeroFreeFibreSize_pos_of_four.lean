-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_pos_of_four
-- name    : Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_pos_of_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:34.297631+00:00
-- url     : https://prove2.me/theorems/7675ae30-a52a-4050-bf56-5d29de964e96
-- title:
--   Observed zero-free fibres have positive maximum from order four
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{u:2u=0\}$, $K=G[3]=\{v:3v=0\}$, $h=|H|$, $t=|K|$, $n=|G|$, and $q=|2G|$. For a triple support $S$, let $\mathcal F(S)$ be all three-element supports having the same ordered pair-sum counts, and $\mathcal O(S)=\{S+u:u\in H\}$. An ordinary fibre has size $h$; an exceptional fibre has size $2h$. For any fibre $F$, put $F^\circ=\{S\in F:0\notin S\}$. If $n\ge4$, then the maximum observed zero-free full fibre size satisfies
--
--   $$M_0(G)>0.$$
--
--   This describes the finite triple-support square fibres.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSharpMaximum.lean, lines 81–118; source file SHA-256 98c3b135eb2ea85402b9696299566a40098ac965175f8307832d30ec1e652733; theorem Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_pos_of_four

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
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

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem maxObservedZeroFreeFibreSize_pos_of_four
    (hn : 4 ≤ Fintype.card G) :
    0 < maxObservedZeroFreeFibreSize (G := G) := by sorry




























end Couret.STROBO2TORS
