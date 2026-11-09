-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_maxObservedZeroFreeFibreSize_eq_zero_of_card_lt_four
-- name    : Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_eq_zero_of_card_lt_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:43.864195+00:00
-- url     : https://prove2.me/theorems/28449ec4-2c12-444a-a29c-d31fe3aa5d61
-- title:
--   No positive zero-free maximum below four group elements
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. If $n<4$, the defined maximum observed zero-free fibre size is $$M(G)=0.$$
--
--   The maximum convention therefore includes empty observed families.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSharpMaximum.lean, lines 120–156; source file SHA-256 98c3b135eb2ea85402b9696299566a40098ac965175f8307832d30ec1e652733; theorem Couret.STROBO2TORS.maxObservedZeroFreeFibreSize_eq_zero_of_card_lt_four

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_squareFibre_member
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem maxObservedZeroFreeFibreSize_eq_zero_of_card_lt_four
    (hn : Fintype.card G < 4) :
    maxObservedZeroFreeFibreSize (G := G) = 0 := by sorry


























end Couret.STROBO2TORS
