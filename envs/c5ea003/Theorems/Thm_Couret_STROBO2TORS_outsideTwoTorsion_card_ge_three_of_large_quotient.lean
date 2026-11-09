-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_outsideTwoTorsion_card_ge_three_of_large_quotient
-- name    : Couret.STROBO2TORS.outsideTwoTorsion_card_ge_three_of_large_quotient
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:46.855546+00:00
-- url     : https://prove2.me/theorems/37d68064-f8ae-4692-92fc-902853d18c56
-- title:
--   At least three elements lie outside two-torsion
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. If $h>1$, the doubling image has more than one element, and $n>4$, then $$|G\setminus H|\ge3.$$ All three strict hypotheses are retained.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSharpMaximum.lean, lines 363–386; source file SHA-256 98c3b135eb2ea85402b9696299566a40098ac965175f8307832d30ec1e652733; theorem Couret.STROBO2TORS.outsideTwoTorsion_card_ge_three_of_large_quotient

import Aesop
import Definitions.Def_Couret_Strobo2TorsSharpMaximum_bfb30eac9be9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_group_card_eq_h_mul_doublingImages
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem outsideTwoTorsion_card_ge_three_of_large_quotient
    (hh : 1 < (twoTorsion : Finset G).card)
    (hq : 1 < (doublingImages : Finset G).card)
    (hn : 4 < Fintype.card G) :
    3 ≤ ((Finset.univ : Finset G) \ (twoTorsion : Finset G)).card := by sorry







end Couret.STROBO2TORS
