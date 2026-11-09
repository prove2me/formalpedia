-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_numeric
-- name    : Couret.STROBO2TORS.exceptionalFibres_card_numeric
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:18:25.671788+00:00
-- url     : https://prove2.me/theorems/e4c4e45c-7415-40d4-a96c-2f7ec5447cde
-- title:
--   Number of exceptional square fibres
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. The exceptional fibre family satisfies $$|\mathcal E|=(n/h)(h-1)((t-1)/2).$$ Division is natural-number division; no lower bound on the torsion ranks is assumed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsEnumeration.lean, lines 443–447; source file SHA-256 c5994a3923540d425df056cc4b93ff327cc2020eebfa6a424ceca158f26761bc; theorem Couret.STROBO2TORS.exceptionalFibres_card_numeric

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_doublingImages_card_division
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_product
import Theorems.Thm_Couret_STROBO2TORS_threeSignPairs_card_division
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]

theorem exceptionalFibres_card_numeric :
    (exceptionalFibres : Finset (Finset (Finset G))).card =
      (Fintype.card G / (twoTorsion : Finset G).card) * ((twoTorsion : Finset G).card - 1) *
        (((threeTorsion : Finset G).card - 1) / 2) := by sorry


























end Finite
end Couret.STROBO2TORS
