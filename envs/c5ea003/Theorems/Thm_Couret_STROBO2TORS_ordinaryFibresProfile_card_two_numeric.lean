-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_two_numeric
-- name    : Couret.STROBO2TORS.ordinaryFibresProfile_card_two_numeric
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:39:49.846206+00:00
-- url     : https://prove2.me/theorems/9e21f045-f2aa-401d-88e4-2a65d8cb4bda
-- title:
--   Number of ordinary fibres in profile two
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. The ordinary profile-two fibre family has cardinality $$|\mathcal O_2|=\frac{\binom h2\binom{n-h}1-h(h-1)(t-1)}h.$$ All subtractions and division are natural-number operations.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsOrdinaryCount.lean, lines 480–491; source file SHA-256 36abdb7751662075f2a7470be2d1ccb52e577e35046510b06cdd5f29e66531f2; theorem Couret.STROBO2TORS.ordinaryFibresProfile_card_two_numeric

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupportsProfile_two_card
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_card_sub_div
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

























/-! ## Exceptional-support strata through their unique parameters -/







/-! ## Arithmetic classification of each exceptional parameter profile -/







/-! ## First explicit exceptional parameter count (one two-torsion vertex) -/






/-! ## Second exceptional support profile via an involution on raw parameters -/













/-! ## Closed numerical counts of ordinary profile-one and profile-two fibres -/

theorem ordinaryFibresProfile_card_two_numeric :
    (ordinaryFibresProfile (G := G) 2).card =
      ((twoTorsion : Finset G).card.choose 2 *
        ((Fintype.card G - (twoTorsion : Finset G).card).choose 1) -
        ((twoTorsion : Finset G).card *
          ((twoTorsion : Finset G).card - 1) *
          ((threeTorsion : Finset G).card - 1))) /
        (twoTorsion : Finset G).card := by sorry


end Finite
end Couret.STROBO2TORS
