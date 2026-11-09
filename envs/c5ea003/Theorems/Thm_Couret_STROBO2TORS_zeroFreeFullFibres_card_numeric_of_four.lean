-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_numeric_of_four
-- name    : Couret.STROBO2TORS.zeroFreeFullFibres_card_numeric_of_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:58:05.44242+00:00
-- url     : https://prove2.me/theorems/e3e2a196-3bc5-4cb7-ab92-29f2fac3324d
-- title:
--   Number of observed zero-free fibres when two-torsion has size at least four
-- statement:
--   Let $G$ be a finite abelian group. Write $H=G[2]=\{x:2x=0\}$, $K=G[3]=\{x:3x=0\}$, $n=|G|$, $h=|H|$, and $t=|K|$. For a finite support $S$, let $Q_S(z)$ count ordered pairs in $S^2$ with sum $z$, let $F(S)$ be its fibre among three-element supports, and put $S+u=\{x+u:x\in S\}$. If $h\ge4$, then $$|\mathcal F^\circ|=\binom n3/h-(n/h)(h-1)((t-1)/2).$$
--
--   The family consists of nonempty zero-free parts of full square fibres, with repetitions removed; arithmetic is in the natural numbers.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/Strobo2TorsSurvivalCounts.lean, lines 103–113; source file SHA-256 eb83aad035d165b4936c91ba5553308053fd7af14d21de79283c272887a1f571; theorem Couret.STROBO2TORS.zeroFreeFullFibres_card_numeric_of_four

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_card_numeric
import Theorems.Thm_Couret_STROBO2TORS_tripleSupports_weighted_card
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_pos
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_card_of_four
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

theorem zeroFreeFullFibres_card_numeric_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card) :
    (zeroFreeFullFibres : Finset (Finset (Finset G))).card =
      (Fintype.card G).choose 3 / (twoTorsion : Finset G).card -
        ((Fintype.card G / (twoTorsion : Finset G).card) *
          ((twoTorsion : Finset G).card - 1) *
          (((threeTorsion : Finset G).card - 1) / 2)) := by sorry


end Finite
end Couret.STROBO2TORS
