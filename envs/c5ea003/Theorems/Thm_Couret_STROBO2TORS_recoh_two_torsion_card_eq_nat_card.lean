-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_card_eq_nat_card
-- name    : Couret.STROBO2TORS.recoh_two_torsion_card_eq_nat_card
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:06.126104+00:00
-- url     : https://prove2.me/theorems/fb69a266-26f5-4898-b69e-c2f6412a5096
-- title:
--   The finite-set and subgroup two-torsion cardinalities agree
-- statement:
--   Let $G$ be a finite abelian group. The filtered finite set $H=\{u\in G:2u=0\}$ and the torsion subgroup $G[2]$ have the same cardinality:
--
--   $$|H|=\operatorname{card}(G[2]).$$
--
--   This aligns the two representations used by counting and character constructions.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreLower.lean, lines 18–37; source file SHA-256 25b4421c1b3f5d0b165e92effb04f9cec71c9084d67a55ff431cc52c867772ef; theorem Couret.STROBO2TORS.recoh_two_torsion_card_eq_nat_card

import Aesop
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

/-!
Information lower bound for a bank chosen after the labelled ordered
square is known.  Reconstructing means actual injectivity on the existing
finite square fibre.  The result applies to arbitrary complex characters,
including probes which vanish on that fibre.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem recoh_two_torsion_card_eq_nat_card :
    (twoTorsion : Finset G).card =
      Nat.card (recohTorsionSubgroup (G := G) 2) := by sorry








end Couret.STROBO2TORS
