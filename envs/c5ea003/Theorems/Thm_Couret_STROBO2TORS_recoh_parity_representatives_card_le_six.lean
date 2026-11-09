-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_parity_representatives_card_le_six
-- name    : Couret.STROBO2TORS.recoh_parity_representatives_card_le_six
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:42:56.939321+00:00
-- url     : https://prove2.me/theorems/4faef0ad-185e-4329-bd59-6766c64c883f
-- title:
--   Parity generation produces at most six representatives
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a support $S$, $P_\chi(S)=\sum_{s\in S}\chi(s)$, and $F(S)=\{T:|T|=3,R_T=R_S\}$. Put $H=G[2]$. For arbitrary finite $U\subseteq G$, arbitrary $R:G\to\mathbb N$, and arbitrary partial halving function $h$,
--
--   $$|\operatorname{ParityRepresentatives}(U,R,h)|\le6.$$
--
--   Soundness, completeness and support coverage are not hypotheses for this cardinality bound.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohParityGenerator.lean, lines 501–505; source file SHA-256 c0de570c34b3a0044573486512e463147ffae9acc9eff636411cbf33711eee31; theorem Couret.STROBO2TORS.recoh_parity_representatives_card_le_six

import Aesop
import Definitions.Def_Couret_RecohParityGenerator_deb90a4bb68d
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a

set_option autoImplicit false
set_option maxRecDepth 2000

/-!
The compact parity generator for three-point ordered squares.

All executable searches are over the supplied finite square support U,
one residual set, or its two-element subsets. There is no `Fintype G`
assumption on the generator. The final exact-square test is performed after
the chosen translation; the translation identity below relates it to the
normalized square test used by Python v0.2.

This module proves a mathematical coverage contract for these Lean
definitions. It does not provide a semantics for Python, JSON or its runtime.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_parity_representatives_card_le_six
    (U : Finset G) (R : G → ℕ) (half : G → Option G) :
    (recohParityRepresentatives U R half).card ≤ 6 := by sorry


end Couret.STROBO2TORS
