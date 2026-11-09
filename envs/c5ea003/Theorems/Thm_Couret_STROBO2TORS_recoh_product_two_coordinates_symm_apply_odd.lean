-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_product_two_coordinates_symm_apply_odd
-- name    : Couret.STROBO2TORS.recoh_product_two_coordinates_symm_apply_odd
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:56:38.986254+00:00
-- url     : https://prove2.me/theorems/dd1f633c-303f-45e9-ac74-a849cb93b385
-- title:
--   Binary coordinate reconstruction vanishes on odd factors
-- statement:
--   Let $d\in\mathbb N$, let $q_0,\ldots,q_{d-1}$ be positive integers, and put $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$. Let a bit vector be indexed by the even cyclic coordinates, and reconstruct the corresponding element $u\in G[2]$ under the standard product binary equivalence. For every coordinate $i$ with $2\nmid q_i$,
--
--   $$u_i=0.$$
--
--   This fixes the odd-coordinate part of reconstructed torsion shifts.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicCoordinates.lean, lines 226–229; source file SHA-256 307e0b9c9a6c40440db993a517d675d2c455fc33b9a8339a890d89c7b3caf84e; theorem Couret.STROBO2TORS.recoh_product_two_coordinates_symm_apply_odd

import Aesop
import Definitions.Def_Couret_RecohCyclicCoordinates_d669b2caaf1a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCyclicHalves_383c4510168a
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
Executable binary coordinates on the two-torsion of a product of cyclic
groups.  The coordinate type is the subtype of even factors.  Encoding tests
whether a cyclic coordinate is zero; decoding uses zero on odd factors and
either zero or q / 2 on even factors.  Neither direction chooses a basis or
enumerates the ambient group or its torsion subgroup.

The definitions below are computable Lean definitions.  Their formulas are
the coordinate shift formulas of the separate Python decoder; this module
does not certify the Python runtime or a parser for its input values.
-/

namespace Couret.STROBO2TORS























variable {d : ℕ} (q : Fin d → ℕ)

















variable [∀ i, NeZero (q i)]

@[simp] theorem recoh_product_two_coordinates_symm_apply_odd
    (bits : RecohEvenCoordinate q → ZMod 2) (i : Fin d) (hi : ¬ 2 ∣ q i) :
    ((recohProductTwoCoordinates q).symm bits : (j : Fin d) → ZMod (q j)) i = 0 := by sorry


end Couret.STROBO2TORS
