-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_product_two_coordinates_eq_zero_iff
-- name    : Couret.STROBO2TORS.recoh_product_two_coordinates_eq_zero_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:49:30.259195+00:00
-- url     : https://prove2.me/theorems/a8c4a459-2824-47a9-9396-04212fac6920
-- title:
--   A binary torsion coordinate vanishes exactly with its cyclic coordinate
-- statement:
--   Let $d\ge0$, let $q_i$ be nonzero natural numbers for $i<d$, and set $A=\prod_{i<d}\mathbb Z/q_i$. A primary coordinate for a prime $p$ is an index with $p\mid q_i$. For supports in $A$, write $Q_S$ for ordered-sum counts, $P_\chi(S)=\sum_{x\in S}\chi(x)$, and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a character bank $B$. For $u\in A[2]$ and an even-modulus coordinate $i$, $$e(u)_i=0\iff u_i=0,$$ where $e$ is the defined product two-torsion coordinate map. This identifies its zero bits exactly.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicCoordinates.lean, lines 213–218; source file SHA-256 307e0b9c9a6c40440db993a517d675d2c455fc33b9a8339a890d89c7b3caf84e; theorem Couret.STROBO2TORS.recoh_product_two_coordinates_eq_zero_iff

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

@[simp] theorem recoh_product_two_coordinates_eq_zero_iff
    (u : recohTorsionSubgroup (G := (i : Fin d) → ZMod (q i)) 2)
    (i : RecohEvenCoordinate q) :
    recohProductTwoCoordinates q u i = 0 ↔
      (u : (j : Fin d) → ZMod (q j)) i.val = 0 := by sorry






end Couret.STROBO2TORS
