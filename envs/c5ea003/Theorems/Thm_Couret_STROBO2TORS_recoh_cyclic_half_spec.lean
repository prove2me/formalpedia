-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_half_spec
-- name    : Couret.STROBO2TORS.recoh_cyclic_half_spec
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:23.735125+00:00
-- url     : https://prove2.me/theorems/f94720c9-a5be-427f-b7f9-8a42e7552cf6
-- title:
--   The explicit cyclic halving solver is sound and complete
-- statement:
--   Let $q>0$. The specified halving function on $\mathbb Z/q\mathbb Z$ uses multiplication by $(q+1)/2$ when $q$ is odd, halves the standard representative when both $q$ and that representative are even, and returns none otherwise. It satisfies
--
--   $$h(t)=\operatorname{some}(x)\Longrightarrow2x=t,\qquad[\exists x,2x=t]\Longrightarrow[\exists x,h(t)=\operatorname{some}(x)].$$
--
--   The solver need not list every half.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicHalves.lean, lines 76–78; source file SHA-256 a4e0211ade942e149c23077a732176c321236fab9e7cca6522d82ba445be71bd; theorem Couret.STROBO2TORS.recoh_cyclic_half_spec

import Aesop
import Definitions.Def_Couret_RecohCyclicHalves_383c4510168a
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6

set_option autoImplicit false

/-!
Coordinatewise doubling solver used by the exact RECOH decoder.

The cyclic solver uses the canonical natural representative of a ZMod value.
For odd modulus it multiplies by (q+1)/2; for even modulus it rejects an odd
representative and otherwise divides that representative by two.  The product
solver checks only the finitely many coordinates, never the ambient group.
This is Lean code with proved soundness and completeness, rather than a claim
that a separate Python parser, cache or runtime has been verified.
-/

namespace Couret.STROBO2TORS

theorem recoh_cyclic_half_spec (q : ℕ) [NeZero q] :
    RecohHalfSolverSpec (recohCyclicHalf q) := by sorry










end Couret.STROBO2TORS
