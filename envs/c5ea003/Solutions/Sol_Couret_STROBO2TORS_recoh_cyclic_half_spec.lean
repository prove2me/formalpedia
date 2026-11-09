-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_half_spec
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:27.00844+00:00
-- url     : https://prove2.me/submissions/c4a1fbe2-fb56-47bc-8043-0796fabb71e7

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















theorem p2m_local_recoh_cyclic_half_spec (q : ℕ) [NeZero q] :
    RecohHalfSolverSpec (recohCyclicHalf q) :=
  ⟨recoh_cyclic_half_sound q, recoh_cyclic_half_complete q⟩









end Couret.STROBO2TORS


theorem solution : ∀ (q : Nat) [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) q],
  @Couret.STROBO2TORS.RecohHalfSolverSpec.{0} (ZMod q)
    (@Ring.toAddCommGroup.{0} (ZMod q) (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q)))
    (Couret.STROBO2TORS.recohCyclicHalf q) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_half_spec

