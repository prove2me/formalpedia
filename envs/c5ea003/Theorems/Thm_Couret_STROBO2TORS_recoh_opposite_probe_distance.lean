-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_opposite_probe_distance
-- name    : Couret.STROBO2TORS.recoh_opposite_probe_distance
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:26.943343+00:00
-- url     : https://prove2.me/theorems/c8885359-775c-4cb3-b55b-4afb5663ca56
-- title:
--   Opposite complex values are twice their amplitude apart
-- statement:
--   For every complex z, $$\|z-(-z)\|=2\|z\|.$$ Zero is included.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohProbeStability.lean#L57-L62, lines 57–62; source file SHA-256 1d695a0d84e83ff92491e95ea472df8f9bf1059d52c5525c794d82c7f31a9800; theorem Couret.STROBO2TORS.recoh_opposite_probe_distance

import Aesop
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
Quantitative separation of character readings.  A separation statement uses
an existential coordinate; no finite maximum, nonempty bank, or nontrivial
fibre is silently assumed.  In particular singleton fibres and empty banks
are handled by the same definition.
-/

namespace Couret.STROBO2TORS



variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_opposite_probe_distance (z : ℂ) :
    ‖z - -z‖ = 2 * ‖z‖ := by sorry




variable [Fintype G]















end Couret.STROBO2TORS
