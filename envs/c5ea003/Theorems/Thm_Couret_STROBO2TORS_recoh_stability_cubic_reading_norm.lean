-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_stability_cubic_reading_norm
-- name    : Couret.STROBO2TORS.recoh_stability_cubic_reading_norm
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:52:27.069974+00:00
-- url     : https://prove2.me/theorems/22dc07c2-f394-4a78-8e4b-f05a646c4f35
-- title:
--   Exact amplitude of a nontrivial cubic reading
-- statement:
--   For $z\in\mathbb C$ with $z^3=1$, $z\ne1$,
--
--   $$|1+2z|=\sqrt3.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohExceptionalStability.lean#L23-L49, lines 23–49; source file SHA-256 788e929f7e526870f55ea3a771c8f7f5dc647bcd18b0afb61c80f3eaf4f4c947; theorem Couret.STROBO2TORS.recoh_stability_cubic_reading_norm

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
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15

set_option autoImplicit false

/-!
Exact separation constants in the exceptional normal form.  Binary probes
have amplitudes one or three, and a detecting ternary probe separates the
two orbits by exactly twice the square root of three.  The two-torsion pair
inside the normal form supplies a matching universal upper bound of two.
-/

namespace Couret.STROBO2TORS

theorem recoh_stability_cubic_reading_norm (z : ℂ) (hz : z ^ 3 = 1) (hne : z ≠ 1) :
    ‖1 + 2 * z‖ = Real.sqrt 3 := by sorry


variable {G : Type*} [AddCommGroup G] [DecidableEq G]





variable [Fintype G]





















end Couret.STROBO2TORS
