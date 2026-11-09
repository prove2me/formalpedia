-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_rational_root_power_error
-- name    : Couret.STROBO2TORS.recoh_rational_root_power_error
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:25.015744+00:00
-- url     : https://prove2.me/theorems/94efd68d-d461-4aee-a67f-2f3de3857da0
-- title:
--   Rational phase centres approximate every cyclic root power
-- statement:
--   Let $A_m(x)=\sum_{j<m}(-1)^j x^{2j+1}/(2j+1)$, $p_m=16A_m(1/5)-4A_m(1/239)$ and $e_m=16(1/5)((1/5)^2)^m/(1-(1/5)^2)+4(1/239)((1/239)^2)^m/(1-(1/239)^2)$. Put $E_{m,n}=2e_m+2\cdot8^n/n!$. Rational-complex centres are interpreted as complex numbers. For positive $N$, natural $e,m,n$, $|p_m|\le4$ and $n\ge15$, let $c_{N,e}^{m,n}$ be the specified rational Taylor centre at turn $(e\bmod N)/N$. Then
--
--   $$|c_{N,e}^{m,n}-\zeta_N^e|\le E_{m,n}.$$
--
--   No bound on the unreduced exponent is needed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableSquareSelection.lean#L36-L46, lines 36–46; source file SHA-256 2f7714eca3c4e8b224d008d7909c95a42c2c459aa1c10a8588b3fe2fc9d9a1c8; theorem Couret.STROBO2TORS.recoh_rational_root_power_error

import Aesop
import Definitions.Def_Couret_RecohStableSquareSelection_4ccedec76589
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Cast.Order
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_phase_error
import Definitions.Def_Couret_RecohRationalRoots_2e1442988636
import Definitions.Def_Couret_RecohOddPowerRuntime_8c8d44664d18
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8

set_option autoImplicit false

/-!
The robust binary multipliers are computed from the exact labelled square.
Rational phase centres have a proved error budget.  The finite odd-power
search compares their squared norms to 9/4 and falls back to exponent one.
No support or measured character value is an input to this computation.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

theorem recoh_rational_root_power_error (N e machinTerms taylorTerms : ℕ) [NeZero N]
    (hpi : |recohPiPartial machinTerms| ≤ 4) (htaylor : 15 ≤ taylorTerms) :
    ‖recohRationalComplexValue (recohRationalRootPower N e machinTerms taylorTerms) -
      recohCyclicRoot N ^ e‖ ≤ (recohRationalPhaseError machinTerms taylorTerms : ℝ) := by sorry




variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

























end Couret.STROBO2TORS
