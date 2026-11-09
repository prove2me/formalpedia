-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_square_phase_center_error
-- name    : Couret.STROBO2TORS.recoh_square_phase_center_error
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:18:09.921214+00:00
-- url     : https://prove2.me/theorems/0e6cda87-c9f6-44ad-b141-2b52f6798989
-- title:
--   The rational square transform has nine times the root error
-- statement:
--   Let $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$ with positive natural moduli $q_j$. Write $P_\chi(A)=\sum_{x\in A}\chi(x)$, $R_A$ for the ordered pair-sum count, and $F(A)$ for its fibre among triples. Let $A_m(x)=\sum_{j<m}(-1)^j x^{2j+1}/(2j+1)$, $p_m=16A_m(1/5)-4A_m(1/239)$ and $e_m=16(1/5)((1/5)^2)^m/(1-(1/5)^2)+4(1/239)((1/239)^2)^m/(1-(1/239)^2)$. Put $E_{m,n}=2e_m+2\cdot8^n/n!$. Rational-complex centres are interpreted as complex numbers. For an arbitrary sparse square-entry list $L$, let $R_L$ be its interpreted count function, $U_L=\{z:R_L(z)\ne0\}$, and $C_L(j,N,b,m,n)=\sum_{z\in U_L}R_L(z)c_{N,(z_j).\mathrm{val}b}^{m,n}$ the rational square phase centre. Suppose $|A|=3$, $R_A=R_L$, $N>0$ divides the modulus at coordinate $j$, $|p_m|\le4$, and $n\ge15$. Let $\chi_{j,N}$ be the canonical coordinate character. For every natural multiplier $b$,
--
--   $$|C_L(j,N,b,m,n)-P_{\chi_{j,N}^b}(A)^2|\le9E_{m,n}.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableSquareSelection.lean#L124-L160, lines 124–160; source file SHA-256 2f7714eca3c4e8b224d008d7909c95a42c2c459aa1c10a8588b3fe2fc9d9a1c8; theorem Couret.STROBO2TORS.recoh_square_phase_center_error

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_complex_scale_value
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_root_power_error
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_sq
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









variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_square_phase_center_error
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hR : orderedSquare S = recohTypedSquareValue entries)
    (coordinate : Fin d) (N : ℕ) [NeZero N] (hN : N ∣ q coordinate)
    (multiplier machinTerms taylorTerms : ℕ)
    (hpi : |recohPiPartial machinTerms| ≤ 4) (htaylor : 15 ≤ taylorTerms) :
    ‖recohRationalComplexValue
        (recohSquarePhaseCenter q entries coordinate N multiplier machinTerms taylorTerms) -
      (recohSupportProbe ((recohCyclicCoordinateCharacter q coordinate N hN) ^ multiplier) S) ^ 2‖ ≤
        9 * (recohRationalPhaseError machinTerms taylorTerms : ℝ) := by sorry














end Couret.STROBO2TORS
