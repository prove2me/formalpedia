-- Prove2me | Definitions.Def_Couret_RecohStableSquareSelection_4ccedec76589
-- name    : Couret_RecohStableSquareSelection_4ccedec76589
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:11:10.455234+00:00
-- url     : https://prove2.me/theorems/1d9b3f09-5408-4234-b26b-99a493ddb689
-- title:
--   Odd binary multipliers computed from exact square data
-- statement:
--   Let $A=\prod_{i<d}\mathbb Z/q_i$ with $d\ge0$ and every $q_i>0$. Input entries are a list of points of $A$ and natural multiplicities. A rational root-power center uses the turn $(e\bmod N)/N$ and the rational phase construction. For a coordinate and multiplier, the square-phase center sums these centers over the selected typed square support, weighted by the typed square-value function. For an even coordinate with canonical two-primary depth $a_i$, the algorithm uses order $N_i=2^{a_i+1}$, odd test multipliers $2j+1$, four Machin terms and 48 Taylor terms. It compares the rational squared norm with $9/4$ and selects $$m_i=2\,\operatorname{OddSquaredChoice}(2^{a_i},s_i)+1.$$ Only the supplied exact square entries enter this computation; no hidden support or measured character value is an input. Correct interpretation, input-format assumptions and quantitative stability guarantees belong to later theorems; the raw definition does not certify them for arbitrary malformed entries.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableSquareSelection.lean; source file SHA-256 2f7714eca3c4e8b224d008d7909c95a42c2c459aa1c10a8588b3fe2fc9d9a1c8

import Aesop
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



def recohRationalRootPower (N e machinTerms taylorTerms : ℕ) : RecohRationalComplex :=
  recohRationalPhase (((e % N : ℕ) : ℚ) / N) machinTerms taylorTerms





variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

def recohSquarePhaseCenter
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (coordinate : Fin d) (N multiplier machinTerms taylorTerms : ℕ) : RecohRationalComplex :=
  ∑ z ∈ recohSelectedSquareSupport q entries,
    recohRationalComplexScale (recohTypedSquareValue entries z)
      (recohRationalRootPower N ((z coordinate).val * multiplier) machinTerms taylorTerms)











def recohStableBinarySquareNorm
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (i : RecohEvenCoordinate q) (j : ℕ) : ℚ :=
  recohRationalSquaredDistance
    (recohSquarePhaseCenter q entries i.val
      (2 ^ ((recohCanonicalPrimaryData q 2).exponent i + 1)) (2 * j + 1) 4 48) (0, 0)

def recohStableBinaryMultiplier
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (i : RecohEvenCoordinate q) : ℕ :=
  2 * recohOddSquaredChoice (2 ^ (recohCanonicalPrimaryData q 2).exponent i)
    (recohStableBinarySquareNorm q entries i) + 1









end Couret.STROBO2TORS


