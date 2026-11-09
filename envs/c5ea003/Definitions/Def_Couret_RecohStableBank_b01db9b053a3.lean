-- Prove2me | Definitions.Def_Couret_RecohStableBank_b01db9b053a3
-- name    : Couret_RecohStableBank_b01db9b053a3
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:12:14.580653+00:00
-- url     : https://prove2.me/theorems/a88ea9ba-51a3-4e8d-8973-3083ef26baa8
-- title:
--   Powered binary characters in a square-selected measurement bank
-- statement:
--   Fix d : ℕ, q : Fin d → ℕ and instances asserting q(i)≠0. The group is the product of ZMod(q(i)). Binary coordinates are indices i with 2 dividing q(i). Given any natural multiplier for each such coordinate, recohStableBinaryBank raises its canonical primary-2 character to that power. Multipliers need not be positive or odd in this definition; power zero is allowed. recohStableObservedBank uses the same measurement index type as the square-selected bank for the supplied position/count entries: its left slots are these powered binary characters, and its right slots use the unmodified canonical primary-3 character at the selected ternary coordinate. The selected ternary index subtype is empty when no coordinate was selected and otherwise has one element. Entries need not satisfy a format hypothesis to form the definitions. The bundle asserts no amplitude, stability, or decoding guarantee.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableBank.lean; source file SHA-256 77be62a3e2bd7051471ff8ef5d23213a8670a43f693859dccdf4b62ca2c3d1e7

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
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
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
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8

set_option autoImplicit false

/-!
Quantitative reconstruction with the square-selected minimum-size bank.
Each binary character is replaced by a prescribed odd power; the selected
ternary character and the measurement index type are unchanged.

The multipliers are parameters of the bank and are fixed before readings are
received. The quantitative theorems require a certified amplitude bound on
the square fibre. A separate square-only selector supplies these parameters
and that bound.

The rational-decoder bridges use a supplied candidate set contained in the
fibre. They do not introduce an executable enumeration of the ambient group
or its powerset. Prediction error is included in the uniqueness budget.
-/

namespace Couret.STROBO2TORS



variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- One prescribed power of each canonical binary character. -/
noncomputable def recohStableBinaryBank (multipliers : RecohEvenCoordinate q → ℕ) :
    RecohEvenCoordinate q → AddChar ((i : Fin d) → ZMod (q i)) ℂ :=
  fun i => (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i) ^ multipliers i













/-- The measurement slots are exactly those of the square-selected bank. -/
noncomputable def recohStableObservedBank
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (multipliers : RecohEvenCoordinate q → ℕ) :
    RecohSelectedBankIndex q entries → AddChar ((i : Fin d) → ZMod (q i)) ℂ :=
  Sum.elim (recohStableBinaryBank q multipliers)
    (fun i => recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3) i.val)



















end Couret.STROBO2TORS


