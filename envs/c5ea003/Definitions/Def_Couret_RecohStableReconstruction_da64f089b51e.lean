-- Prove2me | Definitions.Def_Couret_RecohStableReconstruction_da64f089b51e
-- name    : Couret_RecohStableReconstruction_da64f089b51e
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:12:58.116356+00:00
-- url     : https://prove2.me/theorems/1f953164-481e-45b4-b268-a31cd61c3c70
-- title:
--   Rational prediction centres and guarded noisy reconstruction
-- statement:
--   For a finite product of cyclic groups ZMod(q i), indexed by Fin d with every q i nonzero, defines the selected stable character bank and rational predicted readings from finite sums of rational root approximations. Binary slots use the stable binary multiplier and power-of-two order; the selected ternary slot uses multiplier one and power-of-three order. Prediction tolerance is (1−epsilon)/4 and acceptance radius is epsilon plus that tolerance. The precision guard requires rational 0≤epsilon<1, |PiPartial(machinTerms)|≤4, at least 15 Taylor terms, and three times the rational phase-error bound no greater than the prediction tolerance. The core applies noisy sign decoding to square-derived representatives. The public decoder returns this core only when both the typed-square format check and precision check pass; otherwise it returns the empty finite set. These definitions specify the guard and computation, without themselves asserting a reconstruction guarantee.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableReconstruction.lean; source file SHA-256 6ba847ab84346711528fad14d2971d71a5bd99f9152b733aa4ad067c05fd8df3

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
import Mathlib.Data.Nat.Log
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
import Mathlib.Topology.Algebra.Order.Floor
import Definitions.Def_Couret_RecohStableSquareSelection_4ccedec76589
import Definitions.Def_Couret_RecohStableBank_b01db9b053a3
import Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
import Definitions.Def_Couret_RecohRationalRoots_2e1442988636

set_option autoImplicit false

/-!
End-to-end stable reconstruction on explicit cyclic products.  The square
determines the bank, rational series determine the prediction centres, and
the decoder generates at most one candidate per square representative.
Precision is supplied by two natural numbers and checked by rational guards.
No complex comparison occurs in the executable definitions.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

noncomputable def recohComputedStableBank
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ)) :
    RecohSelectedBankIndex q entries → AddChar ((i : Fin d) → ZMod (q i)) ℂ :=
  recohStableObservedBank q entries (recohStableBinaryMultiplier q entries)





def recohSupportPhaseCenter (S : Finset ((i : Fin d) → ZMod (q i)))
    (coordinate : Fin d) (N multiplier machinTerms taylorTerms : ℕ) : RecohRationalComplex :=
  ∑ x ∈ S, recohRationalRootPower N ((x coordinate).val * multiplier) machinTerms taylorTerms



def recohStablePredictionTolerance (epsilon : ℚ) : ℚ := (1 - epsilon) / 4

def recohStableAcceptanceRadius (epsilon : ℚ) : ℚ :=
  epsilon + recohStablePredictionTolerance epsilon

def RecohStablePrecisionValid (epsilon : ℚ) (machinTerms taylorTerms : ℕ) : Prop :=
  0 ≤ epsilon ∧ epsilon < 1 ∧ |recohPiPartial machinTerms| ≤ 4 ∧
    15 ≤ taylorTerms ∧
      3 * recohRationalPhaseError machinTerms taylorTerms ≤ recohStablePredictionTolerance epsilon

instance (epsilon : ℚ) (machinTerms taylorTerms : ℕ) :
    Decidable (RecohStablePrecisionValid epsilon machinTerms taylorTerms) := by
  unfold RecohStablePrecisionValid
  infer_instance

def recohStablePrecisionCheck (epsilon : ℚ) (machinTerms taylorTerms : ℕ) : Bool :=
  decide (RecohStablePrecisionValid epsilon machinTerms taylorTerms)







def recohStablePredictedReading
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (machinTerms taylorTerms : ℕ) (S : Finset ((i : Fin d) → ZMod (q i))) :
    RecohSelectedBankIndex q entries → RecohRationalComplex :=
  Sum.elim
    (fun i => recohSupportPhaseCenter q S i.val
      (2 ^ ((recohCanonicalPrimaryData q 2).exponent i + 1))
      (recohStableBinaryMultiplier q entries i) machinTerms taylorTerms)
    (fun i => recohSupportPhaseCenter q S i.val.val
      (3 ^ ((recohCanonicalPrimaryData q 3).exponent i.val + 1)) 1 machinTerms taylorTerms)



def recohStableNoisyCore
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (observed : RecohSelectedBankIndex q entries → RecohRationalComplex)
    (epsilon : ℚ) (machinTerms taylorTerms : ℕ) : Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  recohNoisySignDecoder (recohCyclicSquareRepresentatives q entries)
    (recohProductTwoCoordinates q) Sum.inl
    (recohStablePredictedReading q entries machinTerms taylorTerms) observed
    (recohStableAcceptanceRadius epsilon)

def recohStableNoisyDecoder
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (observed : RecohSelectedBankIndex q entries → RecohRationalComplex)
    (epsilon : ℚ) (machinTerms taylorTerms : ℕ) : Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  if recohTypedSquareFormatCheck entries && recohStablePrecisionCheck epsilon machinTerms taylorTerms then
    recohStableNoisyCore q entries observed epsilon machinTerms taylorTerms
  else ∅















end Couret.STROBO2TORS


