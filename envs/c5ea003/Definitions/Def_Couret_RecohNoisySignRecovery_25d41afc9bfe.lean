-- Prove2me | Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
-- name    : Couret_RecohNoisySignRecovery_25d41afc9bfe
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:05:10.911988+00:00
-- url     : https://prove2.me/theorems/bf901326-4d8f-4a2e-a79a-9b977f146763
-- title:
--   Rational ball tests and candidate sign recovery
-- statement:
--   Defines a Boolean test that radius is nonnegative and the rational squared distance from an observed value to a predicted base value is at most radius², with equality accepted. Given an additive equivalence from the two-torsion subgroup to J→ZMod 2, predicted readings and observed readings, recohNoisyRecoverSupport passes these binary sign tests to the indexed support recovery. RecoveredCandidates is the finite-set image of supplied representatives, so duplicate outputs are removed and empty input gives no candidates. The complete decoder uses an index J→I with finite I to select binary readings, then applies the full rational noisy-reading filter to the recovered candidates. No finite ambient group is required by these definitions.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisySignRecovery.lean; source file SHA-256 0b99604778196eef3e1a2e7f4520b571c7f705ced9a9268c1833a15086c9a9a4

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
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
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8
import Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3

set_option autoImplicit false

/-!
Noisy sign recovery from a list of square-fibre representatives.  Each
binary sign is recovered by one rational ball test, then transported through
the existing two-torsion coordinate equivalence.  At most one candidate is
created per representative, without enumerating the two-torsion subgroup.
The rational decoder in RecohNoisyUniqueness supplies the final tolerance
filter and uniqueness contract.
-/

namespace Couret.STROBO2TORS

/-- Positive sign test, using only rational arithmetic. -/
def recohRationalSignSame (base observed : RecohRationalComplex) (radius : ℚ) : Bool :=
  decide (0 ≤ radius ∧ recohRationalSquaredDistance observed base ≤ radius ^ 2)





variable {G J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2

/-- Recover a candidate support from its predicted representative and
the rational noisy readings.  The coordinate inverse is supplied as data. -/
def recohNoisyRecoverSupport (e : H₂ ≃+ (J → ZMod 2))
    (predicted : Finset G → J → RecohRationalComplex)
    (observed : J → RecohRationalComplex) (radius : ℚ) (B : Finset G) : Finset G :=
  recohIndexedRecoverSupport e
    (fun T i => recohRationalSignSame (predicted T i) (observed i) radius) B

/-- One recovered candidate per representative; this definition never
enumerates the ambient group or its two-torsion subgroup. -/
def recohNoisyRecoveredCandidates (representatives : Finset (Finset G))
    (e : H₂ ≃+ (J → ZMod 2))
    (predicted : Finset G → J → RecohRationalComplex)
    (observed : J → RecohRationalComplex) (radius : ℚ) : Finset (Finset G) :=
  representatives.image (recohNoisyRecoverSupport e predicted observed radius)









/-- The complete executable decoder: generate one translation per supplied
representative, deduplicate, then check every full-bank reading using exact
rational squared-distance comparisons.  `index` selects the binary slots. -/
def recohNoisySignDecoder {I : Type*} [Fintype I]
    (representatives : Finset (Finset G)) (e : H₂ ≃+ (J → ZMod 2))
    (index : J → I) (predicted : Finset G → I → RecohRationalComplex)
    (observed : I → RecohRationalComplex) (radius : ℚ) : Finset (Finset G) :=
  recohRationalNoisyDecoder
    (recohNoisyRecoveredCandidates representatives e
      (fun B j => predicted B (index j)) (fun j => observed (index j)) radius)
    predicted observed radius







end Couret.STROBO2TORS


