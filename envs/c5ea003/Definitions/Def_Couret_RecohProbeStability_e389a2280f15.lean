-- Prove2me | Definitions.Def_Couret_RecohProbeStability_e389a2280f15
-- name    : Couret_RecohProbeStability_e389a2280f15
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:45.073897+00:00
-- url     : https://prove2.me/theorems/ea1d7a40-1dc3-4908-b0c2-f0eb860e53be
-- title:
--   Coordinatewise separation of candidate readings
-- statement:
--   RecohReadingSeparated reading candidates δ, for arbitrary index types X,I, a reading X → I → ℂ, a finite candidate set, and a real δ, requires that each distinct pair S,T in the candidates admit some coordinate i with δ ≤ norm(reading(S,i)-reading(T,i)). RecohProbeSeparated specializes this to finite supports in an additive abelian group with decidable equality, using the unweighted, unnormalised sum of a bank character over each support. There is no positivity restriction on δ and no assumed nonempty index type: empty or singleton candidate sets satisfy the predicate vacuously, while distinct candidates require an actual coordinate. The bundle also defines the two explicit supports {0,1,2} and {0,2,3} in ZMod 4, named recohStabilityC4Left and recohStabilityC4Right; it includes no separation bound for them.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohProbeStability.lean; source file SHA-256 1d695a0d84e83ff92491e95ea472df8f9bf1059d52c5525c794d82c7f31a9800

import Aesop
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

/-- Coordinatewise separation of a finite candidate set. -/
def RecohReadingSeparated {X I : Type*} (reading : X → I → ℂ)
    (candidates : Finset X) (δ : ℝ) : Prop :=
  ∀ S ∈ candidates, ∀ T ∈ candidates, S ≠ T →
    ∃ i, δ ≤ ‖reading S i - reading T i‖

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Separation for the unweighted, unnormalised character bank. -/
def RecohProbeSeparated {I : Type*} (bank : I → AddChar G ℂ)
    (candidates : Finset (Finset G)) (δ : ℝ) : Prop :=
  RecohReadingSeparated (fun S i => recohSupportProbe (bank i) S) candidates δ











variable [Fintype G]





/-- The sharp uniform obstruction consists of these two explicit triples. -/
def recohStabilityC4Left : Finset (ZMod 4) := {0, 1, 2}

def recohStabilityC4Right : Finset (ZMod 4) := {0, 2, 3}







end Couret.STROBO2TORS


