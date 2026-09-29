-- Prove2me | Definitions.Def_Probability_ForkPinningCore
-- name    : Probability_ForkPinningCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:56.44867+00:00
-- url     : https://prove2.me/theorems/5f7e5196-01f1-4dee-9633-0ceb02c790af
-- title:
--   Aether Catalog definitions — Probability_ForkPinningCore
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ForkPinningCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ForkPinningCore.lean by skeleton subtraction
import Mathlib
/-
# Fork pinning: a finite information-theoretic core

This file develops, from scratch, the small amount of finite information theory needed to
state and prove the **fork-pinning criterion**:

> a binary "fork" (a two-valued statistic of a Frobenius element) is congruence-pinned by a
> Dirichlet character exactly when it factors through the abelianization of the Galois group.

The probabilistic model is the uniform measure on a finite type `Ω` (which, in the arithmetic
application, is the Galois group of the splitting field; Chebotarev equidistribution turns
"a random prime" into "a uniformly random Frobenius element").

Main results:

* `ForkPinning.negMulLog_sum_le` / `negMulLog_sum_lt` : super-additivity of `x ↦ -x log x`
  on non-negative families, with the strict form.
* `ForkPinning.entropy_le_entropy_joint` : `H X ≤ H (X, Y)` (conditional entropy is non-negative).
* `ForkPinning.pinned_iff_determines` : `I(X;Y) = H Y ↔ X determines Y`  — the pinning criterion.
* `ForkPinning.mutualInfo_le_entropy` : `I(X;Y) ≤ H Y`.
* `ForkPinning.mutualInfo_nonneg` : `0 ≤ I(X;Y)` (Gibbs / sub-additivity of entropy).
* `ForkPinning.mutualInfo_eq_zero_of_indep` : independence ⇒ flat fork.
* `ForkPinning.mutualInfo_const_left` : a constant statistic carries no information
  (the "within-face fork is flat" mechanism).
-/


namespace ForkPinning

open Finset Real

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable {κ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]

/-! ## Basic definitions: uniform measure, entropy, mutual information -/

/-- The fiber of a statistic `X` over a value `k`. -/
def fiber (X : Ω → κ) (k : κ) : Finset Ω := univ.filter (fun ω => X ω = k)

/-- The probability that the statistic `X` takes the value `k`, under the uniform measure. -/
noncomputable def prb (X : Ω → κ) (k : κ) : ℝ := (fiber X k).card / Fintype.card Ω

/-- Shannon entropy (in nats) of a statistic under the uniform measure on `Ω`. -/
noncomputable def H (X : Ω → κ) : ℝ := ∑ k : κ, negMulLog (prb X k)

/-- The joint statistic. -/
def joint (X : Ω → κ) (Y : Ω → β) : Ω → κ × β := fun ω => (X ω, Y ω)

/-- Mutual information `I(X;Y) = H X + H Y - H (X,Y)`. -/
noncomputable def mutualInfo (X : Ω → κ) (Y : Ω → β) : ℝ := H X + H Y - H (joint X Y)

/-- `X` determines `Y`: the fork `Y` factors through the statistic `X`. -/
def Determines (X : Ω → κ) (Y : Ω → β) : Prop := ∀ ω ω', X ω = X ω' → Y ω = Y ω'

/-! ## Elementary probability facts -/






/-! ## Super-additivity of `negMulLog` -/




/-! ## Conditional entropy is non-negative -/



/-! ## The pinning criterion -/







/-! ## Flatness -/







/-! ## Non-negativity of mutual information (Gibbs), with the equality case -/











/-! ## Capacity: the fork can learn at most `log |κ|` -/



/-! ## Conditional entropy: the quantitative pinned fraction -/

/-- The conditional law of the fork given `X = k` (the value is irrelevant when `prb X k = 0`). -/
noncomputable def condPrb (X : Ω → κ) (Y : Ω → β) (k : κ) (b : β) : ℝ :=
  prb (joint X Y) (k, b) / prb X k

/-- Entropy of the fork conditioned on the event `X = k`. -/
noncomputable def condEntropyAt (X : Ω → κ) (Y : Ω → β) (k : κ) : ℝ :=
  ∑ b : β, negMulLog (condPrb X Y k b)

/-- Conditional entropy `H(Y | X) = H(X,Y) − H(X)`. -/
noncomputable def condEntropy (X : Ω → κ) (Y : Ω → β) : ℝ := H (joint X Y) - H X



end ForkPinning


