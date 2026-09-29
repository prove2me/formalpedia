-- Prove2me | Definitions.Def_Algebra_RLHFDriftCore
-- name    : Algebra_RLHFDriftCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T09:14:14.445142+00:00
-- url     : https://prove2.me/theorems/12ef8e2f-58df-4c10-b640-c140053d6820
-- title:
--   Aether Catalog definitions — Algebra_RLHFDriftCore
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.RLHFDriftCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/RLHFDriftCore.lean by skeleton subtraction
import Mathlib

/-!
# Core objects of the RLHF alignment-drift catalogue

Domain: Algebra (convex analysis × information theory × alignment theory).

This file collects the base objects that the RLHF drift thread of the catalogue is
phrased in — finite probability vectors, the Gibbs (KL-regularised) policy, the
Kullback–Leibler divergence, the total-variation (`ℓ¹`) distance, and the first two
moment functionals of a reward — together with the elementary API used downstream.

The names and definitions follow the conventions of the RLHF drift files of the
catalogue (`RLHF.IsDist`, `RLHF.gibbsPolicy`, `RLHF.klDiv`, `RLHF.l1Dist`,
`RLHF.rewardRange`, `RLHF.mean`, `RLHF.variance`, ...), so the results proved here and
in `Algebra.RLHFMeanAbsoluteDeviation` / `Algebra.RLHFKLSecondOrder` speak about
exactly the same objects as `RLHF.kl_gibbs_le_variance` and
`RLHF.gibbs_l1_le_variance`.

Nothing in this file is deep; it exists so that the two research files that follow are
self-contained and compile.
-/

namespace RLHF

open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## 1. Finite probability vectors -/

/-- A probability vector on a finite type. -/
structure IsDist (p : Ω → ℝ) : Prop where
  nonneg : ∀ y, 0 ≤ p y
  total : ∑ y, p y = 1

/-- A strictly positive probability vector (full support). -/
structure IsPosDist (p : Ω → ℝ) : Prop where
  pos : ∀ y, 0 < p y
  total : ∑ y, p y = 1


/-! ## 2. Moment functionals -/

/-- The mean `𝔼_p[f] = ∑ y, p y · f y`. -/
noncomputable def mean (p f : Ω → ℝ) : ℝ := ∑ y, p y * f y

/-- The variance `Var_p(f) = 𝔼_p[(f − 𝔼_p f)²]`. -/
noncomputable def variance (p f : Ω → ℝ) : ℝ := ∑ y, p y * (f y - mean p f) ^ 2

/-- The **mean absolute deviation** `MAD_p(f) = 𝔼_p|f − 𝔼_p f|`. -/
noncomputable def mad (p f : Ω → ℝ) : ℝ := ∑ y, p y * |f y - mean p f|

/-- The covariance `Cov_p(f, g) = 𝔼_p[(f − 𝔼_p f)(g − 𝔼_p g)]`. -/
noncomputable def cov (p f g : Ω → ℝ) : ℝ :=
  ∑ y, p y * ((f y - mean p f) * (g y - mean p g))





/-! ## 3. The Gibbs policy -/

/-- The partition function `Z_β = ∑ y, p y e^{r y / β}`. -/
noncomputable def partition (β : ℝ) (r p : Ω → ℝ) : ℝ := ∑ y, p y * Real.exp (r y / β)

/-- The KL-regularised (Gibbs) policy `π_β(y) ∝ p y · e^{r y / β}`. -/
noncomputable def gibbsPolicy (β : ℝ) (r p : Ω → ℝ) : Ω → ℝ :=
  fun y => p y * Real.exp (r y / β) / partition β r p

/-- The Kullback–Leibler divergence `KL(q ‖ p) = ∑ y, q y log (q y / p y)`. -/
noncomputable def klDiv (q p : Ω → ℝ) : ℝ := ∑ y, q y * Real.log (q y / p y)

/-- The `ℓ¹` (twice total-variation) distance. -/
noncomputable def l1Dist (q p : Ω → ℝ) : ℝ := ∑ y, |q y - p y|


variable [Nonempty Ω]

/-- The reward range `max r − min r`. -/
noncomputable def rewardRange (r : Ω → ℝ) : ℝ :=
  univ.sup' univ_nonempty r - univ.inf' univ_nonempty r








end RLHF


