-- Prove2me | Definitions.Def_Probability_WignerSecondMomentConcentration
-- name    : Probability_WignerSecondMomentConcentration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:42:58.02976+00:00
-- url     : https://prove2.me/theorems/43f41bd8-5dab-47ff-bedb-78a9e249fd98
-- title:
--   Aether Catalog definitions — Probability_WignerSecondMomentConcentration
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerSecondMomentConcentration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerSecondMomentConcentration.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_WignerUniversalFourthMoment
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Convergence in probability of the second spectral moment of a Wigner matrix

For an arbitrary centred, unit-variance entry law `ℒ` (finitely supported, fourth
moment `m₄`), the second moment of the empirical spectral distribution of `W/√N`

* has expectation exactly `1 - 1/N`, and
* has variance exactly `2 (m₄ - 1) (N-1) / N³`,

so by Chebyshev's inequality it converges **in probability** to `1 = C₁`, the
second moment of the Wigner semicircle law.  This is the `k = 2` case of the
semicircle law, proved for a general Wigner ensemble rather than for a single
entry distribution.
-/

open Matrix BigOperators Finset Filter Topology
open RademacherWigner (edgeOf)
open scoped Classical

namespace WignerUniversal

variable {S : Type*} [Fintype S] {N : ℕ}

/-! ### Basic probabilistic infrastructure -/

/-- The weight (product law probability) of a configuration. -/
noncomputable def weight (L : EntryLaw S) (ω : Conf N S) : ℝ := ∏ e, L.w (ω e)







/-- The probability of an event, i.e. of a finite set of configurations. -/
noncomputable def gprob (L : EntryLaw S) (A : Finset (Conf N S)) : ℝ :=
  ∑ ω ∈ A, weight L ω




/-! ### The second trace moment and its square -/




/-! ### The second moment of the second trace moment -/


/-- `ne i j = 1` iff `i ≠ j`. -/
def neInd (i j : Fin N) : ℝ := if i = j then 0 else 1

/-- Indicator of the coinciding ordered edge pair `(k,l) = (i,j)`. -/
def pairInd1 (i j k l : Fin N) : ℝ :=
  (if i = j then 0 else 1) * (if k = i then 1 else 0) * (if l = j then 1 else 0)

/-- Indicator of the reversed edge pair `(k,l) = (j,i)`. -/
def pairInd2 (i j k l : Fin N) : ℝ :=
  (if i = j then 0 else 1) * (if k = j then 1 else 0) * (if l = i then 1 else 0)






/-! ### Mean, variance and convergence in probability -/





end WignerUniversal


