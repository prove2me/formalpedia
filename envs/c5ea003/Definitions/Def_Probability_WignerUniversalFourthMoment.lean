-- Prove2me | Definitions.Def_Probability_WignerUniversalFourthMoment
-- name    : Probability_WignerUniversalFourthMoment
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T15:45:20.490279+00:00
-- url     : https://prove2.me/theorems/db86a189-cc7e-44aa-8c43-3cf950f01d53
-- title:
--   Aether Catalog definitions — Probability_WignerUniversalFourthMoment
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerUniversalFourthMoment`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerUniversalFourthMoment.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Universality of the fourth spectral moment of Wigner matrices

The Rademacher computation of `Probability.WignerRademacherEnsemble` is a special
case of a *universal* phenomenon: the limiting spectral moments of a Wigner matrix
depend on the entry distribution **only through its mean and variance**.

Here we prove this at order four, for an arbitrary finitely supported entry law
`ℒ` with mean `0` and variance `1` (the fourth moment `m₄(ℒ)` is arbitrary):

  `E [ tr (W⁴) ] = 2N(N-1)² - 2N(N-1) + m₄ · N(N-1)`,

so that the normalised fourth spectral moment
`(1/N) E [ tr ((W/√N)⁴) ] → 2 = C₂`, independently of `m₄`.  The `m₄`-dependent
term counts the degenerate walks that traverse a single edge four times; there are
only `O(N²)` of them, which is why the entry distribution is invisible in the limit.

The proof replaces the sign-flip involution of the Rademacher case by genuine
independence: the expectation of a product over edges factorises
(`gexpect_prod`), so any closed walk that uses some edge exactly once contributes
`0` because the entries are centred.
-/

open Matrix BigOperators Finset Filter Topology
open RademacherWigner (edgeOf indA indB indC)

namespace WignerUniversal

variable {S : Type*} [Fintype S]

/-- A finitely supported, centred, unit-variance entry law: `w` are the
probabilities and `v` the values taken by a single matrix entry. -/
structure EntryLaw (S : Type*) [Fintype S] where
  /-- probability weights -/
  w : S → ℝ
  /-- values of the entry -/
  v : S → ℝ
  /-- weights are nonnegative -/
  w_nonneg : ∀ s, 0 ≤ w s
  /-- weights sum to one -/
  total : ∑ s, w s = 1
  /-- the law is centred -/
  mean : ∑ s, w s * v s = 0
  /-- the law has unit variance -/
  var : ∑ s, w s * v s ^ 2 = 1

/-- The fourth moment of the entry law (unconstrained). -/
noncomputable def EntryLaw.m4 (L : EntryLaw S) : ℝ := ∑ s, L.w s * L.v s ^ 4

variable {N : ℕ}

/-- A configuration: an independent sample of the entry law for each edge. -/
abbrev Conf (N : ℕ) (S : Type*) := (Fin N × Fin N) → S

/-- Expectation with respect to the product law. -/
noncomputable def gexpect (L : EntryLaw S) (f : Conf N S → ℝ) : ℝ :=
  ∑ ω : Conf N S, (∏ e, L.w (ω e)) * f ω

/-- The matrix entries: zero on the diagonal, symmetric, sampled at edge `{i,j}`. -/
def gentry (L : EntryLaw S) (ω : Conf N S) (i j : Fin N) : ℝ :=
  if i = j then 0 else L.v (ω (edgeOf i j))



/-- The random matrix of the ensemble. -/
def GW (L : EntryLaw S) (ω : Conf N S) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => gentry L ω i j



/-! ### Linearity of the expectation -/




/-! ### Independence: the expectation of a product over edges factorises -/


/-! ### Elementary products over the edge set -/




/-! ### The expectation of a single closed 4-walk -/






/-! ### The universal fourth trace moment -/



/-! ### The Rademacher law as an instance -/

/-- The symmetric Rademacher law `±1` with probability `1/2`. -/
noncomputable def rademacherLaw : EntryLaw Bool where
  w := fun _ => 1 / 2
  v := fun b => if b then 1 else -1
  w_nonneg := by intro s; norm_num
  total := by simp
  mean := by simp
  var := by simp



end WignerUniversal


