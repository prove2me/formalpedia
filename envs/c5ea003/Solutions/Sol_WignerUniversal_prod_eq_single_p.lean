-- Prove2me | solution 1 for WignerUniversal.prod_eq_single_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T20:32:21.316709+00:00
-- url     : https://prove2.me/submissions/68030b33-a16e-40b3-8c7a-a297895bc879

-- Sol generated from Probability/WignerUniversalFourthMoment.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerUniversalFourthMoment
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
open WignerUniversal

variable {S : Type*} [Fintype S]



variable {N : ℕ}









/-! ### Linearity of the expectation -/




/-! ### Independence: the expectation of a product over edges factorises -/


/-! ### Elementary products over the edge set -/




/-! ### The expectation of a single closed 4-walk -/






/-! ### The universal fourth trace moment -/



/-! ### The Rademacher law as an instance -/





open WignerUniversal in
theorem solution{ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) (F : ι → ℝ)
    (h1 : ∀ e, e ≠ p → F e = 1) : ∏ e, F e = F p :=
  Finset.prod_eq_single p (fun b _ hb => h1 b hb) (by simp)
