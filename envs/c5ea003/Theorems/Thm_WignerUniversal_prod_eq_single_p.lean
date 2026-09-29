-- Prove2me | Theorems.Thm_WignerUniversal_prod_eq_single_p
-- name    : WignerUniversal.prod_eq_single_p
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T20:32:09.379864+00:00
-- url     : https://prove2.me/theorems/47fc97ad-a65f-4c16-ba32-5a664e8402d7
-- title:
--   Prod eq single'
-- statement:
--   Formal statement of `WignerUniversal.prod_eq_single_p` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem WignerUniversal.prod_eq_single'{ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) (F : ι → ℝ)
--       (h1 : ∀ e, e ≠ p → F e = 1) : ∏ e, F e = F p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerUniversalFourthMoment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerUniversalFourthMoment.lean#L116

-- Thm stub generated from Probability/WignerUniversalFourthMoment.lean
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

theorem WignerUniversal.prod_eq_single_p{ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι) (F : ι → ℝ)
    (h1 : ∀ e, e ≠ p → F e = 1) : ∏ e, F e = F p := by sorry
