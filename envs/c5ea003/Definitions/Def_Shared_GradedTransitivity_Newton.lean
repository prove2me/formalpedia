-- Prove2me | Definitions.Def_Shared_GradedTransitivity_Newton
-- name    : Shared_GradedTransitivity_Newton
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:54:22.031972+00:00
-- url     : https://prove2.me/theorems/82c19f98-9550-4bcd-8413-0e6121605140
-- title:
--   Aether Catalog definitions — Shared_GradedTransitivity_Newton
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.GradedTransitivity.Newton`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/GradedTransitivity/Newton.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_Structure

/-!
# Newton's forward-difference classification

This file closes the circle around the rationality criterion by proving the
missing *converse*: a sequence whose `k`-th forward difference vanishes
eventually is, from that point on, a `ℚ`-linear combination of the `k`
binomial functions `n ↦ C(n-N, j)`, `j < k` (Newton's forward difference
formula).  Together with `FiniteDifference` this yields the classification

`(1-q)^k` clears `∑ a n qⁿ`
  ⟺ `Δ^k a` vanishes eventually
  ⟺ `a` is eventually a combination of `C(·-N, j)`, `j < k`.

For a graded `G`-set this says: eventual `r`-transitivity is only the simplest
member of a hierarchy, and the exponent `k` in the denominator measures exactly
the binomial degree of the orbit-counting sequence.

## Main results

* `newton_forward` : Newton's forward difference formula.
* `sdiff_iter_binom_eq_zero` : the binomial functions are annihilated.
* `rationality_tfae_newton` : the three-way classification.
-/

namespace GradedTransitivity

open Polynomial

/-! ### Linearity of the difference operator -/




/-! ### The shifted binomial functions -/

/-- The `j`-th shifted binomial function `n ↦ C(n-N, j)`. -/
def binomShift (N j : ℕ) : ℕ → ℚ := fun n => ((n - N).choose j : ℚ)




/-! ### Newton's forward difference formula -/





/-! ### The classification -/


end GradedTransitivity


