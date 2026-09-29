-- Prove2me | Definitions.Def_NumberTheory_RLHFEulerProductGeneral
-- name    : NumberTheory_RLHFEulerProductGeneral
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:37.198952+00:00
-- url     : https://prove2.me/theorems/b3aa0e11-fc66-4263-bd8c-1ef713e83de7
-- title:
--   Aether Catalog definitions — NumberTheory_RLHFEulerProductGeneral
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.RLHFEulerProductGeneral`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/RLHFEulerProductGeneral.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy

/-!
# The full Euler product of an aligned policy: arbitrarily many primes

`NumberTheory.RLHFZetaEulerPolicy` treated the two-prime smooth response space.  Here we
carry the construction to a response space built from `k` primes with individually bounded
exponents,

`Ω = Π i, Fin (A i + 1)`,   `n(a) = ∏ i, (P i) ^ (a i)`,

and the Dirichlet reward `r(n) = -β s log n`.  The results:

* `RLHF.zetaWeight_prod` — complete multiplicativity of `n ↦ n^{-s}` over finite products.
* `RLHF.zetaSumMulti_eq_prod` — the **Euler product**: the partition function of the
  aligned policy factors as `∏ i, localZeta s (P i) (A i)`.
* `RLHF.gibbs_multi_independent` — the aligned policy is the product of its per-prime
  marginals: *all* prime exponents are mutually independent under RLHF alignment.
* `RLHF.freeEnergy_multi_additive` — the RLHF free energy is a sum of per-prime terms.
* `RLHF.freeEnergy_multi_lt_euler` — a Mertens-type strict upper bound by the genuine
  Euler factors `-∑ log (1 - P i ^ {-s})`.
-/

namespace RLHF

open Finset

variable {k : ℕ}

/-! ## 1. Multi-prime smooth response spaces -/

/-- The multi-exponent response space. -/
abbrev SmoothMulti (A : Fin k → ℕ) := (i : Fin k) → Fin (A i + 1)

/-- The integer named by a tuple of prime exponents. -/
def smoothValMulti (P : Fin k → ℕ) {A : Fin k → ℕ} (a : SmoothMulti A) : ℕ :=
  ∏ i, P i ^ (a i : ℕ)



/-! ## 2. The Euler product for the partition function -/

/-- The multi-prime truncated zeta sum. -/
noncomputable def zetaSumMulti (s : ℝ) (P : Fin k → ℕ) (A : Fin k → ℕ) : ℝ :=
  ∑ a : SmoothMulti A, zetaWeight s (smoothValMulti P a)



/-! ## 3. The aligned policy and its independence structure -/

/-- The Dirichlet reward on the multi-prime response space. -/
noncomputable def zetaRewardMulti (β s : ℝ) (P : Fin k → ℕ) {A : Fin k → ℕ} :
    SmoothMulti A → ℝ :=
  fun a => -(β * s) * Real.log (smoothValMulti P a : ℝ)





/-! ## 4. Additivity of the free energy over the primes -/



end RLHF


