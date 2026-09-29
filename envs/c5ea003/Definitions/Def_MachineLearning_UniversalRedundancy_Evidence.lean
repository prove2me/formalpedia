-- Prove2me | Definitions.Def_MachineLearning_UniversalRedundancy_Evidence
-- name    : MachineLearning_UniversalRedundancy_Evidence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:23.890014+00:00
-- url     : https://prove2.me/theorems/ae4a6f4b-0698-4073-bca9-a4cc1ab4cccb
-- title:
--   Aether Catalog definitions — MachineLearning_UniversalRedundancy_Evidence
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.UniversalRedundancy.Evidence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/UniversalRedundancy/Evidence.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Computational evidence for the price of universality

Exact small-case computations supporting the bounds of
`UniversalRedundancy.Bernoulli`.  `shtarkovBernoulliQ n` is the classical
normalized-maximum-likelihood normalizer of the binary memoryless class,

`∑_{k=0}^{n} C(n,k) (k/n)^k ((n-k)/n)^{n-k}`,

computed here in exact rational arithmetic.  The theorems below are *verified*
computations (no floating point, no `native_decide`): for `n = 2, 4, 8` they
pin down the exact value and confirm both sides of the proved sandwich
`√n / 4 ≤ Cₛ ≤ n + 1` — the lower bound in the equivalent rational form
`Cₛ² ≥ n/16`.

## Application Keywords

Shtarkov sum, NML normalizer, exact rational computation, small-case evidence
-/


open Finset

namespace UniversalRedundancy

/-- Exact rational value of the Shtarkov (NML) normalizer of the binary
memoryless class for messages of length `n`. -/
def shtarkovBernoulliQ (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1),
    (n.choose k : ℚ) * ((k : ℚ) / (n : ℚ)) ^ k * (((n - k : ℕ) : ℚ) / (n : ℚ)) ^ (n - k)






end UniversalRedundancy


