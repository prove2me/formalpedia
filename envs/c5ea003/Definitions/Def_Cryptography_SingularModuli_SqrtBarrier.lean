-- Prove2me | Definitions.Def_Cryptography_SingularModuli_SqrtBarrier
-- name    : Cryptography_SingularModuli_SqrtBarrier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:35:39.191496+00:00
-- url     : https://prove2.me/theorems/6546b8ce-1fee-4c2e-90d3-55cdf7c7eef0
-- title:
--   Aether Catalog definitions — Cryptography_SingularModuli_SqrtBarrier
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.SingularModuli.SqrtBarrier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/SingularModuli/SqrtBarrier.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount

/-!
# Singular Moduli Factoring, Step 3: the `√N` barrier

`RootCount.lean` shows that for a monic `H` of degree `h` and a semiprime
`N = pq`, the number of useful evaluation points modulo `N` is at most
`h (p + q)`.  Here we convert that counting bound into the running-time
statement of the paper:

* `successDensity_le` — the probability that a uniformly random `j₀ ∈ [0, N)`
  succeeds is at most `h (1/p + 1/q)`;
* `successDensity_le_balanced` — for a balanced semiprime (`p ≤ q ≤ 3p`) this is
  at most `4h/√N`;
* `expected_trials_ge` — hence the expected number of evaluations before a
  success is at least `√N / (4h)`;
* `multiDiscriminant_successDensity_le_balanced` — **running several
  discriminants does not help**: over a family `F` of monic class polynomials of
  degree `≤ h`, the density of successful (discriminant, evaluation point) pairs
  is still at most `4h/√N`.  The barrier is not an artifact of using a single
  `H_D`.

The last item is the formal content of the "circularity bottleneck": the useful
set is `{j₀ : H_D(j₀) ≡ 0 mod p}`, which is defined in terms of the unknown
prime `p`, and it is a `O(h·√N)`-density subset of the search space no matter
how the discriminants are chosen.
-/

namespace SingularModuli

open Polynomial Finset FactoringBarriers

variable {p q : ℕ} {H : Polynomial ℤ}




/-! ## Many discriminants do not break the barrier -/

open scoped Classical in
/-- The set of successful (discriminant polynomial, evaluation point) pairs for a
finite family `F` of class polynomials. -/
noncomputable def successPairs (F : Finset (Polynomial ℤ)) (N : ℕ) : Finset (Polynomial ℤ × ℕ) :=
  (F ×ˢ Finset.range N).filter (fun z => NontrivialDivisor N (evalGcd z.1 (z.2 : ℤ) N))



end SingularModuli


