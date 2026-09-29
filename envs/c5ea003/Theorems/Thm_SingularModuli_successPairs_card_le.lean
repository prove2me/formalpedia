-- Prove2me | Theorems.Thm_SingularModuli_successPairs_card_le
-- name    : SingularModuli.successPairs_card_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:10:36.88025+00:00
-- url     : https://prove2.me/theorems/77717642-ad73-4597-8fa4-d07790bc7154
-- title:
--   The successful pairs decompose over the family.
-- statement:
--   The successful pairs decompose over the family.
--
--   ```lean
--   theorem SingularModuli.successPairs_card_le(F : Finset (Polynomial ℤ)) (N : ℕ) :
--       (successPairs F N).card ≤ ∑ H ∈ F, successCount H N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SingularModuli/SqrtBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SingularModuli/SqrtBarrier.lean#L119

-- Thm stub generated from Cryptography/SingularModuli/SqrtBarrier.lean
import Mathlib
import Definitions.Def_Cryptography_SingularModuli_RootCount
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier

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

open SingularModuli

open Polynomial Finset FactoringBarriers

variable {p q : ℕ} {H : Polynomial ℤ}




/-! ## Many discriminants do not break the barrier -/

theorem SingularModuli.successPairs_card_le(F : Finset (Polynomial ℤ)) (N : ℕ) :
    (successPairs F N).card ≤ ∑ H ∈ F, successCount H N := by sorry
