-- Prove2me | Theorems.Thm_NeuralCodeRateCeiling_binTerm_step_up
-- name    : NeuralCodeRateCeiling.binTerm_step_up
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:12:23.510044+00:00
-- url     : https://prove2.me/theorems/483885c2-408d-4bf7-9b31-9fbf88841775
-- title:
--   Below the peak the binomial terms increase.
-- statement:
--   Below the peak the binomial terms increase.
--
--   ```lean
--   theorem NeuralCodeRateCeiling.binTerm_step_up{N r k : ℕ} (hr : r ≤ N) (hk : k + 1 ≤ r) :
--       binTerm N r k ≤ binTerm N r (k + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NeuralCodeRateCeiling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NeuralCodeRateCeiling.lean#L74

-- Thm stub generated from Novelty/NeuralCodeRateCeiling.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodeRateCeiling

/-!
# Neural Coding: the Sphere-Packing Rate Ceiling

`Catalog/Novelty/NeuralCodeCapacityBounds.lean` established the *lower* half of
the rate–distance picture for noise-tolerant neural codes: the Gilbert–Varshamov
theorem says the robust capacity `A(N,d)` of `N` neurons has rate at least
`1 - H₂(δ)` bits per neuron, `δ = (d-1)/N`.  The matching *upper* half needs a
**lower** bound on a binomial coefficient, namely the largest-term estimate

`N ^ N ≤ (N + 1) * r ^ r * (N - r) ^ (N - r) * C(N, r)`,

equivalently `log C(N,r) ≥ N · H(r/N) - log (N+1)`.  That is what this file
proves, and then feeds into the sphere-packing (Hamming) bound to obtain the
**rate ceiling**

`log₂ A(N, 2t+1) / N ≤ 1 - H₂(t/N) + log₂(N+1) / N`.

Together with Gilbert–Varshamov this sandwiches the achievable rate of a
population of `N` neurons that must survive `t` misfirings.

## Main results

* `binTerm_le_center` — the binomial term `C(N,k) r^k (N-r)^(N-k)` is maximal at
  `k = r`: the Bernoulli(`r/N`) distribution on `N` neurons peaks at `r` active
  neurons.  (Proved entirely in `ℕ` by a two-sided ratio argument.)
* `pow_self_le_succ_mul_binTerm` — `N^N ≤ (N+1) * binTerm N r r`, the
  largest-term lower bound for the binomial sum.
* `four_pow_le_central_binom` — the classical corollary `4^n ≤ (2n+1) * C(2n,n)`.
* `log_choose_lower` — `N · H(r/N) - log (N+1) ≤ log C(N,r)`, the entropy lower
  bound on binomial coefficients (the converse of `log_ballVolume_le`).
* `ballVolume_entropy_sandwich` — combining with `log_ballVolume_le`, the volume
  of a Hamming ball of relative radius `δ ≤ 1/2` is `exp (N · H(δ))` up to a
  factor `N + 1`.
* `log_maxCodeSize_le` / `sphere_packing_rate_bits` — the **rate ceiling** for
  `t`-error-correcting neural codes.
* `neural_rate_sandwich` — the two-sided rate estimate: with `δ = t/N`,
  `1 - H₂(2δ) ≤ log₂ A(N,2t+1)/N ≤ 1 - H₂(δ) + log₂(N+1)/N`.
-/

open NeuralCodeRateCeiling

open Finset NeuralCodeCapacity

/-! ## The largest term of a binomial sum -/

theorem NeuralCodeRateCeiling.binTerm_step_up{N r k : ℕ} (hr : r ≤ N) (hk : k + 1 ≤ r) :
    binTerm N r k ≤ binTerm N r (k + 1) := by sorry
