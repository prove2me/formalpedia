-- Prove2me | Theorems.Thm_PowerSumGCD_powerSum_modEq_giuga
-- name    : PowerSumGCD.powerSum_modEq_giuga
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:21:56.201436+00:00
-- url     : https://prove2.me/theorems/6b94e2b8-47c6-4e94-b688-a408f814576a
-- title:
--   Giuga-type closed form.
-- statement:
--   **Giuga-type closed form.**  For squarefree `N` and `k > 0`,
--   `F(N,k) + ∑_{r ∣ N, (r-1) ∣ k} N/r ≡ 0 (mod N)`, i.e.
--   `F(N,k) ≡ -∑_{r ∣ N, (r-1) ∣ k} N/r`.
--
--   ```lean
--   theorem PowerSumGCD.powerSum_modEq_giuga{N k : ℕ} (hN : Squarefree N) (hk : 0 < k) :
--       powerSum N k + ∑ r ∈ N.primeFactors.filter (fun r => (r - 1) ∣ k), N / r ≡ 0 [MOD N] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PowerSumGCDGiuga.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PowerSumGCDGiuga.lean#L41

-- Thm stub generated from Novelty/PowerSumGCDGiuga.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Definitions.Def_Novelty_PowerSumGCDGeneral

/-!
# A Giuga-type closed form for the power sum modulo a squarefree modulus

The divisibility characterisation `prime_dvd_powerSum_iff` says *whether* a prime factor
divides `F(N,k) = ∑_{a=1}^{N} a^k`.  Here we pin down the exact residue: for squarefree
`N` and `k > 0`,

  `F(N,k) ≡ - ∑_{r prime, r ∣ N, (r-1) ∣ k}  N / r   (mod N)`.

This is the power-sum analogue of the von Staudt–Clausen / Giuga formula: modulo the
prime `r₀`, every summand `N/r` with `r ≠ r₀` dies (because `r₀ ∣ N/r` for squarefree
`N`), while the surviving term `N/r₀` cancels the Fermat contribution `-N/r₀` of the
`r₀`-block.  Specialising to `N = p` prime and `k = p-1` recovers Giuga's sum
`∑_{a=1}^{p-1} a^{p-1} ≡ -1 (mod p)`.

## Main results

* `dvd_div_of_ne_of_mem_primeFactors` : `r₀ ∣ N / r` for distinct primes of a squarefree `N`;
* `powerSum_modEq_giuga` : the closed form above (written additively in `ℕ`);
* `powerSum_prime_giuga` : `∑_{a=1}^{p} a^{p-1} + 1 ≡ 0 (mod p)` for `p` prime;
* `powerSum_giuga_iff_neg_one` : for squarefree `N`, `F(N,k) ≡ -1 (mod N)` exactly when the
  Giuga sum `∑_{(r-1) ∣ k} N/r` is `≡ 1 (mod N)`.
-/

open Finset

open PowerSumGCD

theorem PowerSumGCD.powerSum_modEq_giuga{N k : ℕ} (hN : Squarefree N) (hk : 0 < k) :
    powerSum N k + ∑ r ∈ N.primeFactors.filter (fun r => (r - 1) ∣ k), N / r ≡ 0 [MOD N] := by sorry
