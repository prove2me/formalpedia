-- Prove2me | Theorems.Thm_PowerSumReveal_powerSum_prime_pow_not_dvd
-- name    : PowerSumReveal.powerSum_prime_pow_not_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:37:23.363119+00:00
-- url     : https://prove2.me/theorems/a274d370-649c-43cf-bb98-78e5e82cabc4
-- title:
--   If `(p-1) ∣ k` then exactly one power of `p` is lost: `p^{e-1}` divides the power sum
-- statement:
--   If `(p-1) ∣ k` then exactly one power of `p` is lost: `p^{e-1}` divides the power sum
--   but `p^e` does not (assuming `p ∤ m`).
--
--   ```lean
--   theorem PowerSumReveal.powerSum_prime_pow_not_dvd{p e m k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 1 ≤ e)
--       (hk : k ≠ 0) (hdk : (p - 1) ∣ k) (hm : ¬ p ∣ m) :
--       p ^ (e - 1) ∣ powerSum (p ^ e * m) k ∧ ¬ p ^ e ∣ powerSum (p ^ e * m) k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PowerSumPrimePower.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PowerSumPrimePower.lean#L213

-- Thm stub generated from Geometry/PowerSumPrimePower.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPrimePower

/-!
# Cycle 3: the power-sum reveal at a prime power

The squarefree theory of `Geometry.PowerSumSquarefree` rests on the Fermat evaluation
`∑_{x : ZMod p} x^k = -1` (if `(p-1) ∣ k`) or `0`.  This file removes the squarefreeness
restriction at odd primes by proving the prime-power analogue

`∑_{a < p^e} a^k ≡ -p^{e-1} (mod p^e)` if `(p-1) ∣ k`, and `≡ 0 (mod p^e)` otherwise,

for every odd prime `p`, every `e ≥ 1` and every `k ≥ 1`.  Note the exponent: the
condition is `(p-1) ∣ k`, **not** `λ(p^e) = p^{e-1}(p-1) ∣ k`; the extra `p`-part of the
unit group plays no role.  (Numerically: for `p^e = 9` the sum is `≡ 6 = -3` for every
even `k`, not only for `k` divisible by `6`.)

The proof is an induction on `e` using the "lift the exponent" step

`∑_{a < p^e} a^k ≡ p · ∑_{a < p^{e-1}} a^k (mod p^e)`,

obtained by writing `a = p^{e-1} j + r` and expanding binomially: the square of
`p^{e-1}` vanishes mod `p^e`, and the linear term carries the Gauss sum
`∑_{j<p} j = p(p-1)/2`, which is divisible by `p` precisely because `p` is odd.

Consequences: for `N = p^e * m` with `p ∤ m`,

`gcd (powerSum N k, p^e) = if (p-1) ∣ k then p^{e-1} else p^e`,

so a prime power `p^e ‖ N` is revealed in full unless `(p-1) ∣ k`, in which case exactly
one power of `p` is lost.  This is the correct generalisation of the semiprime master
formula to non-squarefree moduli.

## Main results

* `PowerSumReveal.sum_range_pow_prime_pow` — the prime-power Fermat sum.
* `PowerSumReveal.powerSum_prime_pow_dvd` / `powerSum_prime_pow_not_dvd`.
* `PowerSumReveal.gcd_powerSum_prime_pow` — the prime-power master formula.
-/

open PowerSumReveal

open Finset

/-! ## Two elementary tools -/



/-! ## Lifting the exponent -/


/-! ## The prime-power Fermat sum -/




/-! ## Consequences for the power sum -/

theorem PowerSumReveal.powerSum_prime_pow_not_dvd{p e m k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 1 ≤ e)
    (hk : k ≠ 0) (hdk : (p - 1) ∣ k) (hm : ¬ p ∣ m) :
    p ^ (e - 1) ∣ powerSum (p ^ e * m) k ∧ ¬ p ^ e ∣ powerSum (p ^ e * m) k := by sorry
