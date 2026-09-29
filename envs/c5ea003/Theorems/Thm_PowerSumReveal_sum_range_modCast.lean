-- Prove2me | Theorems.Thm_PowerSumReveal_sum_range_modCast
-- name    : PowerSumReveal.sum_range_modCast
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:36:10.4126+00:00
-- url     : https://prove2.me/theorems/7a2ea04b-ba99-40df-b94a-fcda4420bac0
-- title:
--   Summing a function of `a mod p` over one full period `range p` is the same as
-- statement:
--   Summing a function of `a mod p` over one full period `range p` is the same as
--   summing over `ZMod p`.
--
--   ```lean
--   theorem PowerSumReveal.sum_range_modCast(p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
--       ∑ a ∈ range p, f (a : ZMod p) = ∑ x : ZMod p, f x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PowerSumFactorReveal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PowerSumFactorReveal.lean#L68

-- Thm stub generated from Geometry/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal

/-!
# Power-sum GCD factor reveal

For a modulus `N` put

`powerSum N k = ∑_{a = 1}^{N} a ^ k`.

The main result of this file is a *complete* description of `gcd (powerSum N k) N`
when `N = p * q` is a semiprime and `k ≥ 1`:

`gcd (powerSum (p*q) k, p*q) = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`.

The mechanism is a two-step reduction.

* *Periodicity.* The interval `[1, N]` with `N = p * m` covers every residue class
  modulo `p` exactly `m` times, so `powerSum (p*m) k ≡ m * ∑_{x ∈ ZMod p} x^k (mod p)`.
* *Fermat.* For `k ≥ 1`, `∑_{x ∈ ZMod p} x^k = -1` if `(p-1) ∣ k` and `= 0` otherwise.

Consequently `p ∣ powerSum (p*m) k ↔ ¬ (p-1) ∣ k` (when `p ∤ m`), and the gcd formula
follows from multiplicativity of `Nat.gcd` over coprime factors.

Specialising to `k = p - 1` gives the advertised **factor reveal**:
`gcd (powerSum (p*q) (p-1), p*q) = q` whenever `(q-1) ∤ (p-1)`.

## Main results

* `PowerSumReveal.sum_pow_zmod` — Fermat power-sum over `ZMod p`.
* `PowerSumReveal.powerSum_cast` — the periodicity reduction, in `ZMod p`.
* `PowerSumReveal.prime_dvd_powerSum_iff` — divisibility criterion.
* `PowerSumReveal.gcd_powerSum_semiprime` — the master gcd formula.
* `PowerSumReveal.powerSum_factor_reveal` — Theorem 1 (factor reveal at `k = p-1`).
-/

open PowerSumReveal

open Finset



/-! ## Step 1: the Fermat power sum over `ZMod p` -/


/-! ## Step 2: periodicity of `a ↦ a mod p` on an interval of length `p * m` -/

theorem PowerSumReveal.sum_range_modCast(p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    ∑ a ∈ range p, f (a : ZMod p) = ∑ x : ZMod p, f x := by sorry
