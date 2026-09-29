-- Prove2me | solution 1 for PowerSumReveal.powerSum_cast_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:40:49.227012+00:00
-- url     : https://prove2.me/submissions/69ea3f84-4861-4fac-881e-a3213be73771

-- Sol generated from Geometry/PowerSumFactorReveal.lean
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





/-! ## Step 3: the divisibility criterion -/


/-! ## Step 4: the gcd formula -/



/-! ## Theorem 1: the factor reveal -/





open PowerSumReveal in
theorem solution(p N : ℕ) [NeZero p] {k : ℕ} (hk : k ≠ 0)
    (hN : (N : ZMod p) = 0) :
    ((powerSum N k : ℕ) : ZMod p) = ∑ a ∈ range N, (a : ZMod p) ^ k := by
  have hcast : ((powerSum N k : ℕ) : ZMod p) = ∑ a ∈ Finset.Icc 1 N, (a : ZMod p) ^ k := by
    unfold powerSum; push_cast; rfl
  rw [hcast]
  have hins : range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext x; simp only [mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hnot : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have h1 : ∑ a ∈ range (N + 1), (a : ZMod p) ^ k
      = (0 : ZMod p) ^ k + ∑ a ∈ Finset.Icc 1 N, (a : ZMod p) ^ k := by
    rw [hins, Finset.sum_insert hnot]; norm_num
  have h2 : ∑ a ∈ range (N + 1), (a : ZMod p) ^ k
      = ∑ a ∈ range N, (a : ZMod p) ^ k + (N : ZMod p) ^ k := Finset.sum_range_succ _ N
  rw [zero_pow hk, zero_add] at h1
  rw [hN, zero_pow hk, add_zero] at h2
  rw [← h1, h2]
