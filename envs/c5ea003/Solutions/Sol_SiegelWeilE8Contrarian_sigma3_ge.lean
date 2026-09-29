-- Prove2me | solution 1 for SiegelWeilE8Contrarian.sigma3_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:18:04.444908+00:00
-- url     : https://prove2.me/submissions/79e5bfd9-4dcd-454e-9122-c55782fd879c

-- Sol generated from Applications/SiegelWeilE8ThetaContrarian.lean
import Mathlib
import Definitions.Def_Applications_SiegelWeilE8ThetaContrarian

/-!
# Contrarian conjectures around the `E₈` / Siegel–Weil theta series

The companion file `SiegelWeilE8Theta.lean` establishes that the `E₈` vector
counts `rE8 n = 240·σ₃(n)` form the coefficient system of the weight-`4` Hecke
eigenform `E₄` (prime-power geometric form, Hecke three-term recurrence,
multiplicativity, and the global Hecke convolution identity).

Following the *contrarian* mandate, this file stress-tests bold conjectures about
that arithmetic system.  We both **prove** several nontrivial structural facts
and **disprove** two natural-looking but false strengthenings.

## Proved

* `sigma3_mod_six` — the congruence `σ₃(n) ≡ σ₁(n) (mod 6)`, a hidden linear
  relation between the weight-`4` and weight-`2` divisor systems, coming from
  `d³ ≡ d (mod 6)`.
* `sigma3_ge_cube` / `sigma3_ge` — the lower bounds `n³ ≤ σ₃(n)` and
  `n³ + 1 ≤ σ₃(n)` for `n ≥ 2`.
* `sigma3_eq_lower_bound_iff_prime` — the lower bound `σ₃(n) = n³ + 1` is attained
  **exactly** at the primes: a characterization of primality via the `E₄`
  Fourier coefficients.
* `rE8_ge_cube` — the E₈ vector count grows at least like `240·n³`.

## Disproved (contrarian counterexamples)

* `rE8_not_multiplicative` — the E₈ count `rE8` is *not* multiplicative; the
  correct coprime law necessarily carries the normalizing factor `240`.
* `hecke_recurrence_composite_fails` — the Hecke three-term recurrence genuinely
  **requires** primality of the base; it fails at `p = 6`.

See `FUTURE_DIRECTIONS.md` for the flagship open target `E₄² = E₈`
(`σ₇(n) = σ₃(n) + 120·∑ σ₃(m)σ₃(n−m)`), verified numerically here.
-/

open SiegelWeilE8Contrarian

open ArithmeticFunction Finset


/-! ### A hidden congruence between σ₃ and σ₁ -/



/-! ### Lower bounds and the prime characterization -/





/-! ### Contrarian disproofs -/



/-! ### Low-order corroboration -/



open SiegelWeilE8Contrarian in
theorem solution(n : ℕ) (hn : 2 ≤ n) : n ^ 3 + 1 ≤ (sigma 3) n := by
  rw [sigma_apply]
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors_self _ (by omega)
  have hpair : ∑ d ∈ ({1, n} : Finset ℕ), d ^ 3 = n ^ 3 + 1 := by
    rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ n)]; ring
  have hle : ∑ d ∈ ({1, n} : Finset ℕ), d ^ 3 ≤ ∑ d ∈ n.divisors, d ^ 3 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
  omega
