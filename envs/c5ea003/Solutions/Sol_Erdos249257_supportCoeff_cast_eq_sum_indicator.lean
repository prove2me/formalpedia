-- Prove2me | solution 1 for Erdos249257.supportCoeff_cast_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:02:21.305272+00:00
-- url     : https://prove2.me/submissions/903857cd-ed58-4993-b9fb-58d301eb208f

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
import Definitions.Def_Erdos249257_LcmConeFlatness
import Definitions.Def_Erdos249257_LcmConeNonflat
import Definitions.Def_Erdos249257_SternBrocotRunGeometry
import Definitions.Def_Erdos249257_CertificateKernel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Set
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257
/-! ## Canonical witness selector: universal exact-order witness route

The canonical witness selector reduction, Lean-checked: for every finite
nonempty support `F` of positive exponents, every prime `p` dividing
`L = lcm F` admits a *selector row* — an element of `F` attaining the full
`p`-adic valuation of `L` while being multiple-free inside `F`.  Feeding each
selector row an exact-order prime-power witness (`q ^ s` divides `b ^ m - 1`
exactly when the selected exponent divides `m`) supplies the
`PrimeComponentWitness` valuation deficit, so the finite period-noncollapse
statement follows for the *actual* numerator `A = ∑ (b ^ L - 1) / (b ^ n - 1)`
conditional only on witness supply for the multiple-free rows. -/















/-! ### Concrete route demonstration, including a Zsigmondy exception pair

`F = {1, 2, 3, 6}` over `b = 2` forces the prime-power witness lane: no prime
has multiplicative order `6` for base `2` (the classical Zsigmondy exception
`2 ^ 6 - 1 = 63 = 3 ^ 2 * 7`), while `q ^ s = 3 ^ 2` works. -/





/-! ## Unconditional exact-order witness supply: the cyclotomic route

Zsigmondy's theorem is not needed.  Because the witness interface asks for a
prime *power* `q ^ s` rather than a bare prime, the classical exception pairs
dissolve into a generic construction: any prime divisor `q` of the cyclotomic
value `Φ_n(b)` has `ord_q(b)` equal to the `q`-free part of `n`, and
lifting-the-exponent then chooses `s` so that `q ^ s` sees order exactly `n`.
The Zsigmondy exception families are recovered as instances of the same lift:
`(b, n) = (2, 6)` yields `q ^ s = 3 ^ 2`, and `n = 2` with `b + 1` a power of
two yields `q = 2` with the appropriate `s`. -/











/-! ## The unconditional finite period non-collapse theorem -/











/-! ## Rational-denominator bridge and denominator growth

The unconditional theorem above speaks about `reducedDenominator F b`, a
`Nat`-valued construction.  This section identifies that construction with
`Rat.den` of the literal rational partial sum `∑_{n ∈ F} 1 / (b ^ n - 1)`,
restates the theorem over that denominator, and derives the strict
denominator growth bound `lcm F < den`.  The capstone
`lcm_Icc_lt_den_erdosPartialSum` states the growth bound for the classical
partial sums `∑_{n=1}^{N} 1 / (b ^ n - 1)` in pure Mathlib vocabulary. -/





























/-! ## Infinite bridge: irrationality criterion and first infinite-support instances

The finite theorems above are exact statements about the reduced denominators
of the partial sums.  This section turns that denominator authority into an
irrationality engine for the *infinite* series: the Dirichlet-gap criterion
`irrational_of_den_mul_abs_sub_tendsto_zero` needs exactly an upper bound on
`Rat.den` of the partial sums times the tail, and `den_finiteErdosSum_dvd`
supplies it from the kernel's own common-denominator lattice.  The class
theorem `irrational_erdosSum_of_lcm_gap` proves irrationality of
`∑ 1 / (b ^ (a k) - 1)` for every base `b ≥ 2` whenever the support outruns
the lcm of its own prefix; factorial and geometric supports instantiate it,
giving the first infinite-series irrationality theorems in this development —
including the literal base-2 members of the Erdős #257 statement family.
The universal problem (every infinite support) remains open and is not
claimed. -/

open Filter Topology





















































/-! ## Full-support lane: near-integer criterion and Lambert bridge

The lcm-gap criterion above provably cannot reach the full support
`a k = k + 1`: the closing theorem of this section,
`lcm_gap_hypothesis_fails_full_support`, machine-checks that the prefix lcm
of `{1, …, k}` outruns the next exponent `k + 1`, so the gap hypothesis
fails.  This section therefore opens the second route.
`irrational_of_int_mul_near_int` is the classical integer-dilation
near-integer irrationality criterion — the engine shape behind Erdős's 1948
digit/carry arguments.  `erdosSum_full_support_eq_tsum_divisor_count` is
the Lambert bridge identifying the full-support series `∑ 1 / (b^n - 1)`
with the divisor-count series `∑ τ(m) / b^m` (Mathlib's
`tsum_pow_div_one_sub_eq_tsum_sigma` at `k = 0`, `r = 1/b`), and
`irrational_erdosSum_full_support_of_near_int` reduces full-support
(Erdős–Borwein) irrationality to producing near-integer witnesses for the
divisor-count series — the exact obligation Erdős's 1948 congruence
construction discharges.  Those witnesses are not constructed here:
full-support irrationality is *not* claimed. -/















/-! ## Full-support lane: divisor block certificates

The reduction `irrational_erdosSum_full_support_of_near_int` (above) leaves a
single named obligation: near-integer witnesses for the divisor-count series.
This section factors that obligation into *finite block certificates*.  A
certificate for precision `q` is a tuple `(N, K, L, B)` of naturals with three
finite conditions: a first block `b ^ r ∣ τ (N + r)` for `1 ≤ r ≤ K` (which
makes the leading shifted-tail terms integral), a middle window
`τ (N + r) ≤ B` for `K < r ≤ L`, and one ℕ-arithmetic inequality
`q * (B * b ^ (L - K) + (N + L + 2)) < b ^ L` absorbing the geometric middle
bound and the crude `τ(n) ≤ n` far tail.
`near_int_witness_of_divisor_block_certificate` consumes a certificate and
produces the near-integer witness; `irrational_erdosSum_full_support_of_block_certificates`
closes the loop: certificates for every `q` give full-support irrationality.
`bpow_dvd_card_divisors_of_exact_prime_block` is the multiplicativity hinge
showing the first-block condition is reachable by prescribing exact prime
valuations (Erdős's 1948 congruence construction).  Producing certificates for
every `q` — Erdős's construction itself — is NOT claimed here. -/

















/-! ## Full-support lane: weighted divisor block certificates -/











/-! ## Full-support lane: CRT first-block construction -/









/-! ## Full-support lane: middle-window average and selection -/



















/-! ## Full-support lane: bounded CRT frame and certificate existence -/

























/-! ## Support-coefficient calculus (wave 8)

The full-support theorem `irrational_erdosSum_full_support` is a statement
about the coefficient `τ(n) = n.divisors.card`.  Erdős #257 is a statement
about the coefficient `f_A(n) = #{d ∣ n : d ∈ A}` for an arbitrary support
`A ⊆ ℕ` — the Dirichlet incidence `1_A * 1`.  This section factors the
landed proof into that language: a *generic* weighted-coefficient
certificate engine (any `c : ℕ → ℕ` with `c m ≤ m`), a weighted Lambert
transform, the support coefficient `supportCoeff`, and the support series
`erdosSupportSeries`.  Full support is recovered as the `A = Set.univ`
instance; the multiples supports `A = dℕ` land as the first non-trivial
support classes.  Arbitrary-support Erdős #257 is NOT claimed: for a
general infinite `A`, certificate existence for `supportCoeff A` is an
open obligation, isolated here as an explicit hypothesis. -/



















/-! ## Support-coefficient calculus: the weighted Lambert transform -/





/-! ## Support-coefficient calculus: supportCoeff and erdosSupportSeries -/
end Erdos249257

open Filter Topology
open Erdos249257 in
theorem solution (A : Set ℕ) (n : ℕ) :
    ((supportCoeff A n : ℕ) : ℝ)
      = ∑ e ∈ n.divisors, Set.indicator A (fun _ => (1 : ℝ)) e := by
  classical
  unfold supportCoeff
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : e ∈ A
  · simp [h]
  · simp [h]
