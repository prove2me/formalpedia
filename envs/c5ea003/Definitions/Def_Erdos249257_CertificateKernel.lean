-- Prove2me | Definitions.Def_Erdos249257_CertificateKernel
-- name    : Erdos249257_CertificateKernel
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:09:32.352993+00:00
-- url     : https://prove2.me/theorems/22e33036-a539-4191-ad21-f60e7db71b69
-- title:
--   Support divisor coefficient and Erdős reciprocal series
-- statement:
--   This bundle defines supportCoeff(A,n) as the number of divisors of n belonging to A, and erdosSupportSeries(b,A) as the real sum of indicator-restricted reciprocal atoms 1/(b^a−1). Its surrounding source discusses conditional certificate results; these two definitions alone do not assert irrationality.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/CertificateKernel.lean#L1-L19278
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_Erdos249257_TotientTailPeriodKiller
import Definitions.Def_Erdos249257_CarrySurvivorExtinction
import Definitions.Def_Erdos249257_LcmConeFlatness
import Definitions.Def_Erdos249257_LcmConeNonflat
import Definitions.Def_Erdos249257_SternBrocotRunGeometry
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

/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet
incidence `1_A * 1` of a support set `A ⊆ ℕ`.  This is the coefficient
in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1)
= ∑_n f_A(n)/b^n`.  Full support gives `f_ℕ = τ`; primes give `ω`;
prime powers give `Ω`. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card









/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an
indicator series over ℕ.  The `a = 0` term is `1/(1-1) = 0` under real
division-by-zero conventions, so supports containing `0` contribute
nothing spurious. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a











/-! ## Support-coefficient calculus: multiples supports `A = dℕ` -/








/-! ## Support-coefficient calculus (wave 9): carry-aware certificates,
finite-prefix calculus, rational-prefix composition, stray-divisor
calculus, and the ω/Ω coefficient bridge

Wave 8 reduced arbitrary-support Erdős #257 to weighted-certificate
existence for `supportCoeff A`.  This wave repairs the certificate
interface for support families whose coefficients are not `τ`-shaped:

* the first block may be certified **in aggregate** (carry-aware) rather
  than digit-by-digit;
* a support may be **normalised by a finite prefix** per precision, with
  the rational prefix cleared by a `den · b^N` multiplier — necessarily
  so, since `b^a - 1` is coprime to `b` and no `b`-power multiplier can
  clear the prefix denominator;
* stray support divisors are counted by exact finite arithmetic
  (filter splits, reciprocal-tail budgets, and a two-line density bound),
  replacing the `τ`-specific valuation forcing that does NOT transfer;
* prime and prime-power supports are identified with `ω` and `Ω`,
  aligning the calculus with the Erdős #69 / Tao–Teräväinen frontier
  without claiming their analytic input.

None of this claims arbitrary-support certificate existence. -/











/-! ## Finite-prefix calculus: height cuts of a support -/











/-! ## Rational-prefix composition: near-integer witnesses with a
prefix-clearing multiplier -/



/-! ## Stray-divisor calculus: exact finite arithmetic for support
coefficients -/













/-! ## The ω / Ω coefficient bridge: prime and prime-power supports -/









/-! ## Pairwise-coprime supports: Erdős's 1948 partial theorem -/

















/-! ## Support-coefficient calculus: eventually-periodic supports (wave 10)

Erdős #257 for supports whose indicator is eventually periodic.  The engine
is a **periodic divisor-orbit sieve**: if membership in `A` depends only on
the residue mod `m`, and `p` is a prime not dividing `m`, then Euler's
theorem makes the divisor ray `d, pd, p²d, …` sweep residues mod `m` with
period dividing `φ(m)`.  A prime with exact valuation `b·φ(m) - 1` therefore
splits every divisor ray into complete residue cycles repeated a multiple of
`b` times, contributing a clean factor `b` to `supportCoeff A n` — no primes
in arithmetic progressions, no Lambert `q`-series criterion.  The bounded
Bertrand/CRT frame of the full-support lane supplies such primes wholesale:
only the exact-valuation exponent changes, from `b - 1` to `b·φ(m) - 1`. -/





























/-! ## Weighted-coefficient calculus (wave 11): periodic Nat weights and
nonnegative rational periodic Lambert coefficients

Wave 10 proved Erdős #257 for eventually-periodic 0/1 supports through the
periodic divisor-orbit sieve.  This section lifts the sieve from indicator
supports to **multiplicity weights**: a bounded weight `w : ℕ → ℕ` is a
finite stack of indicator layers `χ_i(x) = (i < w x)`, each of which is
`m`-periodic whenever `w` is — so the landed predicate-level orbit theorem
applies layer by layer, and the weighted divisor coefficient
`weightedCoeff w n = ∑_{d ∣ n} w d` inherits the full `b^r` first-block
divisibility with NO new bijection arguments.  Combined with a
linear-growth generalisation of the generic coefficient engine
(`c n ≤ G·n` instead of `c n ≤ n`) and a `w ≤ W`-normalised weighted
Lambert bridge, this closes:

* `irrational_weightedErdosSeries_periodic` — every `m`-periodic Nat
  weight with a positive value has `∑_a w(a)/(b^a - 1)` irrational;
* `irrational_weightedErdosSeries_eventuallyPeriodic` — likewise for
  eventually periodic Nat weights with a positive value in the periodic
  tail;
* `irrational_ratWeightSeries_eventuallyPeriodic` — likewise for
  **nonnegative rational** eventually periodic coefficient sequences, by
  clearing one common denominator over the prefix-plus-period window.

The wave-10 support theorems are the `{0,1}`-valued instances
(`weightedCoeff_indicator_eq_supportCoeff`).  Mixed-sign rational periodic
coefficients (the full Luca–Tachiya statement) are NOT claimed: the
one-sided engine still needs tail positivity.  As the signed-lane socket,
the **one-extra-orbit defect** lemmas
(`weightedCoeff_modEq_of_periodic_extra_orbit`) show that exact valuation
`b·φ(m)` — one slot past the complete Euler cycles — pins the weighted
coefficient mod `b` to its cofactor value: complete cycles give
divisibility, one extra orbit gives a protected residue. -/











/-! ## Weighted-coefficient calculus: the periodic weight toolkit -/







/-! ## Weighted-coefficient calculus: the layer-cake decomposition -/



/-! ## Weighted-coefficient calculus: the layered periodic orbit sieve -/



/-! ## Weighted-coefficient calculus: the one-extra-orbit defect

Complete Euler cycles give divisibility; ONE extra orbit slot gives a
controlled residue.  At exact valuation `b·φ(m)` (instead of
`b·φ(m) - 1`), each divisor ray contributes `b` complete cycles plus a
single copy of its base value, so the whole coefficient is pinned mod `b`
to the coefficient of the cofactor.  This is the protected-residue
primitive the future signed-coefficient lane will consume: it converts
mixed-sign cancellation from an analytic positivity problem into a
finite modular problem.  No signed theorem is claimed here. -/







/-! ## Weighted-coefficient calculus: the linear-growth coefficient engine

The wave-8 generic engine assumed the growth envelope `c m ≤ m` — enough
for `τ` and for support coefficients, but not for weighted coefficients,
which only satisfy `weightedCoeff w n ≤ W·n`.  These are the `G`-linear
generalisations; each delegates its analytic content to the `c = id`
instance of the landed lemma and scales by `G`. -/













/-! ## Weighted-coefficient calculus: the Nat-weight Lambert bridge -/






/-! ## Weighted-coefficient calculus: periodic weight certificate supply -/



/-! ## Weighted-coefficient calculus: the wave-11 theorems -/









/-! ## Signed-coefficient calculus (wave 12): the ℤ-weight engine and the
protected-residue socket

Wave 11 closed nonnegative rational eventually-periodic Lambert
coefficients through the layer-cake orbit sieve and the one-sided
near-integer engine.  Mixed signs destroy exactly one ingredient: the
positive far tail that makes the fractional remainder nonzero.  This
section builds the signed replacement in four unconditional layers and
one explicitly conditional layer.

1. **Signed coefficient algebra.**  `intWeightedCoeff w n = ∑_{d∣n} w d`
   for `w : ℕ → ℤ`, with the `toNat`-part decomposition
   `intWeightedCoeff w = weightedCoeff w⁺ - weightedCoeff w⁻` and the
   `natAbs` growth envelopes.  The decomposition is ALGEBRA ONLY: no
   irrationality statement is ever inferred from the two nonnegative
   parts separately — differences of irrationals can be rational.

2. **Signed orbit layer.**  Complete Euler cycles never needed
   positivity: `b^|P| ∣ intWeightedCoeff w n` at exact valuations
   `b·φ(m) - 1` follows from the Nat theorem on both parts.  The landed
   one-extra-orbit defect is already an ARBITRARY-MODULUS statement (its
   `b` is a bare multiplier), so exact valuation `M·φ(m)` pins
   `intWeightedCoeff w (p^(M·φ(m))·R) ≡ intWeightedCoeff w R [ZMOD M]`
   for every modulus `M` — at `M = b^s` this is an arbitrary-precision
   protected residue, the bridge from "some digit is nonzero" to "a small
   nonzero fractional residue survives".

3. **Seed calculus.**  A minimal-index argument shows base-primitive
   signed weights have divisor coefficients that are nonzero (indeed
   non-divisible by any target modulus) at some positive index, and the
   extra-orbit transport carries that seed residue to infinitely many
   exact-valuation witnesses `p^(M·φ(m))·R`.  Non-cancellation is
   therefore ACHIEVABLE in isolation at every modulus.

4. **Signed certificate consumer.**  A protected-block certificate —
   first-block divisibility except at one protected slot `s`, a known
   nonzero residue `V` mod `b^s` at the protected slot, an absolute
   middle bound, and two inequalities (the protected term dominates the
   noise; everything is below `1/q`) — yields a two-sided near-integer
   witness.  Certificates for every precision give irrationality of the
   signed coefficient series and of the signed weighted Lambert series
   `intWeightedErdosSeries`.

5. **The conditional boundary.**  What is NOT claimed: that periodic
   signed weights possess protected-block certificates.  The frame
   machinery supplies the divisible slots and the middle average exactly
   as in waves 10–11, and the extra-orbit socket pins the protected slot
   to its cofactor coefficient mod `b^s` — but the cofactor `R` of a CRT
   progression slot is arithmetically uncontrolled, so `V ≠ 0` is an open
   supply obligation ("cofactor non-cancellation").  The two live
   branches are (a) a selection argument over the frame progression with
   arbitrary primes, or (b) a bounded prime-in-arithmetic-progression
   supply in the style of Luca–Tachiya's proof; qualitative Dirichlet is
   NOT enough, because the certificate arithmetic needs the selected slot
   inside a bounded window.  The unconditional mixed-sign rational
   periodic coefficient theorem (full Luca–Tachiya) remains a
   NON-CLAIM. -/













/-! ## Signed-coefficient calculus: the signed periodic orbit layer -/









/-! ## Signed-coefficient calculus: the seed calculus

Non-cancellation seeds: a signed weight that is not everywhere divisible
by the target modulus has a divisor coefficient that is not divisible by
it either — at the MINIMAL such index, because all proper divisors sit
below the minimum.  The extra-orbit transport then carries the seed
residue to exact-valuation witnesses at every modulus.  These lemmas show
the protected residue exists in isolation; steering the CERTIFICATE FRAME
onto such a witness is exactly the open supply obligation. -/









/-! ## Signed-coefficient calculus: the signed analysis layer

The analytic lemmas of the linear-growth engine, lifted to `ℤ`-valued
coefficients under the ABSOLUTE growth envelope `|c n| ≤ G·n`.  Each
delegates its content to the `natAbs` instance of the landed Nat lemma;
signs only pass through `summable_abs_iff` and triangle inequalities. -/











/-! ## Signed-coefficient calculus: the protected-block certificate
consumer -/







/-! ## Signed-coefficient calculus: the signed weighted Lambert bridge -/









/-! ## Signed-coefficient calculus: the wave-13 dichotomy engine

The wave-12 protected slot exists to certify a NONZERO fractional
residue.  Wave 13 records the reduction that makes most of that
machinery unnecessary: a rational number `x` whose base-`b` dilations
`b^N·x` are never integers keeps every `b^N·x` at distance `≥ 1/den(x)`
from `ℤ`, so a FULL-divisibility certificate (every first-block slot
divisible, no protected slot, no positivity, no nonzero residue) at
precision `q = den(x)` already contradicts rationality.  The
full-block certificate supply is the landed periodic frame machinery
verbatim — positivity was only ever consumed by the far-tail witness,
and the protected slot only ever excluded the single remaining escape:
`x` a base-`b` TERMINATING rational `z/b^k`.

Consequence, unconditional for EVERY `m`-periodic signed integer
weight: `∑ w(a)/(b^a−1)` is irrational OR equals `z/b^k` for some
`z, k`.  The mixed-sign obligation shrinks from protected-certificate
supply at every precision to the single non-termination question.

The companion lemma
`intWeightedCoeff_periodFourSignWeight_eq_zero_of_mod_four_eq_three`
records why the certificate frame CANNOT be steered onto nonzero
cofactor residues by residue selection alone: for the period-4 sign
weight `1, 0, −1, 0` the divisor involution `d ↦ n/d` pairs opposite
signs on every `n ≡ 3 mod 4`, so the signed coefficient vanishes
IDENTICALLY on that residue class — zero sets of periodic signed
coefficients can contain full arithmetic progressions.  Non-termination
for general periodic signed weights therefore remains the honest open
frontier; it is NOT claimed here. -/

















/-! ## Signed-coefficient calculus: closing the terminating escape for
coefficient-nonnegative weights (wave 13b)

The wave-13 dichotomy leaves exactly one escape: the series could be a
base-`b` terminating rational `z₀/b^k`.  For weights whose divisor
COEFFICIENTS are nonnegative (the weights themselves may be mixed-sign
— the period-4 character-type weights are the motivating class), that
escape closes unconditionally:

* a terminating value keeps every dilation `b^N·x` either exactly an
  integer or at distance `≥ 1/b^k` from `ℤ`, so a full-block
  certificate at precision `q = b^k + 1` forces `b^N·x` to BE the
  integer it approximates;
* an exact integer value makes the post-block tail an integer in
  `[0, 1)`, hence ZERO — and a vanishing sum of nonnegative terms
  vanishes term by term, so EVERY coefficient beyond the first block
  is zero;
* that contradicts "infinitely many nonzero coefficients".

Result: `∑ w(a)/(b^a − 1)` is irrational for every `m`-periodic signed
weight with nonnegative (or nonpositive) divisor coefficients that do
not eventually vanish.  This strictly extends the wave-11 nonnegative
WEIGHT theorem: coefficient-nonnegativity tolerates sign-mixed weights.
The fully mixed-sign case (coefficients of both signs) remains open and
is NOT claimed. -/













/-! ## Erdős #249 lane: totient coefficient sockets and first-block supply (wave 14)

Erdős #249 asks whether `∑_{n≥1} φ(n)/2^n` is irrational.  It is the
coefficient-series instance `b = 2`, `c = Nat.totient` of the wave-8
engine: growth `φ(m) ≤ m` is `Nat.totient_le`, tail positivity is
`Nat.totient_pos`, and both the digitwise and the carry-aware consumers
apply verbatim.  This lane lands the two unconditional halves that exist
today and names the missing third:

* **Hinge (landed):** every odd prime divisor `p` of `n` contributes the
  even factor `p - 1` to Euler's product, so a block of `r` distinct odd
  prime divisors forces `2^r ∣ φ(n)`.  No exact valuation is needed.
* **First-block supply (landed):** the exact-valuation CRT progression at
  base `2`, prime floor `2` gives `2^r ∣ φ(x + y·A + r)` along a full
  arithmetic progression.
* **Certificate supply (MISSING — the open content of #249):** the `τ`
  middle window closed because divisor counts average polylogarithmically
  along the frame, so the pigeonhole selector
  (`selected_weighted_middle_of_supported_frame`) crushes the middle mass
  far below `N`.  `φ` has linear average: any middle window after a
  depth-`K` first block carries mass on the order of `N·2^(L-K)`, so the
  height inequality `q·(C + N + L + 2) < 2^L` forces roughly `q·N < 2^K`.
  But every window-local route to `2^r ∣ φ(N+r)` for all `r ≤ K` costs a
  CRT modulus of size `2^Ω(K²)` — `r` odd primes per slot here, or one
  prime `≡ 1 (mod 2^r)` per slot on Linnik-type input — hence
  `N ≥ 2^Ω(K²) ≫ 2^K` and the height inequality cannot close; emptying
  the middle (`K = L`) meets the same wall.  Producing certificates
  therefore needs input beyond window-local divisibility forcing (for
  example counting or equidistribution of the carry sum
  `∑_{r≤K} φ(N+r)·2^(K-r) mod 2^K` at height `N ≈ 2^K/q`), which is not
  claimed here.  Runner non-claims: `not_erdos_249_solution`,
  `not_totient_block_certificate_supply`,
  `not_totient_carry_certificate_supply`. -/











/-! ## Erdős #249 lane, wave 15: low-carry residue-band certificates

Wave 14 shaped the carry-aware socket around **exact** first-block
integrality: `2^K ∣ ∑_{r≤K} φ(N+r)·2^(K-r)`.  That demand is an
artefact of the digitwise ancestry, not of the near-integer criterion:
irrationality needs a positive fractional part **below `1/q`**, not a
zero one.  This wave weakens the certificate interface so the first
block may leave the residue `V = carrySum % b^K`, absorbed by the
height inequality `q·(V·b^(L-K) + C + (N+L+2)) < b^L`.  Exact carry is
the `V = 0` special case (machine-checked below via
`irrational_coeff_series_of_carry_via_low_carry`), so the supply target
widens from ONE congruence class mod `2^K` to a band of ≈ `2^K/q`
residues — exponentially wider once `K` exceeds `2·log₂ q`.
Certificate SUPPLY remains the open content of #249 and is NOT claimed:
runner non-claims `not_erdos_249_solution`,
`not_totient_low_carry_certificate_supply`. -/












/-! ## Erdős #249 lane, wave 16: carry-field recurrences, top-band transfer,
and machine-checked denominator exclusion

The residue field `V_K(N) = (∑_{r≤K} φ(N+r)·2^(K-r)) % 2^K` advances by the
same affine doubling map in both lattice directions: `V_K(N+1) =
(2·V_K(N) + φ(N+K+1)) % 2^K` (shift) and `V_{K+1}(N) = (2·V_K(N) +
φ(N+K+1)) % 2^(K+1)` (window).  Consequently the open low-band supply
obligation is exactly a carry-out event of the K-climb: whenever the
residue enters the top band — `2^(K+1) ≤ 2·V_K + φ(N+K+1)` — the next
window's residue drops below `φ(N+K+1)`
(`totient_carry_residue_top_band_step`), and that event yields a full
low-carry certificate whenever `q·(φ(N+K+1) + N+(K+1)+2) ≤ 2^(K+1)`
(`totient_low_carry_full_block_certificate_of_top_band`).

The per-`q` slice of the open supply is machine-checkable: one concrete
certificate at `q` denies every rational representation `a/q`
(`coeff_series_shifted_ne_int_div_of_low_carry_certificate`) and
transports down the whole denominator ladder
(`totient_low_carry_full_block_certificate_mono`).  This wave lands a
concrete certificate at `q = 4838` (window `N = 763`, `K = 34`, every
window totient certified by its prime factorization), so it is kernel
truth that `∑_{n≥0} φ(n)/2^n` has no rational representation with
denominator ≤ 4838 — the first unconditional statement about the #249
constant itself.  The ∀q supply — full #249 — remains OPEN and is NOT
claimed: runner non-claims `not_erdos_249_solution`,
`not_totient_low_carry_certificate_supply`,
`not_denominator_exclusion_beyond_verified_instance_ladder`. -/
































































/-! ### Wave 17 — gap-certificate engine and bulk denominator exclusion

**The gap reframe.**  Rationality `Σ = a/q` forces `q·F_N ∈ ℤ` at every
shift `N`, pinning the scaled tail to the integer lattice.  The wave-16
engine refuted a denominator only from the bottom band — residue
`V_K(N)` inside `(0, 2^K/q)`, a `1/q`-rare event that drove the witness
scout to `N ≈ 3×10^8` and into the large-totient kernel-recursion trap.
But landing strictly inside ANY consecutive-integer gap `(j, j+1)` after
scaling by `q` is an equal refutation: with `W = (q·V_K(N)) mod 2^K`, the
single inequality `W + q·(N+K+2) < 2^K` — avoid one thin TOP band — is a
full certificate (`strict_between_int_witness_of_weighted_coeff_gap_certificate`;
the landed low-carry certificate is exactly the `j = 0` case,
`totient_gap_certificate_of_low_carry_certificate`).  For
`2^K ≳ q²·(N+K)` essentially every window certifies every `q`, so `N = 1`
suffices and every window totient stays tiny (≤ 112 here): the
kernel-recursion ceiling that capped wave 16 at denominator 4838 is
gone, not merely raised.

**Bulk verification.**  One kernel-computed run of an unrolled
binary-splitting checker (`totient_gap_row_window_1_120` /
`totient_gap_check_window_1_120_pow_*`, recursion depth 22, ordinary
`Decidable` kernel evaluation via `decide +kernel` — no compiler-trusted
reflection, no new axioms) certifies the gap inequality for every
`q ≤ 2^22 = 4194304` at the single window `(N, K) = (1, 120)`;
per-level soundness lemmas convert the run into per-`q` theorems.
Headline: `∑_{n≥0} φ(n)/2^n` has no rational representation with
denominator ≤ 4194304 — wave 16's 4838, and the previously unreachable
empirical champion target 50357951, both fall out of one tiny window.

**What remains open (NOT claimed).**  The `∀q` gap supply — for every `q`
one window avoiding its thin top band — would close Erdős #249
(`irrational_tsum_totient_div_pow_two_of_gap_certificate_supply`).  Under
the rationality hypothesis the top-band deficit obeys the same expanding
shadow dynamics `s ↦ 2s − q·φ` as the residue field, so no unconditional
contradiction is available without new analytic input on totient carry
sums; the supply, and #249 itself, remain open.  Runner non-claims:
`not_erdos_249_solution`, `not_totient_gap_certificate_supply`,
`not_denominator_exclusion_beyond_verified_instance_ladder`. -/






























































































































































































































































































































































































































































































































































































































/-! ## Wave 18: the Mersenne–Lambert ladder — where the #249 constant lives

`L(f) = ∑_{n≥1} f(n)/(2ⁿ-1)` places `S = ∑ φ(n)/2ⁿ` in a one-parameter
family of Lambert values indexed by Dirichlet convolution:

* `L(μ) = 1/2` and `L(φ) = 2` — EXACTLY rational (machine-checked below);
* `L(1) = E`, the Erdős–Borwein constant — IRRATIONAL
  (`irrational_erdosBorwein_series`, machine-checked in this kernel);
* `L(A) = S` for the nonnegative primitive-conductor weight `A = φ * μ`
  (`A(n)` counts primitive Dirichlet characters of conductor `n`) — OPEN;
  this IS Erdős #249, now in positive Erdős–Borwein form, and it inherits
  the wave-17.5 record: no denominator `≤ 7.96×10³⁴`;
* `L(Id) = ∑ σ(m)/2^m` — transcendental by Nesterenko 1996 via `E₂(1/2)`
  (cited, not formalised).

One convolution by `ζ` (`A * ζ = φ`) separates the open constant from a
rational; one more (`φ * ζ = Id`) separates rational from transcendental.
The bodies live in `MersenneLambertLadder`; these kernel restatements bind
them to the literal #249 series shape and to the Farey-gap record bound.
No irrationality of `S` is claimed; the ladder relocates the problem, it
does not solve it. -/

















/-! ## Wave 19: geometric coprimality — the #249 constant as visible-lattice mass

Let `X` be the fair-coin waiting time (`P(X = n) = 2⁻ⁿ`, `n ≥ 1`).  Then
`P(d ∣ X) = 1/(2ᵈ-1)`, so the wave-18 Mersenne–Lambert ladder is the divisor
calculus of `X`: `L(f) = ∑ f(d)/(2ᵈ-1) = E[(f * ζ)(X)]`, and the rungs read

* `L(μ) = 1/2 = P(X = 1)`,
* `L(φ) = 2   = E[X]`,
* `L(1) = E   = E[τ(X)]`  (Erdős–Borwein; irrational, this kernel),
* `L(A) = S   = E[φ(X)]`  — OPEN; this IS #249.

This wave adds the two-variable coordinate (bodies in `GeometricCoprimality`):
`φ(n)` counts the visible lattice points `(a, b)`, `a + b = n`, `0 < a`,
`gcd(a,b) = 1` — uniformly in `n`, no case split — so the #249 constant is
itself a coprime-pair mass, and

  `S - 1/2 = ∑_{(a,b) coprime, a,b ≥ 1} 2^{-(a+b)} = P(gcd(X,Y) = 1)`

for independent fair-coin waiting times `X, Y` (base 2 is the unique point
where `P(X = a)·P(Y = b) = 2^{-(a+b)}` with no normalizing constant).  Erdős
#249 asks whether this coprimality probability is irrational.  The gcd-layer
theorem closes the picture: `∑_{g≥1} P(gcd(X,Y) = g) = 1` exactly — the
probabilistic content of the rational rung `L(φ) = 2` — and the wave-17.5
Farey record transfers: `P(gcd(X,Y) = 1)` has no rational representation with
denominator `≤ 3.98×10³⁴`.  No irrationality of `S` is claimed; the coordinate
change relocates #249 onto the visible lattice, it does not solve it. -/











/-! ## Wave 20: the squared Lambert transform — gcd moments and Stern–Brocot cylinders

Wave 19 made `S - 1/2 = P(gcd(X,Y) = 1)` the open atom of an exactly-normalized
distribution.  This wave lands the calculus that distribution carries.  The
foundation stone is the divisibility factorization

  `P(d ∣ gcd(X,Y)) = P(d ∣ X)·P(d ∣ Y) = 1/(2ᵈ-1)²`,

so the SQUARED Lambert transform `L₂(f) = ∑ f(d)/(2ᵈ-1)² = E[(f * ζ)(gcd)]`
is the two-variable ladder (bodies in `GcdMomentCalculus`):

* `L₂(μ) = S - 1/2 = P(gcd = 1)`          — the OPEN #249 atom (wave 18's
  Möbius-square lens `tsum_totient_half_pow_eq_half_add_moebius_sq`),
* `L₂(1) = ∑ (σ(n)-τ(n))/2ⁿ = E[τ(gcd)]`  — the q-zeta anchor
  `ζ_q(2) - ζ_q(1)` at `q = 1/2`; irrational by Postelmans–Van Assche q-Padé
  (cited, NOT formalised — the identity is machine-checked here),
* `L₂(φ) = ∑ (P(n)-n)/2ⁿ = E[gcd(X,Y)]`   — `P = φ * Id` is Pillai's gcd-sum.

The MIRROR: at level 1, `L(μ) = 1/2` is trivial and `L(1) = E` is the hard
irrational (Erdős 1948); at level 2, `L₂(1)` is the known irrational (q-Padé)
and `L₂(μ)` IS #249.  Möbius projection is the single remaining wall, at both
levels.  The reduced-direction law `∑_{(a,b)=1} 1/(2^{a+b}-1) = 1` and the
Stern–Brocot cylinder closed form `M(a,b) = 1/((2ᵃ-1)(2ᵇ-1)) = P(a∣X)·P(b∣Y)`
(exact mediant telescoping + `(2/3)ᵈ`-rate limit) give the cylinder topology a
cusp-isolation attack would consume: all-left cusps `(N,1)` have mass
`1/(2ᴺ-1)` — near-Mersenne reciprocals, one exponential order closer to the
Erdős–Borwein engine than the raw totient coefficients.  No irrationality of
`S` is claimed; #249 remains open. -/













/-! ## Induced Stern–Brocot runs: Fibonacci pressure and the denominator knife-edge

Raw tree depth has parabolic cusp branches of only linear height.  Grouping
maximal same-direction runs exposes the correct unconditional scale: an
alternating word with `r` nonempty runs has height at least `F_{r+3}`, with
equality on the all-unit spine.  The run continuant below is tied back to the
literal mediant word, not asserted as an independent coordinate.

The natural invariant-coordinate exponents along that spine sum to
`F_{r+3}-2`.  Thus run induction creates Fibonacci analytic pressure but the
naive Mersenne clearing cost lies on the same exponential scale.  These facts
do not supply a denominator surplus and do not prove #249; they isolate the
arithmetic obligation any external cocycle or period identity must beat.
-/















/-! ## Wave 21: the totient-tail period killer — rationality itself is the enemy

Every earlier wave attacked digits (force a zero corridor); wave 20 measured why
that fails (`√log` affordance vs `log` need).  Wave 21 attacks the PERIOD:
rationality of `S` forces the local totient tail `R_N = ∑_{j≥1} φ(N+j)/2ʲ` to
obey `R_{N+h} - R_N ∈ ℤ` eventually (tail-period law), and killing one `(h, N)`
is a finite decidable residue certificate with forbidden zone `O(N)` inside
modulus `2^L ≈ N³` — the proof no longer has to HIT a measure-zero target, only
MISS a vanishing one.  The reduction is complete: a certified kill supply at
every scale proves #249.  Proof bodies: `TotientTailPeriodKiller.lean`. -/













/-! ## Wave 22: carry-survivor extinction and the multiple-period collapse

Rationality gives more than the wave-21 socket spent: if `h₀` is an eventual
binary period, every multiple `m·h₀` is one too (pure telescoping), so the
supply obligation collapses from ∀h to one kill per divisibility ray — and
further onto the single ℕ-indexed family `lcm(1..t)`.  And the bounded-orbit
reformulation is now kernel-checked: an integer tail difference launches an
exact integer carry orbit trapped in a linear strip; the decidable survivor
certificate verifies every candidate escapes.  Proof bodies:
`CarrySurvivorExtinction.lean`. -/



















/-! ## Wave 23: the diagonal lcm collapse and the lcm-ray window structure

Wave 22 collapsed the supply throat onto the one-parameter period family
`lcm(1..t)` but left the position `N` free.  Wave 23 removes the second
parameter: standing AT the ray point `N = lcm(1..t)` still beats every
hypothetical rational — any `t ≥ max(h₀, N₀)` satisfies `h₀ ∣ lcm(1..t)` and
`lcm(1..t) ≥ t ≥ N₀` simultaneously — so #249 follows from a SINGLE ℕ-indexed
sequence of decidable statements `P t := ∃ L, certifiedKill(lcm(1..t),
lcm(1..t), L)` holding for infinitely many `t`.  Below `2t` every window
index divides the period except bare prime powers in `(t, 2t)`, and clean
divisors split the window totient exactly — the first coordinates in which
the open supply is structured arithmetic rather than totient noise.  Proof
bodies: `LcmDiagonalReduction.lean`. -/















/-! ## Wave 24: the lcm-cone flatness law and the annihilator calculus

Wave 23 stood at one diagonal cell of the lcm lattice.  Wave 24 spends the
rationality hypothesis all the way: rationality forces ONE fractional
constant on the entire lcm cone `{k·lcm(1..t) : k ≥ 1}`, so every cone
difference is forced integral — and one certified annihilator anywhere on
the cone at arbitrarily large scale proves #249.  The diagonal, all q-ray
steps, q-gaps, and the prime-jump pairs `lcm(1..t+1) - lcm(1..t)` are cells
of ONE supply theorem.  The endpoint certificate is also proved COMPLETE
(kills exist exactly at non-integers), so the frontier now reads in pure
non-integrality form.  Rank-2 second-difference certificates land sound,
with the measured verdict (probe v2: shadow cancelled, kills NOT shallower)
kernel-checked at a fixture cell.  Proof bodies: `LcmConeFlatness.lean`. -/























/-! ## Wave 25: the cone non-flatness refuter — killing the menu, not the pair

Wave 24 flattened the whole lcm cone under rationality; every certificate
still interrogated flatness through one PAIR of cone points.  Wave 25
interrogates a finite MENU of cone vertices at once: each vertex pins
`2^L·R_{q·H}` inside a one-sided arc of radius `q·H+L+2`, joint flatness
forces a common point of all the arcs, and `coneNonflatCert` refutes every
candidate common point with `|Q|²` one-sided endpoint checks (argmin lemma:
the vertex of minimal deep tail would be a common left endpoint).  Each arc
charges only its OWN one-sided radius — `certifiedKill` charges the top
vertex's radius on both sides — so the menu floor is HALF the pairwise
floor: strict depth wins are kernel-checked below, including a genuinely
JOINT cell (`t = 8`, menu `[1,2,3,4]`, depth `12` — at floor, slack zero)
where the menu is inconsistent while every pair alone stays consistent.
The lcm-jump lane is named as a supply theorem with no side conditions.
Proof bodies: `LcmConeNonflat.lean`. -/













/-! ## Wave 27: exactness and depth-monotonicity of the menu refuter

Wave 26 measured the fixed-menu advisory mechanism dead (limit-shape
endpoint model refuted at every tested scale) while the firing
observations survived; what earns kernel status this wave is the exact
calculus those measurements ran on.  The probe gate "certificate fires iff
no common point exists" and the depth law behind `nonflat_L_min` are now
theorems: a purely combinatorial argmin (no analytic tails), the window
recursion `P_{L+1} = 2·P_L + φ(M+L+1)`, and a halving descent for common
points.  Consequence: a firing certificate fires at EVERY deeper depth
(floors held), so `∃L` in any supply statement collapses onto canonical
large-enough depths and `nonflat_L_min` is THE firing threshold.
Proof bodies: `LcmConeNonflat.lean`. -/











end Erdos249257


