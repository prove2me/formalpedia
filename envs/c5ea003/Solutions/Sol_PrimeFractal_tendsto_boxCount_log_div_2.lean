-- Prove2me | solution 2 for PrimeFractal.tendsto_boxCount_log_div
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T19:02:50.961342+00:00
-- url     : https://prove2.me/submissions/e0c8b85d-0331-4257-b6d2-0d475b086d21

import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalHausdorff

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Catalog/NumberTheory/PrimeFractalChebyshev.lean ====
/-!
# A Chebyshev-type lower bound for the prime counting function

This file proves an explicit elementary (Chebyshev-style) lower bound

  `n ≤ 8 * π n * log n`   for `n ≥ 8`,

where `π = Nat.primeCounting`.  Mathlib contains Chebyshev's *upper* bound
(`Chebyshev.eventually_primeCounting_le`); here we derive a lower bound from the
central binomial coefficient, following the classical argument

  `4 ^ n < n * centralBinom n ≤ n * (2n) ^ π (2n)`.

The bound is used in `NumberTheory.PrimeFractalBoxDimension` to show that the
box-counting dimension of the "prime fractal" is exactly `1`.
-/

namespace PrimeFractal

open Finset

/-- The central binomial coefficient is a product of prime powers, each at most `2n`,
and there are `π (2n)` primes involved; hence `centralBinom n ≤ (2n) ^ π (2n)`. -/
theorem centralBinom_le_pow_primeCounting (n : ℕ) (hn : 0 < n) :
    n.centralBinom ≤ (2 * n) ^ (Nat.primeCounting (2 * n)) := by
  have hsub : Nat.primesBelow (2 * n + 1) ⊆ Finset.range (2 * n + 1) := by
    intro p hp
    exact Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp)
  have hprod : ∏ p ∈ Nat.primesBelow (2 * n + 1), p ^ (n.centralBinom.factorization p)
      = n.centralBinom := by
    have hstep : ∏ p ∈ Nat.primesBelow (2 * n + 1), p ^ (n.centralBinom.factorization p)
        = ∏ p ∈ Finset.range (2 * n + 1), p ^ (n.centralBinom.factorization p) := by
      refine Finset.prod_subset (f := fun p => p ^ (n.centralBinom.factorization p)) hsub ?_
      intro p hp hnp
      have hnotprime : ¬ Nat.Prime p := by
        intro hpp
        exact hnp (Nat.mem_primesBelow.mpr ⟨Finset.mem_range.mp hp, hpp⟩)
      show p ^ (n.centralBinom.factorization p) = 1
      rw [Nat.factorization_eq_zero_of_not_prime _ hnotprime, pow_zero]
    rw [hstep, Nat.prod_pow_factorization_centralBinom n]
  have hcard : (Nat.primesBelow (2 * n + 1)).card = Nat.primeCounting (2 * n) := by
    rw [Nat.primesBelow_card_eq_primeCounting']
    simpa using (Nat.primeCounting_sub_one (2 * n + 1)).symm
  calc n.centralBinom
      = ∏ p ∈ Nat.primesBelow (2 * n + 1), p ^ (n.centralBinom.factorization p) := hprod.symm
    _ ≤ ∏ _p ∈ Nat.primesBelow (2 * n + 1), (2 * n) := by
          refine Finset.prod_le_prod' ?_
          intro p _
          exact Nat.pow_factorization_choose_le (by positivity)
    _ = (2 * n) ^ (Nat.primeCounting (2 * n)) := by rw [Finset.prod_const, hcard]

/-- Logarithmic form of the central binomial bound. -/
theorem log_four_le (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 ≤
      Real.log n + (Nat.primeCounting (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) := by
  have hn0 : 0 < n := by omega
  have h1 : (4 : ℕ) ^ n ≤ n * n.centralBinom := (Nat.four_pow_lt_mul_centralBinom n hn).le
  have h2 : n * n.centralBinom ≤ n * (2 * n) ^ (Nat.primeCounting (2 * n)) :=
    Nat.mul_le_mul_left _ (centralBinom_le_pow_primeCounting n hn0)
  have h3 : (4 : ℕ) ^ n ≤ n * (2 * n) ^ (Nat.primeCounting (2 * n)) := le_trans h1 h2
  have h3' : (4 : ℝ) ^ n ≤ (n : ℝ) * (2 * (n : ℝ)) ^ (Nat.primeCounting (2 * n)) := by
    have := (Nat.cast_le (α := ℝ)).mpr h3
    push_cast at this
    exact this
  have hpos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hlog := Real.log_le_log hpos h3'
  rw [Real.log_pow] at hlog
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  linarith [hlog]

/-- **Chebyshev-type lower bound.** For `n ≥ 8` we have `n ≤ 8 * π n * log n`,
i.e. `π n ≥ n / (8 log n)`. -/
theorem le_primeCounting_mul_log (n : ℕ) (hn : 8 ≤ n) :
    (n : ℝ) ≤ 8 * (Nat.primeCounting n : ℝ) * Real.log n := by
  -- the even case, with the better constant `4`
  have even_case : ∀ k : ℕ, 4 ≤ k → 2 * (k : ℝ) ≤
      4 * (Nat.primeCounting (2 * k) : ℝ) * Real.log (2 * (k : ℝ)) := by
    intro k hk
    have hbase := log_four_le k hk
    have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hlogk : Real.log k ≤ Real.log (2 * (k : ℝ)) := by
      apply Real.log_le_log hk0
      linarith
    have hpi1 : 1 ≤ Nat.primeCounting (2 * k) := by
      rcases Nat.eq_zero_or_pos (Nat.primeCounting (2 * k)) with h | h
      · rw [Nat.primeCounting_eq_zero_iff] at h; omega
      · exact h
    have hpi1' : (1 : ℝ) ≤ (Nat.primeCounting (2 * k) : ℝ) := by exact_mod_cast hpi1
    have hlogpos : 0 < Real.log (2 * (k : ℝ)) := Real.log_pos (by linarith)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    -- `log k ≤ π(2k) * log (2k)`
    have hstep : Real.log k ≤ (Nat.primeCounting (2 * k) : ℝ) * Real.log (2 * (k : ℝ)) := by
      nlinarith [hlogpos, hpi1', hlogk]
    nlinarith [hbase, hstep, hlogpos, hlog2, hk0]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hk' : n = 2 * k := by omega
    have hk4 : 4 ≤ k := by omega
    have h1 := even_case k hk4
    have hnk : (n : ℝ) = 2 * (k : ℝ) := by rw [hk']; push_cast; ring
    have hpc : Nat.primeCounting n = Nat.primeCounting (2 * k) := by rw [hk']
    rw [← hnk, ← hpc] at h1
    have hpi : (0 : ℝ) ≤ (Nat.primeCounting n : ℝ) := by positivity
    have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    nlinarith [h1]
  · -- odd case: pass to `n - 1`
    obtain ⟨j, hj⟩ := ho
    have hn9 : 9 ≤ n := by omega
    have hk4 : 4 ≤ j := by omega
    have h1 := even_case j hk4
    have hcast : (n : ℝ) - 1 = 2 * (j : ℝ) := by
      have : (n : ℝ) = 2 * (j : ℝ) + 1 := by rw [hj]; push_cast; ring
      linarith
    have hpc : Nat.primeCounting (n - 1) = Nat.primeCounting (2 * j) := by
      congr 1; omega
    rw [← hcast, ← hpc] at h1
    have hmono : Nat.primeCounting (n - 1) ≤ Nat.primeCounting n :=
      Nat.monotone_primeCounting (by omega)
    have hmono' : (Nat.primeCounting (n - 1) : ℝ) ≤ (Nat.primeCounting n : ℝ) := by
      exact_mod_cast hmono
    have hn9' : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn9
    have hlogle : Real.log ((n : ℝ) - 1) ≤ Real.log n :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogpos : 0 < Real.log ((n : ℝ) - 1) := Real.log_pos (by linarith)
    have hpi0 : (0 : ℝ) ≤ (Nat.primeCounting (n - 1) : ℝ) := by positivity
    have hchain : 4 * (Nat.primeCounting (n - 1) : ℝ) * Real.log ((n : ℝ) - 1)
        ≤ 4 * (Nat.primeCounting n : ℝ) * Real.log n := by
      nlinarith [hmono', hlogle, hlogpos, hpi0]
    linarith [h1, hchain]

end PrimeFractal
-- ==== upstream: Catalog/NumberTheory/PrimeFractalHausdorff.lean ====
/-!
# The "prime fractal": Hausdorff dimension and total length

We study the set of primes equipped with the metric

  `d p q = |1 / log p - 1 / log q|`,

as proposed in the research mission.  Concretely, the map
`logInv p = 1 / Real.log p` embeds the primes into `ℝ` and, by `Real.dist_eq`,
the metric induced from `ℝ` is exactly `d`.  We call the image the
*prime fractal* `primeFractal ⊆ ℝ`.

## Main results

* `logInv_injOn_prime` — `logInv` is injective on the primes, so
  `(primes, d)` is isometric to `primeFractal` with the euclidean metric.
* `dimH_primeFractal` — `dimH primeFractal = 0`.  **This refutes the mission
  conjecture `dimH = 1`, and a fortiori the conjecture `dimH = 1 + ε` with
  `ε > 0` measuring twin primes.**  The reason is soft but decisive: the primes
  are countable, and every countable subset of a metric space has Hausdorff
  dimension `0`.
* `dimH_subFractal` — the same holds for *every* subfamily of primes (twin
  primes, Sophie Germain primes, ...): the twin prime conjecture cannot change
  the Hausdorff dimension.
* `primeFractal_length_eq` / `tendsto_primeFractal_length` — the total
  `d`-length of the primes is *finite*, equal to `1 / log 2`.  The mission's
  heuristic ("the length is `∑ 1/(p log p) ∼ log log x`, which diverges") is
  therefore false twice over: the sum telescopes, and `∑ 1/(p log p)`
  converges anyway.
* `isCompact_insert_zero_primeFractal`, `dimH_closure_primeFractal` — the
  closure of the prime fractal is the compact set `{0} ∪ primeFractal`, and it
  still has Hausdorff dimension `0`.

The positive counterpart (the *box-counting* dimension really is `1`) is in
`NumberTheory.PrimeFractalBoxDimension`.
-/

namespace PrimeFractal

open Filter Topology

-- [dropped: platform already declares logInv]
-- [dropped: platform already declares primeFractal]
theorem dist_logInv (p q : ℕ) :
    dist (logInv p) (logInv q) = |1 / Real.log p - 1 / Real.log q| :=
  Real.dist_eq _ _

theorem logInv_pos {p : ℕ} (hp : p.Prime) : 0 < logInv p := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have : 0 < Real.log p := Real.log_pos (by linarith)
  simpa [logInv] using one_div_pos.mpr this

/-- `logInv` is strictly antitone on integers `≥ 2`. -/
theorem logInv_lt_logInv {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) : logInv q < logInv p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpq' : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlq : Real.log p < Real.log q := Real.log_lt_log (by linarith) hpq'
  exact one_div_lt_one_div_of_lt hlp hlq

/-- `logInv` is injective on the set of primes: the prime fractal faithfully
records the primes. -/
theorem logInv_injOn_prime : Set.InjOn logInv {p : ℕ | p.Prime} := by
  intro p hp q hq hpq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt := logInv_lt_logInv hp.two_le h
    rw [hpq] at hlt
    exact lt_irrefl _ hlt
  · have hlt := logInv_lt_logInv hq.two_le h
    rw [hpq] at hlt
    exact lt_irrefl _ hlt

theorem primeFractal_countable : primeFractal.Countable :=
  (Set.to_countable _).image _

/-- **Refutation of the mission conjecture.** The Hausdorff dimension of the prime
fractal is `0`, not `1` (and not `1 + ε`). -/
theorem dimH_primeFractal : dimH primeFractal = 0 :=
  primeFractal_countable.dimH_zero

theorem dimH_primeFractal_ne_one : dimH primeFractal ≠ 1 := by
  rw [dimH_primeFractal]; simp

/-- No `ε`, however small, can appear: `dimH = 1 + ε` is impossible. -/
theorem not_exists_dimH_eq_one_add : ¬ ∃ ε : ENNReal, dimH primeFractal = 1 + ε := by
  rintro ⟨ε, hε⟩
  rw [dimH_primeFractal] at hε
  have : (1 : ENNReal) ≤ 1 + ε := le_self_add
  rw [← hε] at this
  simp at this

/-- **The twin primes cannot help.** Any subfamily of the primes — the twin
primes, the Sophie Germain primes, any set at all — has Hausdorff dimension `0`
in the `d`-metric. -/
theorem dimH_subFractal (T : Set ℕ) : dimH (logInv '' T) = 0 :=
  ((Set.to_countable T).image _).dimH_zero

/-- The twin prime fractal. -/
-- [dropped: platform already declares twinPrimeFractal]
theorem dimH_twinPrimeFractal : dimH twinPrimeFractal = 0 := dimH_subFractal _

/-!
### The total `d`-length of the primes is finite

The mission asserts that `∑_{p ≤ x} d(p, next p) ∼ log log x` diverges.  In fact
the sum telescopes and is bounded by `1 / log 2`.
-/

/-- Telescoping: along any increasing sequence of integers `≥ 2`, the total
`d`-length is a difference of two endpoint values. -/
theorem length_telescope (q : ℕ → ℕ) (hq2 : ∀ i, 2 ≤ q i) (hmono : StrictMono q) (n : ℕ) :
    ∑ i ∈ Finset.range n, dist (logInv (q i)) (logInv (q (i + 1)))
      = logInv (q 0) - logInv (q n) := by
  have hterm : ∀ i, dist (logInv (q i)) (logInv (q (i + 1)))
      = logInv (q i) - logInv (q (i + 1)) := by
    intro i
    have h := logInv_lt_logInv (hq2 i) (hmono (Nat.lt_succ_self i))
    rw [Real.dist_eq, abs_of_pos (by linarith)]
  simp only [hterm]
  exact Finset.sum_range_sub' (fun i => logInv (q i)) n

/-- The `d`-length of any finite increasing chain of primes is at most `1 / log 2`:
the prime fractal is a *rectifiable* set of finite length, not a divergent one. -/
theorem length_le (q : ℕ → ℕ) (hq2 : ∀ i, 2 ≤ q i) (hmono : StrictMono q) (n : ℕ) :
    ∑ i ∈ Finset.range n, dist (logInv (q i)) (logInv (q (i + 1))) ≤ 1 / Real.log 2 := by
  rw [length_telescope q hq2 hmono n]
  have h0 : logInv (q 0) ≤ 1 / Real.log 2 := by
    rcases eq_or_lt_of_le (hq2 0) with h | h
    · simp [logInv, ← h]
    · exact le_of_lt (by simpa [logInv] using logInv_lt_logInv (le_refl 2) h)
  have hn : 0 ≤ logInv (q n) := by
    have h2 : (2 : ℝ) ≤ ((q n : ℕ) : ℝ) := by exact_mod_cast hq2 n
    have hlog : 0 < Real.log (q n) := Real.log_pos (by linarith)
    simp only [logInv]
    positivity
  linarith

/-- The `n`-th prime, as a sequence. -/
-- [dropped: platform already declares primeSeq]
theorem primeSeq_prime (n : ℕ) : (primeSeq n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

theorem primeSeq_strictMono : StrictMono primeSeq :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

theorem primeSeq_zero : primeSeq 0 = 2 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 2) (by norm_num)
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  rwa [hc] at h

theorem tendsto_logInv_primeSeq : Tendsto (fun n => logInv (primeSeq n)) atTop (𝓝 0) := by
  have hle : ∀ n : ℕ, (n : ℝ) ≤ ((primeSeq n : ℕ) : ℝ) := by
    intro n
    exact_mod_cast primeSeq_strictMono.le_apply
  have hcast : Tendsto (fun n : ℕ => ((primeSeq n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono hle tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((primeSeq n : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  simpa [logInv, one_div] using hlog.inv_tendsto_atTop

/-- **The total `d`-length of the primes is exactly `1 / log 2`.**  In particular it
is finite, contradicting the divergence heuristic behind the mission conjecture. -/
theorem tendsto_primeFractal_length :
    Tendsto (fun n => ∑ i ∈ Finset.range n,
        dist (logInv (primeSeq i)) (logInv (primeSeq (i + 1)))) atTop (𝓝 (1 / Real.log 2)) := by
  have hq2 : ∀ i, 2 ≤ primeSeq i := fun i => (primeSeq_prime i).two_le
  have hrw : ∀ n, ∑ i ∈ Finset.range n,
      dist (logInv (primeSeq i)) (logInv (primeSeq (i + 1)))
      = 1 / Real.log 2 - logInv (primeSeq n) := by
    intro n
    rw [length_telescope primeSeq hq2 primeSeq_strictMono n, primeSeq_zero]
    norm_num [logInv]
  simp only [hrw]
  simpa using (tendsto_const_nhds (x := (1 : ℝ) / Real.log 2) (f := atTop)).sub
    tendsto_logInv_primeSeq

/-!
### Topology: the closure of the prime fractal
-/

theorem range_primeSeq : Set.range primeSeq = {p : ℕ | p.Prime} :=
  Nat.range_nth_of_infinite Nat.infinite_setOf_prime

theorem primeFractal_eq_range : primeFractal = Set.range (fun n => logInv (primeSeq n)) := by
  rw [primeFractal, ← range_primeSeq, ← Set.range_comp]
  rfl

/-- Adding the single limit point `0` makes the prime fractal compact. -/
theorem isCompact_insert_zero_primeFractal : IsCompact (insert (0 : ℝ) primeFractal) := by
  rw [primeFractal_eq_range]
  exact tendsto_logInv_primeSeq.isCompact_insert_range

/-- The closure of the prime fractal adds at most the point `0`. -/
theorem closure_primeFractal_subset : closure primeFractal ⊆ insert (0 : ℝ) primeFractal := by
  refine closure_minimal (Set.subset_insert _ _) ?_
  exact isCompact_insert_zero_primeFractal.isClosed

/-- Even the closure — a genuine compact subset of `ℝ` — has Hausdorff dimension `0`. -/
theorem dimH_closure_primeFractal : dimH (closure primeFractal) = 0 := by
  have hcount : (insert (0 : ℝ) primeFractal).Countable :=
    primeFractal_countable.insert 0
  exact (hcount.mono closure_primeFractal_subset).dimH_zero

end PrimeFractal
-- ==== upstream: Packages/Catalog/NumberTheory/PrimeFractalBoxDimension.lean ====
/-!
# The box-counting dimension of the prime fractal is exactly `1`

`NumberTheory.PrimeFractalHausdorff` shows that the Hausdorff dimension of the
prime fractal `{1 / log p : p prime} ⊆ ℝ` is `0`, refuting the mission
conjecture.  Here we prove the *positive* half of the story: the notion that
actually sees the conjectured value is the **box-counting (Minkowski)
dimension**, and for the prime fractal it equals `1` on the nose.

At scale `1/m` we count the boxes `[k/m, (k+1)/m)` that meet the prime fractal,
i.e. the cardinality `boxCount m` of the set of values `⌊m / log p⌋` over primes
`p`.  The two halves are:

* `boxCount_le` : `boxCount m ≤ 2m + 1` — a trivial upper bound valid for any
  subset of an interval, which is what forces the dimension to be `≤ 1`.  In
  particular *no* configuration of primes — twin primes included — can produce
  a dimension `1 + ε` with `ε > 0`.
* `eventually_boxCount_ge` : `boxCount m ≥ m / (16 (log m)^4)`.  This is the
  arithmetic input: it uses the Chebyshev-type lower bound
  `PrimeFractal.le_primeCounting_mul_log` together with the observation that
  `p ↦ ⌊m / log p⌋` is injective on primes `p ≤ Y` as soon as
  `2 Y (log Y)^2 ≤ m` (primes below `Y` are spread more than `1/m` apart in the
  `d`-metric).

Together they give `tendsto_boxCount_log_div`: `log (boxCount m) / log m → 1`,
hence `upperBoxDim = lowerBoxDim = 1` (`upperBoxDim_eq_one`,
`lowerBoxDim_eq_one`), while the Hausdorff dimension is `0`
(`dimH_lt_boxDim`).  The prime fractal is therefore a *dimension-irregular*
set: box and Hausdorff dimensions disagree maximally.
-/

namespace PrimeFractal

open Filter Topology

-- [dropped: platform already declares boxIndex]
-- [dropped: platform already declares occupiedBoxes]
-- [dropped: platform already declares boxCount]
theorem logInv_le_two {p : ℕ} (hp : 2 ≤ p) : logInv p ≤ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hpos : 0 < Real.log p := by linarith
  rw [logInv, div_le_iff₀ hpos]
  linarith

theorem boxIndex_le (m p : ℕ) (hp : 2 ≤ p) : boxIndex m p ≤ 2 * m := by
  have hle : (m : ℝ) * logInv p ≤ ((2 * m : ℕ) : ℝ) := by
    have h2 := logInv_le_two hp
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    push_cast
    nlinarith
  simpa using Nat.floor_le_of_le hle

theorem occupiedBoxes_subset (m : ℕ) : occupiedBoxes m ⊆ ↑(Finset.range (2 * m + 1)) := by
  rintro k ⟨p, hp, rfl⟩
  simp only [Finset.coe_range, Set.mem_Iio]
  exact Nat.lt_succ_of_le (boxIndex_le m p hp.two_le)

theorem occupiedBoxes_finite (m : ℕ) : (occupiedBoxes m).Finite :=
  Set.Finite.subset (Finset.range (2 * m + 1)).finite_toSet (occupiedBoxes_subset m)

/-- The trivial upper bound on the box count: at scale `1/m` the prime fractal, which
lives inside `[0, 2]`, can meet at most `2m + 1` boxes. -/
theorem boxCount_le (m : ℕ) : boxCount m ≤ 2 * m + 1 := by
  have h := Set.ncard_le_ncard (occupiedBoxes_subset m) (Finset.range (2 * m + 1)).finite_toSet
  simpa [boxCount, Set.ncard_coe_finset] using h

theorem one_le_boxCount (m : ℕ) : 1 ≤ boxCount m := by
  have hmem : boxIndex m 2 ∈ occupiedBoxes m := ⟨2, Nat.prime_two, rfl⟩
  have hne : (occupiedBoxes m).Nonempty := ⟨_, hmem⟩
  exact (Set.ncard_pos (occupiedBoxes_finite m)).mpr hne

/-! ### Separation of primes in the `d`-metric -/

/-- Consecutive integers `≥ 2` have logarithms at distance at least `1/(2p)`. -/
theorem log_sub_log_ge {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) :
    1 / (2 * (p : ℝ)) ≤ Real.log q - Real.log p := by
  have hP : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hQ : (p : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hpq
  set P : ℝ := (p : ℝ)
  set u : ℝ := 1 / (2 * P) with hu
  have hP0 : 0 < P := by linarith
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 4 := by
    rw [hu]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- `exp u ≤ 1 / (1 - u)`
  have hexp : (1 - u) * Real.exp u ≤ 1 := by
    have h := Real.add_one_le_exp (-u)
    rw [Real.exp_neg] at h
    have hpos : 0 < Real.exp u := Real.exp_pos u
    have h' : (1 - u) ≤ (Real.exp u)⁻¹ := by linarith
    calc (1 - u) * Real.exp u ≤ (Real.exp u)⁻¹ * Real.exp u := by nlinarith
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  -- hence `P * exp u ≤ Q`
  have hkey : P * Real.exp u ≤ (q : ℝ) := by
    have h1u : 0 < 1 - u := by linarith
    have hPQ : P ≤ (q : ℝ) * (1 - u) := by
      have hexpand : (q : ℝ) * (1 - u) = (q : ℝ) - (q : ℝ) * (1 / (2 * P)) := by
        rw [hu]; ring
      have hqu : (q : ℝ) * (1 / (2 * P)) ≤ (q : ℝ) - P := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        nlinarith [hQ, hP0]
      rw [hexpand]
      linarith
    nlinarith [Real.exp_pos u, hexp, hPQ, h1u]
  have hlog : Real.log (P * Real.exp u) ≤ Real.log q :=
    Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero u), Real.log_exp] at hlog
  linarith

/-- **Key separation estimate.** If `2 Y (log Y)^2 ≤ m` then distinct primes `p < q ≤ Y`
land in distinct boxes of size `1/m`. -/
theorem boxIndex_lt {m Y p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpY : p ≤ Y) (hqY : q ≤ Y)
    (hlt : p < q) (hm : 2 * (Y : ℝ) * (Real.log Y) ^ 2 ≤ m) :
    boxIndex m q < boxIndex m p := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hQ2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hpq' : (p : ℝ) < (q : ℝ) := by exact_mod_cast hlt
  set a : ℝ := Real.log p with ha
  set b : ℝ := Real.log q with hb
  set L : ℝ := Real.log Y with hL
  have ha0 : 0 < a := Real.log_pos (by linarith)
  have hab : a < b := Real.log_lt_log (by linarith) hpq'
  have hb0 : 0 < b := lt_trans ha0 hab
  have hbL : b ≤ L := Real.log_le_log (by linarith) (by exact_mod_cast hqY)
  have haL : a ≤ L := le_of_lt (lt_of_lt_of_le hab hbL)
  have hL0 : 0 < L := lt_of_lt_of_le ha0 haL
  have hsep : 1 / (2 * (p : ℝ)) ≤ b - a := log_sub_log_ge hp hlt
  have hPY : (p : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hpY
  have habL : a * b ≤ L ^ 2 := by nlinarith
  have hmP : 2 * (p : ℝ) * (a * b) ≤ (m : ℝ) := by nlinarith
  -- `m * (1/a - 1/b) ≥ 1`
  have hstep : 1 ≤ (m : ℝ) * (1 / a - 1 / b) := by
    have hdiff : 1 / a - 1 / b = (b - a) / (a * b) := by
      field_simp
    rw [hdiff, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
    have h1 : 2 * (p : ℝ) * (b - a) ≥ 1 := by
      rw [ge_iff_le, ← div_le_iff₀' (by positivity)]
      simpa [one_div] using hsep
    nlinarith [hmP, h1, mul_pos ha0 hb0]
  have hqnn : 0 ≤ (m : ℝ) * logInv q := by
    have : 0 ≤ logInv q := le_of_lt (by
      have : 0 < Real.log q := hb0
      simpa [logInv] using one_div_pos.mpr this)
    positivity
  have hge : (m : ℝ) * logInv q + 1 ≤ (m : ℝ) * logInv p := by
    simp only [logInv]
    nlinarith [hstep]
  have hfl := Nat.floor_le_floor hge
  rw [Nat.floor_add_one hqnn] at hfl
  simp only [boxIndex]
  exact Nat.lt_of_succ_le hfl

theorem boxIndex_injOn {m Y : ℕ} (hm : 2 * (Y : ℝ) * (Real.log Y) ^ 2 ≤ m) :
    Set.InjOn (boxIndex m) {p : ℕ | p.Prime ∧ p ≤ Y} := by
  rintro p ⟨hp, hpY⟩ q ⟨hq, hqY⟩ hpq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt := boxIndex_lt hp.two_le hq.two_le hpY hqY h hm
    rw [hpq] at hlt
    exact lt_irrefl _ hlt
  · have hlt := boxIndex_lt hq.two_le hp.two_le hqY hpY h hm
    rw [hpq] at hlt
    exact lt_irrefl _ hlt

/-! ### From Chebyshev to a lower bound on the box count -/

theorem primeCounting_eq_ncard (Y : ℕ) :
    {p : ℕ | p.Prime ∧ p ≤ Y}.ncard = Nat.primeCounting Y := by
  have hset : {p : ℕ | p.Prime ∧ p ≤ Y} = ↑(Nat.primesBelow (Y + 1)) := by
    ext p
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_primesBelow, Nat.lt_succ_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset, Set.ncard_coe_finset, Nat.primesBelow_card_eq_primeCounting']
  simpa using (Nat.primeCounting_sub_one (Y + 1)).symm

/-- Every prime `≤ Y` occupies its own box, provided `2 Y (log Y)^2 ≤ m`. -/
theorem primeCounting_le_boxCount {m Y : ℕ} (hm : 2 * (Y : ℝ) * (Real.log Y) ^ 2 ≤ m) :
    Nat.primeCounting Y ≤ boxCount m := by
  have hsub : boxIndex m '' {p : ℕ | p.Prime ∧ p ≤ Y} ⊆ occupiedBoxes m := by
    rintro k ⟨p, hp, rfl⟩
    exact ⟨p, hp.1, rfl⟩
  have h1 : (boxIndex m '' {p : ℕ | p.Prime ∧ p ≤ Y}).ncard = Nat.primeCounting Y := by
    rw [Set.InjOn.ncard_image (boxIndex_injOn hm), primeCounting_eq_ncard]
  calc Nat.primeCounting Y = (boxIndex m '' {p : ℕ | p.Prime ∧ p ≤ Y}).ncard := h1.symm
    _ ≤ (occupiedBoxes m).ncard := Set.ncard_le_ncard hsub (occupiedBoxes_finite m)
    _ = boxCount m := rfl

/-! ### Asymptotics -/

/-- Powers of `log` are eventually dominated by the identity, in the form we need. -/
theorem eventually_log_pow_le {C : ℝ} (hC : 0 < C) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, C * (Real.log m) ^ k ≤ (m : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in atTop, C * (Real.log x) ^ k ≤ x := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := k)).def (c := 1 / C) (by positivity)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hidx : (0 : ℝ) ≤ id x := by simpa using (by linarith : (0 : ℝ) ≤ x)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg hidx] at hx
    have : C * (Real.log x ^ k) ≤ C * ((1 / C) * x) := by
      exact mul_le_mul_of_nonneg_left hx (le_of_lt hC)
    calc C * Real.log x ^ k ≤ C * ((1 / C) * x) := this
      _ = x := by field_simp
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hreal

theorem eventually_two_le_log : ∀ᶠ m : ℕ in atTop, (2 : ℝ) ≤ Real.log m :=
  (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Real.tendsto_log_atTop.eventually_ge_atTop 2)

/-- **The arithmetic heart.** At scale `1/m` the primes occupy at least
`m / (16 (log m)^4)` boxes. -/
theorem eventually_boxCount_ge :
    ∀ᶠ m : ℕ in atTop, (m : ℝ) / (16 * (Real.log m) ^ 4) ≤ (boxCount m : ℝ) := by
  filter_upwards [eventually_log_pow_le (C := 16) (by norm_num) 3, eventually_two_le_log]
    with m h16 hL2
  set L : ℝ := Real.log m with hLdef
  have hL0 : 0 < L := by linarith
  have hL8 : (8 : ℝ) ≤ L ^ 3 := by
    nlinarith [hL2, sq_nonneg (L - 2), sq_nonneg (L + 2)]
  have hL3 : (0 : ℝ) < L ^ 3 := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set Y : ℕ := ⌊(m : ℝ) / L ^ 3⌋₊ with hYdef
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg Y
  have hYle : (Y : ℝ) * L ^ 3 ≤ (m : ℝ) := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ (m : ℝ) / L ^ 3 by positivity)
    rw [← hYdef] at h
    rw [← le_div_iff₀ hL3]
    exact h
  have hYgt : (m : ℝ) < ((Y : ℝ) + 1) * L ^ 3 := by
    have h := Nat.lt_floor_add_one ((m : ℝ) / L ^ 3)
    rw [← hYdef] at h
    rw [← div_lt_iff₀ hL3]
    exact h
  have hmL16 : (16 : ℝ) * L ^ 3 ≤ (m : ℝ) := by linarith
  have hY15 : (15 : ℝ) ≤ (Y : ℝ) := by nlinarith [hYgt, hmL16, hL3]
  have hY8 : 8 ≤ Y := by exact_mod_cast le_trans (by norm_num : (8 : ℝ) ≤ 15) hY15
  have hYm : (Y : ℝ) ≤ (m : ℝ) := by nlinarith [hYle, hL8, hY0]
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hlogYL : Real.log Y ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by linarith) hYm
  -- the separation hypothesis `2 Y (log Y)^2 ≤ m`
  have hsep : 2 * (Y : ℝ) * (Real.log Y) ^ 2 ≤ (m : ℝ) := by
    have h1 : (Real.log Y) ^ 2 ≤ L ^ 2 := by nlinarith
    have h2 : 2 * (Y : ℝ) * (Real.log Y) ^ 2 ≤ 2 * (Y : ℝ) * L ^ 2 := by nlinarith
    have h3 : 2 * (Y : ℝ) * L ^ 2 ≤ (Y : ℝ) * L ^ 3 := by nlinarith [sq_nonneg L, hY0, hL2]
    linarith
  -- Chebyshev's lower bound applied at `Y`
  have hcheb := le_primeCounting_mul_log Y hY8
  have hpi : (Nat.primeCounting Y : ℝ) ≤ (boxCount m : ℝ) := by
    exact_mod_cast primeCounting_le_boxCount hsep
  have hpi0 : (0 : ℝ) ≤ (Nat.primeCounting Y : ℝ) := Nat.cast_nonneg _
  have hchebL : (Y : ℝ) ≤ 8 * (Nat.primeCounting Y : ℝ) * L := by
    nlinarith [hcheb, hlogYL, hpi0]
  -- `m ≤ 2 Y L^3 ≤ 16 π(Y) L^4 ≤ 16 boxCount m L^4`
  have hm2Y : (m : ℝ) ≤ 2 * (Y : ℝ) * L ^ 3 := by nlinarith [hYgt, hY15, hL3]
  have hmfin : (m : ℝ) ≤ 16 * (Nat.primeCounting Y : ℝ) * L ^ 4 := by
    nlinarith [hchebL, hL3, hm2Y]
  rw [div_le_iff₀ (by positivity)]
  have hL4 : (0 : ℝ) < L ^ 4 := by positivity
  have hmul : (Nat.primeCounting Y : ℝ) * L ^ 4 ≤ (boxCount m : ℝ) * L ^ 4 := by
    nlinarith [hpi, hL4]
  linarith [hmfin, hmul]

theorem tendsto_log_log_div_log : Tendsto (fun m : ℕ => Real.log (Real.log m) / Real.log m)
    atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlog : Tendsto (fun m : ℕ => Real.log m) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  exact h.comp hlog

theorem tendsto_inv_log : Tendsto (fun m : ℕ => 1 / Real.log m) atTop (𝓝 0) := by
  have hlog : Tendsto (fun m : ℕ => Real.log m) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa [one_div] using hlog.inv_tendsto_atTop

/-- **Main theorem: the box-counting dimension of the prime fractal is `1`.** -/
theorem tendsto_boxCount_log_div :
    Tendsto (fun m : ℕ => Real.log (boxCount m) / Real.log m) atTop (𝓝 1) := by
  have hupper : ∀ᶠ m : ℕ in atTop,
      Real.log (boxCount m) / Real.log m ≤ 1 + Real.log 3 * (1 / Real.log m) := by
    filter_upwards [eventually_two_le_log, eventually_ge_atTop 1] with m hL2 hm1
    have hL0 : 0 < Real.log m := by linarith
    have hm0 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hb : (boxCount m : ℝ) ≤ 3 * (m : ℝ) := by
      have := boxCount_le m
      have : ((boxCount m : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
    have hb0 : (0 : ℝ) < (boxCount m : ℝ) := by
      have := one_le_boxCount m
      exact_mod_cast lt_of_lt_of_le zero_lt_one (by exact_mod_cast this)
    have hlog : Real.log (boxCount m) ≤ Real.log 3 + Real.log m := by
      have := Real.log_le_log hb0 hb
      rwa [Real.log_mul (by norm_num) (by linarith)] at this
    rw [div_le_iff₀ hL0]
    field_simp
    linarith
  have hlower : ∀ᶠ m : ℕ in atTop,
      1 - (Real.log 16 * (1 / Real.log m) + 4 * (Real.log (Real.log m) / Real.log m))
        ≤ Real.log (boxCount m) / Real.log m := by
    filter_upwards [eventually_boxCount_ge, eventually_two_le_log, eventually_ge_atTop 1]
      with m hge hL2 hm1
    have hL0 : 0 < Real.log m := by linarith
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hpos : (0 : ℝ) < (m : ℝ) / (16 * (Real.log m) ^ 4) := by positivity
    have hlog := Real.log_le_log hpos hge
    have hexp : Real.log ((m : ℝ) / (16 * (Real.log m) ^ 4))
        = Real.log m - Real.log 16 - 4 * Real.log (Real.log m) := by
      rw [Real.log_div (ne_of_gt hm0) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [hexp] at hlog
    rw [le_div_iff₀ hL0]
    field_simp
    linarith
  have h1 : Tendsto (fun m : ℕ => 1 + Real.log 3 * (1 / Real.log m)) atTop (𝓝 1) := by
    have := (tendsto_inv_log.const_mul (Real.log 3))
    simpa using tendsto_const_nhds.add this
  have h2 : Tendsto (fun m : ℕ =>
      1 - (Real.log 16 * (1 / Real.log m) + 4 * (Real.log (Real.log m) / Real.log m)))
      atTop (𝓝 1) := by
    have ha := tendsto_inv_log.const_mul (Real.log 16)
    have hb := tendsto_log_log_div_log.const_mul (4 : ℝ)
    have := tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)) |>.sub (ha.add hb)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1 hlower hupper

/-- The upper box-counting (Minkowski) dimension of the prime fractal. -/
-- [dropped: platform already declares upperBoxDim]
-- [dropped: platform already declares lowerBoxDim]
theorem upperBoxDim_eq_one : upperBoxDim = 1 := tendsto_boxCount_log_div.limsup_eq

theorem lowerBoxDim_eq_one : lowerBoxDim = 1 := tendsto_boxCount_log_div.liminf_eq

/-- **The box dimension is exactly `1`: no `ε` of twin primes.** -/
theorem boxDim_eq_one : upperBoxDim = 1 ∧ lowerBoxDim = 1 :=
  ⟨upperBoxDim_eq_one, lowerBoxDim_eq_one⟩

/-- **Dimension irregularity.** The Hausdorff dimension (`0`) is strictly smaller than the
box-counting dimension (`1`): the prime fractal is not a self-similar/Ahlfors-regular set. -/
theorem dimH_lt_boxDim : (dimH primeFractal).toReal < upperBoxDim := by
  rw [dimH_primeFractal, upperBoxDim_eq_one]
  norm_num

end PrimeFractal
section
open PrimeFractal
open Filter Topology

theorem solution  :
    Tendsto (fun m : ℕ => Real.log (boxCount m) / Real.log m) atTop (𝓝 1) := by
  first
  | exact PrimeFractal.tendsto_boxCount_log_div
  | exact PrimeFractal.tendsto_boxCount_log_div
  | exact @PrimeFractal.tendsto_boxCount_log_div
  | apply PrimeFractal.tendsto_boxCount_log_div
  | exact PrimeFractal.tendsto_boxCount_log_div ..


end
