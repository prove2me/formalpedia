-- Prove2me | solution 1 for PrimeFractal.length_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:18:54.437231+00:00
-- url     : https://prove2.me/submissions/f8a787d0-7701-400b-b4cf-8a4d38944dbc

-- Sol generated from NumberTheory/PrimeFractalHausdorff.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalHausdorff

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

open PrimeFractal

open Filter Topology





/-- `logInv` is strictly antitone on integers `≥ 2`. -/
theorem logInv_lt_logInv {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) : logInv q < logInv p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpq' : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlq : Real.log p < Real.log q := Real.log_lt_log (by linarith) hpq'
  exact one_div_lt_one_div_of_lt hlp hlq









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








/-!
### Topology: the closure of the prime fractal
-/







open PrimeFractal in
theorem solution(q : ℕ → ℕ) (hq2 : ∀ i, 2 ≤ q i) (hmono : StrictMono q) (n : ℕ) :
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
