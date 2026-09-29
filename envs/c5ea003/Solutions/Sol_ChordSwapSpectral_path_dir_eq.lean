-- Prove2me | solution 1 for ChordSwapSpectral.path_dir_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:06:55.437404+00:00
-- url     : https://prove2.me/submissions/53fec2ee-7773-40bb-8144-7c543c975d6b

-- Sol generated from Novelty/ChordSwapSpectralGap.lean
import Mathlib
import Definitions.Def_Novelty_ChordSwapSpectralGap
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A cubic spectral-gap witness for chord-swap reconfiguration chains

A *chord diagram* of size `n` is a perfect matching of `2n` points on a circle,
and its *genus* `g` records the topological complexity of the surface obtained by
thickening the chords.  The **chord-swap Markov chain** moves between diagrams of
a fixed genus by reconnecting the four endpoints of two chords, and its mixing
speed is governed by the **spectral gap** `γ_{n,g}`.  Empirically the gap of this
chain, and of the closely related swap chains on perfect matchings, decays like
`n^{-3}` at fixed genus.  The polynomial lower bounds available in the literature
leave the *exponent* open; the present file isolates the exact mechanism through
which the exponent `3` arises and proves, unconditionally, that a natural family
of one-dimensional swap chains realises it.

The spectral gap of a reversible chain has the variational description
`γ = inf_f  E(f,f) / Var(f)`, the infimum over non-constant test functions of the
ratio of the Dirichlet energy to the variance.  This ratio is the single most
important tool for *upper*-bounding a gap: exhibiting one slowly-varying test
function certifies that the chain mixes no faster than the ratio it produces.
We develop this Rayleigh-quotient calculus abstractly for a finite state space
with symmetric edge weights, and then feed it the "position" test function on a
weighted path — the canonical one-dimensional swap chain, in which a local move
shifts a single monotone statistic by one unit.

## Main results

* `dir_nonneg`, `vr_nonneg`, `vr_pos_of_nonconstant` — the Dirichlet energy and
  the pairwise variance are non-negative, and the variance is *strictly* positive
  exactly when the test function is non-constant.
* `vr_eq` — the pairwise variance collapses to the closed form
  `2·(|V|·Σ f² − (Σ f)²)`, the discrete analogue of `Var(f) = E[f²] − E[f]²`.
* `gap_nonneg` and `gap_le_RQ` — the combinatorial spectral gap is non-negative,
  and it is bounded above by the Rayleigh quotient of *every* non-constant test
  function.  This is the abstract engine for all gap upper bounds.
* `path_dir_eq`, `path_vr_eq`, `path_RQ_eq` — on the length-`n` weighted path the
  position test function has Dirichlet energy `2(n−1)`, variance `n²(n²−1)/6`, and
  Rayleigh quotient exactly `12 / (n²(n+1))`.
* `path_gap_cubic_upper` and `path_RQ_Theta` — consequently the gap of the path
  swap chain is `O(n^{-3})`, and the certifying Rayleigh quotient is itself
  `Θ(n^{-3})` (pinched between `6 n^{-3}` and `12 n^{-3}`).  The exponent `3` is
  therefore not an artefact: it is the intrinsic scale of a one-dimensional swap
  statistic, whose energy grows linearly while its variance grows quartically.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  The `n^{-3}` scaling seen for fixed-genus
  chord-swap chains is a shadow of one-dimensional geometry: any swap chain
  carrying a monotone integer statistic that changes by `±1` per move has a test
  function whose energy is linear in `n` and whose variance is quartic in `n`,
  forcing a Rayleigh quotient of order `n^{-3}`.
* **Experiment (Experimenter).**  Built the Rayleigh-quotient calculus over a
  finite space and proved the `inf`-characterisation gives `gap ≤ RQ f` for every
  non-constant `f` (`csInf_le` with the trivial lower bound `0`).  Computed the
  path witness in closed form: energy `2(n−1)` by counting the `2(n−1)` oriented
  edges, variance `n²(n²−1)/6` from `vr_eq` together with the Gauss and
  square-pyramidal sums, quotient `12/(n²(n+1))`.
* **Analysis (Analyst).**  The result is "true and structural".  The whole
  strength is in the *ratio of growth rates*: energy `Θ(n)`, variance `Θ(n⁴)`.
  The infimum characterisation is what turns a single test function into a
  genuine upper bound, and `vr_eq` is what makes the variance computable without
  touching the edge structure.  The exponent `3 = 4 − 1` is the difference of the
  two growth rates.
* **Critique (Critic).**  Is `gap_le_RQ` vacuous?  No — it requires a genuine
  non-constant witness (`path_nonconstant`) and the edge weights to be
  non-negative (used for boundedness below).  Is the path bound trivial?  No: the
  variance is genuinely quartic, and `path_RQ_Theta` shows the quotient is pinned
  to `Θ(n^{-3})`, so no cheaper test function of this monotone shape can beat the
  exponent.  No theorem references itself; the file builds strictly upward.
* **Synthesis (PI).**  The fixed-genus chord-swap gap question factors into
  (i) this universal Rayleigh calculus, and (ii) constructing, on the diagram
  space, a monotone genus-aware statistic that moves by `±1` per swap and whose
  variance is quartic — at which point the same energy/variance bookkeeping
  delivers the `n^{-3}` upper bound.  The matching lower bound is the remaining
  (canonical-path / Poincaré) half of the `Θ` and is recorded as future work.
-/

open scoped BigOperators
open Finset

open ChordSwapSpectral

variable {V : Type*} [Fintype V]












/-! ### The one-dimensional swap chain: the weighted path -/






/-- Auxiliary count: the number of positions `x` with a right neighbour is `n − 1`. -/
theorem sumT (n : ℕ) (hn : 1 ≤ n) :
    (∑ x : Fin n, (if x.val + 1 < n then (1 : ℝ) else 0)) = (n : ℝ) - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j + 1 < n then (1 : ℝ) else 0) n]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : (Finset.range n).filter (fun j => j + 1 < n) = Finset.range (n - 1) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h1, Finset.card_range]
  push_cast [Nat.cast_sub hn]; ring








open ChordSwapSpectral in
theorem solution{n : ℕ} (hn : 1 ≤ n) :
    dir (pathQ n) (idf n) = 2 * ((n : ℝ) - 1) := by
  have hterm : ∀ x y : Fin n, pathQ n x y * (idf n x - idf n y) ^ 2 = pathQ n x y := by
    intro x y
    unfold pathQ idf
    by_cases h : x.val + 1 = y.val ∨ y.val + 1 = x.val
    · simp only [if_pos h]
      rcases h with h | h
      · have hy : (y.val : ℝ) = (x.val : ℝ) + 1 := by exact_mod_cast h.symm
        rw [hy]; ring
      · have hx : (x.val : ℝ) = (y.val : ℝ) + 1 := by exact_mod_cast h.symm
        rw [hx]; ring
    · simp only [if_neg h]; ring
  unfold dir
  simp_rw [hterm]
  have hsplit : ∀ x y : Fin n, pathQ n x y
      = (if x.val + 1 = y.val then (1 : ℝ) else 0)
        + (if y.val + 1 = x.val then (1 : ℝ) else 0) := by
    intro x y; unfold pathQ
    by_cases hA : x.val + 1 = y.val <;> by_cases hB : y.val + 1 = x.val <;> simp_all
    all_goals omega
  simp_rw [hsplit, Finset.sum_add_distrib]
  have inner1 : ∀ x : Fin n, (∑ y : Fin n, (if x.val + 1 = y.val then (1 : ℝ) else 0))
      = if x.val + 1 < n then (1 : ℝ) else 0 := by
    intro x
    rw [Fin.sum_univ_eq_sum_range (fun j => if x.val + 1 = j then (1 : ℝ) else 0) n]
    rw [Finset.sum_ite_eq (Finset.range n) (x.val + 1) (fun _ => (1 : ℝ))]
    simp [Finset.mem_range]
  have inner2 : ∀ x : Fin n, (∑ y : Fin n, (if y.val + 1 = x.val then (1 : ℝ) else 0))
      = if 1 ≤ x.val then (1 : ℝ) else 0 := by
    intro x
    rw [Fin.sum_univ_eq_sum_range (fun j => if j + 1 = x.val then (1 : ℝ) else 0) n]
    by_cases hx : 1 ≤ x.val
    · rw [show (fun j => if j + 1 = x.val then (1 : ℝ) else 0)
          = (fun j => if x.val - 1 = j then (1 : ℝ) else 0) from ?_]
      · rw [Finset.sum_ite_eq (Finset.range n) (x.val - 1) (fun _ => (1 : ℝ))]
        have hlt : x.val - 1 < n := by omega
        simp [Finset.mem_range, hlt, hx]
      · funext j; by_cases h : x.val - 1 = j <;> simp_all <;> omega
    · rw [if_neg hx]
      apply Finset.sum_eq_zero
      intro j _; rw [if_neg (by omega)]
  simp_rw [inner1, inner2]
  rw [sumT n hn]
  have hsum2 : (∑ x : Fin n, (if 1 ≤ x.val then (1 : ℝ) else 0)) = (n : ℝ) - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if 1 ≤ j then (1 : ℝ) else 0) n]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 : (Finset.range n).filter (fun j => 1 ≤ j) = Finset.Ico 1 n := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [h1, Nat.card_Ico]
    push_cast [Nat.cast_sub hn]; ring
  rw [hsum2]; ring
