-- Prove2me | solution 1 for PrimeFractal.finite_of_le_logInv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:18:53.908362+00:00
-- url     : https://prove2.me/submissions/adcbf1e7-4bae-4f1b-9bf6-563d3ccf30a3

-- Sol generated from NumberTheory/PrimeFractalTwin.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalHausdorff

/-!
# No fractal dust: the metric structure of twin primes in the prime fractal

The mission's conjecture rests on the picture that "twin primes create a fractal
dust that increases the dimension".  Here we show that the picture is wrong in
a precise, structural way.

* `twin_dist_le` — a twin pair `(p, p+2)` sits at `d`-distance at most
  `2 / (p (log p)^2)`, *not* `∼ 1 / (p log p)` as the mission asserts: the
  mission's heuristic overestimates the twin scale by a factor `log p`.
* `finite_of_le_logInv` — only finitely many primes lie above any positive
  height, so
* `primeFractal_isolated` — **every point of the prime fractal is isolated**.
  A countable, uniformly discrete-away-from-`0` set carries no dust at any
  scale: the accumulation happens only at the single point `0`.
* `zero_mem_closure_iff_infinite` — for any family `T` of primes, `0` is in the
  closure of the corresponding subfractal iff `T` is infinite.  Applied to the
  twin primes (`twin_conjecture_iff_zero_mem_closure`) this turns the twin
  prime conjecture into a purely metric statement about a single point of `ℝ`
  — and that point contributes nothing to any dimension.
-/

open PrimeFractal

open Filter Topology








open PrimeFractal in
theorem solution{t : ℝ} (ht : 0 < t) :
    {p : ℕ | p.Prime ∧ t ≤ logInv p}.Finite := by
  refine Set.Finite.subset (Set.finite_Iic ⌈Real.exp (1 / t)⌉₊) ?_
  rintro p ⟨hp, hpt⟩
  have hP : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlog : 0 < Real.log p := Real.log_pos (by linarith)
  have hle : Real.log p ≤ 1 / t := by
    rw [logInv] at hpt
    rw [le_div_iff₀ ht]
    rw [le_div_iff₀ hlog] at hpt
    linarith
  have : (p : ℝ) ≤ Real.exp (1 / t) := by
    have := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log (by linarith)] at this
  simp only [Set.mem_Iic]
  have hceil : (p : ℝ) ≤ (⌈Real.exp (1 / t)⌉₊ : ℝ) := le_trans this (Nat.le_ceil _)
  exact_mod_cast hceil
