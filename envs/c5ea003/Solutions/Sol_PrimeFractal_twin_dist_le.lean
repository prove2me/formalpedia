-- Prove2me | solution 1 for PrimeFractal.twin_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:26:30.574919+00:00
-- url     : https://prove2.me/submissions/d7e5a417-4079-437d-a68d-3ce89a6a041c

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
theorem solution{p : ℕ} (hp : 2 ≤ p) :
    dist (logInv p) (logInv (p + 2)) ≤ 2 / ((p : ℝ) * (Real.log p) ^ 2) := by
  have hP : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hcast : ((p + 2 : ℕ) : ℝ) = (p : ℝ) + 2 := by push_cast; ring
  have ha0 : 0 < Real.log p := Real.log_pos (by linarith)
  have hb0 : 0 < Real.log ((p : ℝ) + 2) := Real.log_pos (by linarith)
  have hab : Real.log p ≤ Real.log ((p : ℝ) + 2) :=
    Real.log_le_log hP0 (by linarith)
  -- `log (p+2) - log p ≤ 2 / p`
  have hstep : Real.log ((p : ℝ) + 2) - Real.log p ≤ 2 / (p : ℝ) := by
    have hdiv : Real.log (((p : ℝ) + 2) / (p : ℝ)) ≤ ((p : ℝ) + 2) / (p : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) (ne_of_gt hP0)] at hdiv
    have : ((p : ℝ) + 2) / (p : ℝ) - 1 = 2 / (p : ℝ) := by field_simp; ring
    linarith [hdiv, this.le, this.ge]
  have hdist : dist (logInv p) (logInv (p + 2))
      = 1 / Real.log p - 1 / Real.log ((p : ℝ) + 2) := by
    rw [Real.dist_eq, logInv, logInv, hcast, abs_of_nonneg]
    have h1 : 1 / Real.log ((p : ℝ) + 2) ≤ 1 / Real.log p :=
      one_div_le_one_div_of_le ha0 hab
    linarith
  rw [hdist]
  have hkey : 1 / Real.log p - 1 / Real.log ((p : ℝ) + 2)
      = (Real.log ((p : ℝ) + 2) - Real.log p) / (Real.log p * Real.log ((p : ℝ) + 2)) := by
    field_simp
  rw [hkey, div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : (Real.log p) ^ 2 ≤ Real.log p * Real.log ((p : ℝ) + 2) := by nlinarith
  have hnum : Real.log ((p : ℝ) + 2) - Real.log p ≤ 2 / (p : ℝ) := hstep
  have h2p : (2 : ℝ) / (p : ℝ) * ((p : ℝ) * (Real.log p) ^ 2) = 2 * (Real.log p) ^ 2 := by
    field_simp
  calc (Real.log ((p : ℝ) + 2) - Real.log p) * ((p : ℝ) * (Real.log p) ^ 2)
      ≤ (2 / (p : ℝ)) * ((p : ℝ) * (Real.log p) ^ 2) := by
        apply mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 2 * (Real.log p) ^ 2 := h2p
    _ ≤ 2 * (Real.log p * Real.log ((p : ℝ) + 2)) := by linarith
