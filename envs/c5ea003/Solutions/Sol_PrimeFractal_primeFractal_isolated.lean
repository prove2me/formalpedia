-- Prove2me | solution 1 for PrimeFractal.primeFractal_isolated
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:26:28.208805+00:00
-- url     : https://prove2.me/submissions/3686f4c1-2653-425c-a192-4de04e07dded

-- Sol generated from NumberTheory/PrimeFractalTwin.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalHausdorff
import Theorems.Thm_PrimeFractal_finite_of_le_logInv
import Theorems.Thm_PrimeFractal_logInv_pos

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
theorem solution{x : ℝ} (hx : x ∈ primeFractal) :
    ∃ ε > 0, ∀ y ∈ primeFractal, |y - x| < ε → y = x := by
  obtain ⟨q, hq, rfl⟩ := hx
  set x : ℝ := logInv q with hxdef
  have hx0 : 0 < x := logInv_pos hq
  -- the points of the fractal above `x/2` form a finite set
  have hfin : (logInv '' {p : ℕ | p.Prime ∧ x / 2 ≤ logInv p}).Finite :=
    (finite_of_le_logInv (by linarith)).image _
  set F : Set ℝ := (logInv '' {p : ℕ | p.Prime ∧ x / 2 ≤ logInv p}) \ {x} with hFdef
  have hFfin : F.Finite := hfin.diff
  have hxF : x ∉ F := by simp [hFdef]
  have hopen : IsOpen Fᶜ := hFfin.isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hxF
  refine ⟨min ε (x / 2), by positivity, ?_⟩
  rintro y ⟨p, hp, rfl⟩ hlt
  have h1 : |logInv p - x| < ε := lt_of_lt_of_le hlt (min_le_left _ _)
  have h2 : |logInv p - x| < x / 2 := lt_of_lt_of_le hlt (min_le_right _ _)
  have hge : x / 2 ≤ logInv p := by
    rw [abs_lt] at h2
    linarith [h2.1]
  by_contra hne
  have hmem : logInv p ∈ F := by
    refine ⟨⟨p, ⟨hp, hge⟩, rfl⟩, ?_⟩
    simpa using hne
  have : logInv p ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact h1
  exact (hball this) hmem
