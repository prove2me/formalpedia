-- Prove2me | solution 1 for PrimeFractal.zero_mem_closure_iff_infinite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:26:31.167657+00:00
-- url     : https://prove2.me/submissions/67389950-161b-486a-90b0-cf865afcf59a

-- Sol generated from NumberTheory/PrimeFractalTwin.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalHausdorff
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
theorem solution{T : Set ℕ} (hT : ∀ p ∈ T, Nat.Prime p) :
    (0 : ℝ) ∈ closure (logInv '' T) ↔ T.Infinite := by
  constructor
  · intro h0
    by_contra hfin
    rw [Set.not_infinite] at hfin
    have hclosed : IsClosed (logInv '' T) := (hfin.image _).isClosed
    rw [hclosed.closure_eq] at h0
    obtain ⟨p, hpT, hp0⟩ := h0
    have hpos := logInv_pos (hT p hpT)
    rw [hp0] at hpos
    exact lt_irrefl 0 hpos
  · intro hinf
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨p, hpT, hplarge⟩ := hinf.exists_gt ⌈Real.exp (1 / ε)⌉₊
    have hprime := hT p hpT
    have hP : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hlog : 0 < Real.log p := Real.log_pos (by linarith)
    have hexp : Real.exp (1 / ε) < (p : ℝ) := by
      have h1 : Real.exp (1 / ε) ≤ (⌈Real.exp (1 / ε)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈Real.exp (1 / ε)⌉₊ : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast hplarge
      linarith
    have hloglt : 1 / ε < Real.log p := by
      have := Real.log_lt_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at this
    refine ⟨logInv p, ⟨p, hpT, rfl⟩, ?_⟩
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (logInv_pos hprime), logInv,
      div_lt_iff₀ hlog]
    rw [div_lt_iff₀ hε] at hloglt
    linarith
