-- Prove2me | solution 1 for SubmultiplicativeSearchEntropy.tendsto_pathCount_rate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:36:24.325574+00:00
-- url     : https://prove2.me/submissions/5b9c88a8-7e1a-4c7e-83d3-0bd5839a4d1b

-- Sol generated from Bridges/SubmultiplicativeSearchEntropy.lean
import Mathlib
import Definitions.Def_Bridges_SubmultiplicativeSearchEntropy
import Theorems.Thm_SubmultiplicativeSearchEntropy_pathCount_eigen_bounds

/-! # Submultiplicative search entropy and the Perron root

A bridge between three areas:

* **Combinatorics of proof search** — counting the successful prefixes of a search language;
* **Real analysis (Fekete's subadditive lemma)** — existence of the normalized logarithmic
  growth rate and its identification with the infimum of the finite-scale rates;
* **Linear algebra of nonnegative matrices (Perron theory)** — the growth rate of a
  finite-state pruned search equals `log ρ`, where `ρ` is the Perron eigenvalue of the
  automaton's transition matrix.
-/

open Filter Topology Set

open SubmultiplicativeSearchEntropy

/-! ## Part 1 — Submultiplicative counting functions and Fekete's lemma -/


open SearchProfile

variable (P : SearchProfile)

















/-! ## Part 2 — Nonnegative matrices: path counts of a finite-state pruning automaton -/


variable {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}





/-! ### Perron eigenvectors control path counts -/

variable {r : ℝ}




/-! ## Part 3 — The growth rate of a Perron-controlled search equals `log r` -/

/-- Auxiliary limit: `log (c * r ^ n) / n → log r`. -/
lemma tendsto_log_const_mul_pow_div {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    Tendsto (fun n : ℕ => Real.log (c * r ^ n) / n) atTop (𝓝 (Real.log r)) := by
  have hlim : Tendsto (fun n : ℕ => Real.log c / n + Real.log r) atTop
      (𝓝 (0 + Real.log r)) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Real.log_mul hc.ne' (by positivity), Real.log_pow]
  field_simp

/-- **Squeeze lemma.** A positive sequence trapped between two constant multiples of `r ^ n`
has normalized logarithmic growth rate exactly `log r`. -/
lemma tendsto_log_div_of_comparable {N : ℕ → ℝ} {c C r : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hr : 0 < r) (hlow : ∀ n, c * r ^ n ≤ N n) (hhigh : ∀ n, N n ≤ C * r ^ n) :
    Tendsto (fun n : ℕ => Real.log (N n) / n) atTop (𝓝 (Real.log r)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_log_const_mul_pow_div hc hr) (tendsto_log_const_mul_pow_div hC hr)
    (fun n => ?_) (fun n => ?_)
  · have hpos : 0 < c * r ^ n := by positivity
    have := Real.log_le_log hpos (hlow n)
    gcongr
  · have hpos : 0 < N n := lt_of_lt_of_le (by positivity) (hlow n)
    have := Real.log_le_log hpos (hhigh n)
    gcongr

/-! ## Part 4 — The bridge theorem: Perron root = entropy = dimension -/


variable {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} {r : ℝ}








/-! ## Part 5 — Worked instances

### 5a. Uniform self-similar search: the classical similarity dimension

A `1 × 1` transition matrix `!![s]` models a uniformly self-similar problem in which exactly `s`
of the branches at each node extend to a proof; the bridge recovers the classical similarity
dimension `log s / log b` of the earlier scalar theory. -/


variable {s : ℝ}




/-! ### 5b. The Fibonacci pruning automaton and the golden ratio

Inside the binary search tree, prune every branch that would use two "expensive" inference steps
in a row.  The accepted paths are counted by the transition matrix `!![1,1;1,0]`, whose path
counts are Fibonacci numbers and whose Perron root is the golden ratio; the resulting
proof-search dimension is `log φ / log 2 ≈ 0.6942`. -/












open SubmultiplicativeSearchEntropy in
theorem solution(hk : 0 < k) (hA : ∀ i j, 0 ≤ A i j) {v : Fin k → ℝ} {c C : ℝ}
    (hc : 0 < c) (hcv : ∀ i, c ≤ v i) (hvC : ∀ i, v i ≤ C) (hv : A.mulVec v = r • v)
    (hr : 0 < r) :
    Tendsto (fun n : ℕ => Real.log (pathCount A n) / n) atTop (𝓝 (Real.log r)) := by
  have hkne : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i0⟩ := hkne
  have hC : 0 < C := lt_of_lt_of_le hc ((hcv i0).trans (hvC i0))
  have hS : 0 < ∑ i, v i :=
    Finset.sum_pos (fun i _ => lt_of_lt_of_le hc (hcv i)) ⟨i0, Finset.mem_univ i0⟩
  have hbounds := fun n => pathCount_eigen_bounds (A := A) (r := r) hA hcv hvC hv n
  refine tendsto_log_div_of_comparable (c := (∑ i, v i) / C) (C := (∑ i, v i) / c)
    (by positivity) (by positivity) hr (fun n => ?_) (fun n => ?_)
  · rw [div_mul_eq_mul_div, div_le_iff₀ hC, mul_comm (∑ i, v i) (r ^ n)]
    exact (hbounds n).2.trans_eq (mul_comm _ _)
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc, mul_comm (∑ i, v i) (r ^ n), mul_comm (pathCount A n) c]
    exact (hbounds n).1
