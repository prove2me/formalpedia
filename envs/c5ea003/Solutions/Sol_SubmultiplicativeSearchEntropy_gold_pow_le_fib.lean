-- Prove2me | solution 1 for SubmultiplicativeSearchEntropy.gold_pow_le_fib
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:42:04.700958+00:00
-- url     : https://prove2.me/submissions/c6b57c61-d5d6-474e-8bb0-6171931ee058

-- Sol generated from Bridges/SubmultiplicativeSearchEntropy.lean
import Mathlib
import Definitions.Def_Bridges_SubmultiplicativeSearchEntropy
import Theorems.Thm_SubmultiplicativeSearchEntropy_pathCount_fibMatrix
import Theorems.Thm_SubmultiplicativeSearchEntropy_pow_le_pathCount

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



lemma fibMatrix_nonneg : ∀ i j, 0 ≤ fibMatrix i j := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [fibMatrix]


/-- The golden ratio is a Perron eigenvalue of the Fibonacci automaton, with the strictly
positive eigenvector `(φ, 1)`. -/
lemma fibMatrix_mulVec_gold :
    fibMatrix.mulVec ![Real.goldenRatio, 1] = Real.goldenRatio • ![Real.goldenRatio, 1] := by
  funext i
  fin_cases i
  · simp only [fibMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    simp
    nlinarith [Real.goldenRatio_sq]
  · simp [fibMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]







open SubmultiplicativeSearchEntropy in
theorem solution(n : ℕ) : Real.goldenRatio ^ n ≤ (Nat.fib (n + 3) : ℝ) := by
  have h1 : ∀ m, (1 : ℝ) ≤ pathCount fibMatrix m := by
    intro m
    rw [pathCount_fibMatrix m]
    have : 1 ≤ Nat.fib (m + 3) := Nat.fib_pos.2 (by omega)
    exact_mod_cast this
  have := pow_le_pathCount (k := 2) (A := fibMatrix) (r := Real.goldenRatio)
    (v := ![Real.goldenRatio, 1]) (c := 1) (C := Real.goldenRatio)
    (by norm_num) fibMatrix_nonneg h1 one_pos
    (by intro i; fin_cases i <;> simp [Real.one_lt_goldenRatio.le])
    (by intro i; fin_cases i <;> simp [Real.one_lt_goldenRatio.le])
    fibMatrix_mulVec_gold Real.goldenRatio_pos n
  rwa [pathCount_fibMatrix n] at this
