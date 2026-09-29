-- Prove2me | solution 1 for SubmultiplicativeSearchEntropy.pathCount_fibMatrix
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:29:07.892116+00:00
-- url     : https://prove2.me/submissions/7154a058-2c85-4586-b179-3acce2f172a3

-- Sol generated from Bridges/SubmultiplicativeSearchEntropy.lean
import Mathlib
import Definitions.Def_Bridges_SubmultiplicativeSearchEntropy

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




lemma fibMatrix_sq : fibMatrix ^ 2 = fibMatrix + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fibMatrix, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]


/-- Path counts of the Fibonacci automaton satisfy the Fibonacci recursion. -/
lemma pathCount_fib_rec (n : ℕ) :
    pathCount fibMatrix (n + 2) = pathCount fibMatrix (n + 1) + pathCount fibMatrix n := by
  have hmat : fibMatrix ^ (n + 2) = fibMatrix ^ (n + 1) + fibMatrix ^ n := by
    have : fibMatrix ^ (n + 2) = fibMatrix ^ n * fibMatrix ^ 2 := by rw [pow_add]
    rw [this, fibMatrix_sq, mul_add, mul_one, ← pow_succ]
  simp only [pathCount, hmat, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib






open SubmultiplicativeSearchEntropy in
theorem solution(n : ℕ) : pathCount fibMatrix n = (Nat.fib (n + 3) : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pathCount, Matrix.one_apply]; norm_num
  | one =>
      simp [pathCount, fibMatrix, Fin.sum_univ_succ]
      norm_num
  | more n ih1 ih2 =>
      rw [pathCount_fib_rec n, ih1, ih2]
      have hf : Nat.fib (n + 2 + 3) = Nat.fib (n + 1 + 3) + Nat.fib (n + 3) := by
        have e1 : n + 2 + 3 = (n + 3) + 2 := by ring
        have e2 : n + 1 + 3 = (n + 3) + 1 := by ring
        rw [e1, e2, Nat.fib_add_two]
        omega
      rw [hf]
      push_cast
      ring
