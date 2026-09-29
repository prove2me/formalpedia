-- Prove2me | solution 1 for SubmultiplicativeSearchEntropy.pathCount_eigen_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:29:08.411544+00:00
-- url     : https://prove2.me/submissions/5ee4efa2-5c61-4319-a59a-333de1379ad6

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

/-- If `v` is an eigenvector of `A` for the eigenvalue `r`, it is an eigenvector of `A ^ n`
for `r ^ n`. -/
lemma mulVec_pow_of_eigen {v : Fin k → ℝ} (hv : A.mulVec v = r • v) :
    ∀ n, (A ^ n).mulVec v = (r ^ n) • v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]



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












open SubmultiplicativeSearchEntropy in
theorem solution(hA : ∀ i j, 0 ≤ A i j) {v : Fin k → ℝ} {c C : ℝ}
    (hcv : ∀ i, c ≤ v i) (hvC : ∀ i, v i ≤ C) (hv : A.mulVec v = r • v) (n : ℕ) :
    c * pathCount A n ≤ r ^ n * (∑ i, v i) ∧ r ^ n * (∑ i, v i) ≤ C * pathCount A n := by
  have hrow : ∀ i, ∑ j, (A ^ n) i j * v j = r ^ n * v i := by
    intro i
    have := congrFun (mulVec_pow_of_eigen (A := A) (r := r) hv n) i
    simpa [Matrix.mulVec, dotProduct] using this
  have hnn : ∀ i j, 0 ≤ (A ^ n) i j := pow_entry_nonneg hA n
  constructor
  · have h1 : ∀ i, c * (∑ j, (A ^ n) i j) ≤ r ^ n * v i := by
      intro i
      rw [← hrow i, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (hcv j) (hnn i j)
    calc c * pathCount A n = ∑ i, c * (∑ j, (A ^ n) i j) := by
            rw [pathCount, Finset.mul_sum]
      _ ≤ ∑ i, r ^ n * v i := Finset.sum_le_sum fun i _ => h1 i
      _ = r ^ n * (∑ i, v i) := by rw [Finset.mul_sum]
  · have h2 : ∀ i, r ^ n * v i ≤ C * (∑ j, (A ^ n) i j) := by
      intro i
      rw [← hrow i, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hvC j) (hnn i j)
    calc r ^ n * (∑ i, v i) = ∑ i, r ^ n * v i := by rw [Finset.mul_sum]
      _ ≤ ∑ i, C * (∑ j, (A ^ n) i j) := Finset.sum_le_sum fun i _ => h2 i
      _ = C * pathCount A n := by rw [pathCount, Finset.mul_sum]
