-- Prove2me | Definitions.Def_Bridges_SubmultiplicativeSearchEntropy
-- name    : Bridges_SubmultiplicativeSearchEntropy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:17.258913+00:00
-- url     : https://prove2.me/theorems/3385d95a-ea75-4587-9691-359f7ecbaba9
-- title:
--   Aether Catalog definitions — Bridges_SubmultiplicativeSearchEntropy
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SubmultiplicativeSearchEntropy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SubmultiplicativeSearchEntropy.lean by skeleton subtraction
import Mathlib

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

namespace SubmultiplicativeSearchEntropy

/-! ## Part 1 — Submultiplicative counting functions and Fekete's lemma -/

/-- A *search profile* is a counting function `N : ℕ → ℝ` for the successful prefixes of each
length. It is submultiplicative and everywhere at least `1`. -/
structure SearchProfile where
  /-- number of successful prefixes of length `n` -/
  N : ℕ → ℝ
  one_le : ∀ n, 1 ≤ N n
  submul : ∀ m n, N (m + n) ≤ N m * N n

namespace SearchProfile

variable (P : SearchProfile)


/-- The finite-scale rate at length `n`: `log N n / n`. -/
noncomputable def rate (n : ℕ) : ℝ := Real.log (P.N n) / n




/-- The **entropy (growth) rate** of a search profile: the infimum of its finite-scale rates. -/
noncomputable def growthRate : ℝ := sInf (P.rate '' Ici 1)







/-- The **proof-search dimension** of a profile relative to an ambient branching factor `b`:
the growth rate normalized by `log b`. -/
noncomputable def searchDim (b : ℝ) : ℝ := P.growthRate / Real.log b



end SearchProfile

/-! ## Part 2 — Nonnegative matrices: path counts of a finite-state pruning automaton -/

section Matrices

variable {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}

/-- Entrywise nonnegativity is preserved by matrix powers. -/
lemma pow_entry_nonneg (hA : ∀ i j, 0 ≤ A i j) : ∀ (n : ℕ) (i j), 0 ≤ (A ^ n) i j := by
  intro n
  induction n with
  | zero => intro i j; by_cases h : i = j <;> simp [h]
  | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

/-- The number of length-`n` paths of the automaton with transition matrix `A`:
the sum of all entries of `A ^ n`. -/
def pathCount (A : Matrix (Fin k) (Fin k) ℝ) (n : ℕ) : ℝ := ∑ i, ∑ j, (A ^ n) i j


/-- **Submultiplicativity of path counts.** For a nonnegative matrix, the total number of
length-`(m+n)` paths is at most the product of the counts at lengths `m` and `n`. -/
theorem pathCount_submul (hA : ∀ i j, 0 ≤ A i j) (m n : ℕ) :
    pathCount A (m + n) ≤ pathCount A m * pathCount A n := by
  set f : Fin k → ℝ := fun l => ∑ i, (A ^ m) i l with hf
  set g : Fin k → ℝ := fun l => ∑ j, (A ^ n) l j with hg
  have hfnn : ∀ l, 0 ≤ f l := fun l =>
    Finset.sum_nonneg fun _ _ => pow_entry_nonneg hA m _ _
  have hgnn : ∀ l, 0 ≤ g l := fun l =>
    Finset.sum_nonneg fun _ _ => pow_entry_nonneg hA n _ _
  have key : pathCount A (m + n) = ∑ l, f l * g l := by
    unfold pathCount
    rw [pow_add]
    simp only [Matrix.mul_apply]
    calc ∑ i, ∑ j, ∑ l, (A ^ m) i l * (A ^ n) l j
        = ∑ i, ∑ l, ∑ j, (A ^ m) i l * (A ^ n) l j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ j, (A ^ m) i l * (A ^ n) l j := Finset.sum_comm
      _ = ∑ l, f l * g l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hf, hg, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  have hm : pathCount A m = ∑ l, f l := Finset.sum_comm
  have hn : pathCount A n = ∑ l, g l := rfl
  rw [key, hm, hn, Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ => hgnn i)
    (Finset.mem_univ l)) (hfnn l)

/-! ### Perron eigenvectors control path counts -/

variable {r : ℝ}



end Matrices

/-! ## Part 3 — The growth rate of a Perron-controlled search equals `log r` -/



/-! ## Part 4 — The bridge theorem: Perron root = entropy = dimension -/

section Bridge

variable {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} {r : ℝ}



/-- The search profile attached to a pruning automaton whose path counts never vanish. -/
noncomputable def automatonProfile (A : Matrix (Fin k) (Fin k) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (h1 : ∀ n, 1 ≤ pathCount A n) : SearchProfile where
  N := pathCount A
  one_le := h1
  submul := pathCount_submul hA




end Bridge

/-! ## Part 5 — Worked instances

### 5a. Uniform self-similar search: the classical similarity dimension

A `1 × 1` transition matrix `!![s]` models a uniformly self-similar problem in which exactly `s`
of the branches at each node extend to a proof; the bridge recovers the classical similarity
dimension `log s / log b` of the earlier scalar theory. -/

section Uniform

variable {s : ℝ}



end Uniform

/-! ### 5b. The Fibonacci pruning automaton and the golden ratio

Inside the binary search tree, prune every branch that would use two "expensive" inference steps
in a row.  The accepted paths are counted by the transition matrix `!![1,1;1,0]`, whose path
counts are Fibonacci numbers and whose Perron root is the golden ratio; the resulting
proof-search dimension is `log φ / log 2 ≈ 0.6942`. -/

section Fibonacci

/-- Transition matrix of the "no two consecutive marked steps" pruning automaton. -/
def fibMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]








end Fibonacci

end SubmultiplicativeSearchEntropy


