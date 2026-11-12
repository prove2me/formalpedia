-- Prove2me | Definitions.Def_BregmanMincWeights
-- name    : BregmanMincWeights
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-16T02:06:35.03725+00:00
-- url     : https://prove2.me/theorems/52d231bb-cd49-4d96-840a-b424962608e2
-- title:
--   Radhakrishnan weight functions for Bregman-Minc
-- statement:
--   Auxiliary definitions for the Bregman-Minc permanent inequality: the A-system set aSys A, row preimage preS A σ i, available-count avail i S π, and Radhakrishnan weight qW A σ π = ∏_i 1/avail(i, preS_i, π).
-- source:
--   Radhakrishnan, J. (2001). An entropy proof of Bregman theorem. Journal of Combinatorial Theory, Series A, 77(1), 161-164.

import Mathlib
open scoped BigOperators

/-!
Auxiliary definitions for the Bregman-Minc permanent inequality (Radhakrishnan 1997 proof).

For a 0-1 matrix A of size n×n with positive row sums d_i, we formalize:
- aSys A: the set of compatible permutations (A-systems)
- preS A σ i: the preimage of row i's support under σ
- avail i S π: count of elements of S at or after i's position in ordering π
- qW A σ π: the Radhakrishnan weight ∏_i 1/avail(i, preS_i, π)
-/

namespace BregmanMincWeights

/-- The set of A-systems: permutations σ such that A i (σ i) = 1 for all i. -/
noncomputable def aSys {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => ∀ i, A i (σ i) = 1)

/-- The preimage of row i's support under σ: all positions l such that A i (σ l) = 1. -/
noncomputable def preS {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun l => A i (σ l) = 1)

/-- The number of elements of S that appear at or after position i in ordering π. -/
noncomputable def avail {n : ℕ} (i : Fin n) (S : Finset (Fin n)) (π : Equiv.Perm (Fin n)) : ℕ :=
  (S.filter (fun t => π.symm i ≤ π.symm t)).card

/-- The Radhakrishnan weight of σ under ordering π:
    the product over all rows i of 1/avail(i, preimage of row i's support, π). -/
noncomputable def qW {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∏ i : Fin n, (1 : ℝ) / (avail i (preS A σ i) π : ℝ)

end BregmanMincWeights


