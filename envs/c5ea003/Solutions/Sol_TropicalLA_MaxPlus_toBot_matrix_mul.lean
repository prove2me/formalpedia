-- Prove2me | solution 1 for TropicalLA.MaxPlus.toBot_matrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:08:24.504593+00:00
-- url     : https://prove2.me/submissions/79f15195-134a-4045-9e36-f52eacecc5c4

-- Sol generated from Algebra/TropicalLinearAlgebra/MaxPlusSemiring.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaxPlusSemiring
/-
# The max-plus (tropical) semiring

We construct the tropical semiring `(R ∪ {-∞}, max, +)` as a type synonym
`MaxPlus R := WithBot R` for a linearly ordered additive commutative monoid `R`
(the motivating case being `R = ℝ`), equip it with a `CommSemiring` structure,
and record its characteristic tropical features:

* it is **idempotent**: `a + a = a`;
* it is **zero-sum-free**: `a + b = 0 → a = 0 ∧ b = 0`, so (for nontrivial `R`)
  it admits no additive inverses and is genuinely not a ring;
* finite tropical sums are suprema (`toBot_sum`);
* consequently tropical matrix multiplication is the `max`-of-sums formula and
  is associative.
-/

open TropicalLA


open MaxPlus





/-- Tropical multiplication is ordinary addition. -/
instance {R : Type*} [Add R] : Mul (MaxPlus R) := ⟨fun a b => ofBot (toBot a + toBot b)⟩

@[simp] theorem toBot_add {R : Type*} [LinearOrder R] (a b : MaxPlus R) :
    toBot (a + b) = max (toBot a) (toBot b) := rfl

variable {R : Type*} [AddCommMonoid R] [LinearOrder R] [IsOrderedAddMonoid R]






/-- A finite tropical sum is the supremum of its terms. -/
theorem toBot_sum {ι : Type*} (s : Finset ι) (f : ι → MaxPlus R) :
    toBot (∑ i ∈ s, f i) = s.sup (fun i => toBot (f i)) := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sup_insert, toBot_add, ih]



variable {ι : Type*} [Fintype ι]






open TropicalLA in
theorem solution(A B : Matrix ι ι (MaxPlus R)) (i j : ι) :
    toBot ((A * B) i j) = Finset.univ.sup (fun k => toBot (A i k) + toBot (B k j)) := by
  rw [Matrix.mul_apply, toBot_sum]
  refine Finset.sup_congr rfl fun k _ => ?_
  rfl
