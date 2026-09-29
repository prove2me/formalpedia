-- Prove2me | Theorems.Thm_TropicalLA_isTropEigen_const_mul
-- name    : TropicalLA.isTropEigen_const_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:43:59.694001+00:00
-- url     : https://prove2.me/theorems/74e9aa2d-881c-4c05-8ab8-6f15a1bfe588
-- title:
--   Multiplying all entries by `c ≥ 0` multiplies the eigenvalue and the eigenvector by `c`.
-- statement:
--   Multiplying all entries by `c ≥ 0` multiplies the eigenvalue and the eigenvector by `c`.
--
--   ```lean
--   theorem TropicalLA.isTropEigen_const_mul(hc : 0 ≤ c) (h : IsTropEigen A lam v) :
--       IsTropEigen (Matrix.of fun i j => c * A i j) (c * lam) (fun i => c * v i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalCyclicityInteger.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalCyclicityInteger.lean#L222

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalCyclicityInteger.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
/-
# Cyclicity of tropical powers for integer matrices

This file settles conjecture **C1** of `FUTURE_DIRECTIONS.md` — *tropical powers are
eventually exactly periodic* — for matrices with integer entries (equivalently, after
rescaling, for matrices with rational entries):

  `exists_cyclicity`: for `A` with integer entries there are a period `p ≥ 1` and a
  transient `N` such that for all `m ≥ N`

      `A^{⊗(m+p+1)} = (p·λ) ⊗ A^{⊗(m+1)}`,  i.e.  `tpow A (m+p) = fun i j => p*λ + tpow A m i j`,

  where `λ = maxCycleMean A`.

The proof is exactly the strategy outlined in the conjecture, now made precise:

1. entries of tropical powers of an integer matrix are integers (`tpow_isInt`);
2. `q·λ` is an integer, where `q ≤ n` is the length of a critical cycle
   (`exists_critical_cycle_int`);
3. by `exists_uniform_entry_bound` the normalised powers `A^{⊗(m+1)} − (m+1)λ` live in a
   fixed compact box, so along the arithmetic progression `m = N + t·q` the *integer*
   matrices `A^{⊗(m+1)} − t·(qλ)` take only finitely many values;
4. pigeonhole gives two equal terms, i.e. one exact relation
   `tpow A (M₀ + p) = p·λ + tpow A M₀`;
5. the relation propagates to all later exponents because tropical multiplication commutes
   with adding a constant (`tmul_const_add`).

Boundedness alone does not give periodicity over ℝ; integrality is what makes the box
finite, and that is exactly the hypothesis used here.
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]









/-! ## Positive rescaling, and cyclicity for commensurable entries -/


variable {A : Matrix ι ι ℝ} {lam c : ℝ} {v : ι → ℝ}

theorem TropicalLA.isTropEigen_const_mul(hc : 0 ≤ c) (h : IsTropEigen A lam v) :
    IsTropEigen (Matrix.of fun i j => c * A i j) (c * lam) (fun i => c * v i) := by sorry
