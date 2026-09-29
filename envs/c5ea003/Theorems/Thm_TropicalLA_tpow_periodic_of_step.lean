-- Prove2me | Theorems.Thm_TropicalLA_tpow_periodic_of_step
-- name    : TropicalLA.tpow_periodic_of_step
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:42:42.150473+00:00
-- url     : https://prove2.me/theorems/22e518d3-dcd4-46b4-bfe5-11762d7dbd46
-- title:
--   Propagation of one exact relation.
-- statement:
--   **Propagation of one exact relation.**  If a single tropical power satisfies
--   `tpow A (M₀ + p) = c + tpow A M₀` entrywise, the same relation holds for all larger
--   exponents.
--
--   ```lean
--   theorem TropicalLA.tpow_periodic_of_step{A : Matrix ι ι ℝ} {M₀ p : ℕ} {c : ℝ}
--       (h : tpow A (M₀ + p) = fun i j => c + tpow A M₀ i j) :
--       ∀ m, M₀ ≤ m → tpow A (m + p) = fun i j => c + tpow A m i j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalCyclicityInteger.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalCyclicityInteger.lean#L102

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalCyclicityInteger.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
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

theorem TropicalLA.tpow_periodic_of_step{A : Matrix ι ι ℝ} {M₀ p : ℕ} {c : ℝ}
    (h : tpow A (M₀ + p) = fun i j => c + tpow A M₀ i j) :
    ∀ m, M₀ ≤ m → tpow A (m + p) = fun i j => c + tpow A m i j := by sorry
