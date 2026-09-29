-- Prove2me | Theorems.Thm_TropicalLA_exists_uniform_entry_lower_bound
-- name    : TropicalLA.exists_uniform_entry_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:40:11.348062+00:00
-- url     : https://prove2.me/theorems/227f843a-1c96-4a06-8b48-12ceee0d05a1
-- title:
--   Entrywise lower bound.
-- statement:
--   **Entrywise lower bound.**  For `m ≥ q + 1` (with `q` the length of a critical cycle)
--   every entry of `A^{⊗(m+1)}` is at least `(m+1)·lam − (1+q)·|a − lam|`, where `a` is the
--   smallest entry of `A`.  The witness walk enters a critical node in one step, turns `k`
--   times around the critical cycle and leaves along a tail of length `r ≤ q`.
--
--   ```lean
--   theorem TropicalLA.exists_uniform_entry_lower_bound(A : Matrix ι ι ℝ) :
--       ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧ ∀ m : ℕ, N ≤ m → ∀ i j : ι,
--         ((m : ℝ) + 1) * maxCycleMean A - K ≤ tpow A m i j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalCyclicity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalCyclicity.lean#L139

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalCyclicity.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
/-
# Uniform boundedness of normalised tropical powers

`FUTURE_DIRECTIONS.md` (sub-conjecture 1, extracted from conjecture C1 on cyclicity)
proposed that *every* entry of `A^{⊗(m+1)} − (m+1)·λ` lies in the box `[−C, C]` with
`C = spread(v)` the spread of a tropical eigenvector.  This file settles that
sub-conjecture, in the sharp form:

* `tpow_le_spread` — the **upper** half of the conjecture is true exactly as stated:
  `tpow A m i j ≤ (m+1)·λ + spread v` for every eigenvector `v`;
* `no_spread_lower_bound` — the **lower** half is *false*: for
  `A = [[0,−3],[0,−3]]` the constant vector is an eigenvector (spread `0`) while the
  whole second column of every tropical power stays `3` below `(m+1)·λ`;
* `exists_uniform_entry_bound` — but the *boundedness* statement survives with a larger,
  explicitly computable constant: with `q ≤ n` the length of a critical cycle and
  `a = min_{i,j} A i j`,
  `|tpow A m i j − (m+1)·λ| ≤ spread v + (1+q)·|a − λ|` for all `m ≥ q + 1`.
  The lower bound is obtained by *constructing* long walks: one step into a critical
  node, `k` turns around the critical cycle, and a short tail of length `r ≤ q`.
* `tendsto_tpow_div` — consequently the entrywise Gelfand formula holds:
  `tpow A m i j / (m+1) → λ` for *every* pair `(i,j)`, a strengthening of the
  largest-entry version `tendsto_specNorm_div`.

The technical engine is the semigroup law `tpow_add : A^{⊗(a+b+2)} = A^{⊗(a+1)} ⊗ A^{⊗(b+1)}`
together with the critical cycle produced by tropical Perron–Frobenius.
-/

open TropicalLA

open Filter Topology

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## The semigroup law for tropical powers -/



/-! ## Smallest entry -/




/-! ## Upper bound from an eigenvector -/




/-! ## Powers of a critical cycle -/


/-! ## The uniform two-sided entrywise bound -/

theorem TropicalLA.exists_uniform_entry_lower_bound(A : Matrix ι ι ℝ) :
    ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧ ∀ m : ℕ, N ≤ m → ∀ i j : ι,
      ((m : ℝ) + 1) * maxCycleMean A - K ≤ tpow A m i j := by sorry
