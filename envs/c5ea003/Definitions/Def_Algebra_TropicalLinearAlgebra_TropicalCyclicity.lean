-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
-- name    : Algebra_TropicalLinearAlgebra_TropicalCyclicity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:30:44.241789+00:00
-- url     : https://prove2.me/theorems/a510cfbb-99a5-4c43-a249-dca577ddc113
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_TropicalCyclicity
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.TropicalCyclicity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/TropicalCyclicity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
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

namespace TropicalLA

open Filter Topology

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## The semigroup law for tropical powers -/



/-! ## Smallest entry -/

/-- The smallest entry of `A`; a crude but uniform lower bound on any single step. -/
noncomputable def minEntry (A : Matrix ι ι ℝ) : ℝ :=
  (Finset.univ : Finset (ι × ι)).inf' Finset.univ_nonempty fun p => A p.1 p.2



/-! ## Upper bound from an eigenvector -/

/-- The spread of a vector: the difference between its largest and smallest entries. -/
noncomputable def spread (v : ι → ℝ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := ι)) v
    - Finset.univ.inf' (Finset.univ_nonempty (α := ι)) v



/-! ## Powers of a critical cycle -/


/-! ## The uniform two-sided entrywise bound -/




/-! ## The spread is *not* a lower bound: refutation of the naive box conjecture -/


end TropicalLA


