-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
-- name    : Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:29:11.916994+00:00
-- url     : https://prove2.me/theorems/1ab267c6-2a80-4533-8756-d3fcf394e0d1
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.TropicalPerronFrobenius`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/TropicalPerronFrobenius.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
/-
# Tropical Perron–Frobenius: existence of the eigenvalue

This file completes the max-plus spectral theory of `TropicalEigenvalue.lean` by
proving **existence**: every matrix with finite real entries has a tropical
eigenvalue, namely its maximum cycle mean, together with an explicit eigenvector
built from the Kleene star (optimal-path) matrix of the normalised matrix.

The combinatorial engine is `pathWeight_excise`: a walk that repeats a vertex
splits into a shorter walk with the same endpoints plus a closed sub-walk.
Together with the pigeonhole principle this yields

* `cycle_le_maxCycleMean` : *every* closed walk, of any length, has weight at most
  `length · λ` where `λ` is the maximum mean over closed walks of length `≤ n`;
* `exists_short_walk_ge`  : when all cycles are nonpositive, every walk is dominated
  by one of length at most `n` with the same endpoints;
* `exists_tropEigen`      : **tropical Perron–Frobenius** — `A` has the eigenvalue
  `maxCycleMean A`, with an eigenvector given by optimal paths into a critical node.

Combined with `tropEigenvalue_unique` this says: a max-plus matrix with finite
entries has *exactly one* eigenvalue, the maximum cycle mean.
-/

namespace TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]

section Excision



end Excision

section MaxCycleMean

variable (A : Matrix ι ι ℝ)

theorem cycleIndex_nonempty :
    ((Finset.range (Fintype.card ι)) ×ˢ (Finset.univ : Finset ι)).Nonempty := by
  refine Finset.Nonempty.product ?_ Finset.univ_nonempty
  exact Finset.nonempty_range_iff.mpr (Fintype.card_ne_zero)

/-- The **maximum cycle mean** of `A`: the largest mean weight of a closed walk of
length at most `n = |ι|`.  (Theorem `cycle_le_maxCycleMean` shows longer cycles cannot
do better.) -/
noncomputable def maxCycleMean : ℝ :=
  ((Finset.range (Fintype.card ι)) ×ˢ (Finset.univ : Finset ι)).sup'
    (cycleIndex_nonempty) (fun q => tpow A q.1 q.2 q.2 / (q.1 + 1))

variable {A}






end MaxCycleMean

section Existence

variable {A : Matrix ι ι ℝ}




/-- The Kleene-star (optimal path) vector: `v j` is the best weight of a walk of length
between `1` and `n` from `j` to the base point `i₀`. -/
noncomputable def kleeneVec (B : Matrix ι ι ℝ) (i₀ : ι) : ι → ℝ :=
  fun j => (Finset.range (Fintype.card ι)).sup'
    (Finset.nonempty_range_iff.mpr Fintype.card_ne_zero) (fun k => tpow B k j i₀)






end Existence

end TropicalLA


