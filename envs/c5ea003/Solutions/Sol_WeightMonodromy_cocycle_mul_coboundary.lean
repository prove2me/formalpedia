-- Prove2me | solution 1 for WeightMonodromy.cocycle_mul_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:14:28.21393+00:00
-- url     : https://prove2.me/submissions/caa4551c-6c64-4531-8218-07d81043722f

-- Sol generated from Novelty/WeightMonodromyCohomologyAlgebra.lean
import Mathlib
import Definitions.Def_Novelty_WeightMonodromyCohomologyAlgebra
import Definitions.Def_Novelty_WeightMonodromyFormality
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# The cohomology algebra of a weight-graded dg-algebra, and its strict diagonal model

Companion to `Catalog/Novelty/WeightMonodromyFormality.lean`.

The first part sets up the multiplicative structure of cohomology for a `WeightedDGA`:
cocycles form a subalgebra and coboundaries a two-sided ideal in it, so that `H = Z / B` is a
`k`-algebra.  Note that the Leibniz rule is only postulated for *bihomogeneous* elements, so
these statements genuinely require the bigraded decomposition (they are proved componentwise).

The second part upgrades formality to its sharpest strict form under purity: the *diagonal*
cocycles (bidegree `(n, n)`, i.e. weight = degree, the shape produced by weight-monodromy)
form a subalgebra `diagAlg` on which the differential vanishes identically and which surjects
onto the cohomology algebra.  Consequently the cohomology algebra of `A` is the quotient of an
honest subalgebra of `A` with zero differential — a *strict multiplicative lift* of `H`.
-/

open WeightMonodromy

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜] (D : WeightedDGA 𝒜)

/-! ### Cocycles form a subalgebra, coboundaries a two-sided ideal -/




/-! ### The diagonal subalgebra of pure cocycles -/








open StrictSectionData

variable {D}






/-! ### Subalgebra packaging -/






open WeightMonodromy in
theorem solution{a : A} (ha : D.d a = 0) (c : A) :
    ∃ e : A, a * D.d c = D.d e := by
  refine ⟨∑ i ∈ supp 𝒜 a, (D.sgn i.1)⁻¹ • (cmpL 𝒜 i a * c), ?_⟩
  have ha' : a = ∑ i ∈ supp 𝒜 a, cmpL 𝒜 i a := (sum_cmpL 𝒜 a).symm
  rw [map_sum]
  calc a * D.d c = ∑ i ∈ supp 𝒜 a, cmpL 𝒜 i a * D.d c := by
        conv_lhs => rw [ha']
        rw [Finset.sum_mul]
    _ = ∑ i ∈ supp 𝒜 a, D.d ((D.sgn i.1)⁻¹ • (cmpL 𝒜 i a * c)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, D.leibniz i.1 i.2 _ c (by simpa using cmpL_mem 𝒜 a i),
          D.cmpL_cocycle ha i, zero_mul, zero_add, smul_smul,
          inv_mul_cancel₀ (D.sgn_ne_zero i.1), one_smul]
