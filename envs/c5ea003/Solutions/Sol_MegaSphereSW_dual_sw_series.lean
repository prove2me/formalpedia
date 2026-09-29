-- Prove2me | solution 1 for MegaSphereSW.dual_sw_series
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:39:49.015265+00:00
-- url     : https://prove2.me/submissions/64ae096c-4edb-4ad2-a839-844efee1de80

-- Sol generated from Novelty/MegaSphereStiefelWhitney.lean
import Mathlib
import Definitions.Def_Novelty_MegaSphereStiefelWhitney

/-!
# The Mega-Sphere II: The cohomology ring and Stiefel–Whitney classes

The infinite real projective space `ℝP^∞` is the classifying space `BO(1)` of
real line bundles, and it is the natural "all dimensions at once" home of the
tautological line bundle `L`.  Its mod-`2` cohomology ring is the polynomial
ring on the first Stiefel–Whitney class `w = w₁(L)`:

  `H*(ℝP^∞; 𝔽₂) ≅ 𝔽₂[w]`.

This file takes that polynomial ring as the algebraic model of the cohomology
ring and proves genuine ring-theoretic incarnations of characteristic-class
identities, working over `𝔽₂ = ZMod 2`.  Write `w := X` for the degree-`1`
generator (the universal Stiefel–Whitney class).

Main results:

* `MegaSphereSW.sw_basis` — the powers `wⁿ = w₁ⁿ` are `𝔽₂`-linearly independent,
  i.e. the cohomology ring is a free module with exactly one generator in each
  degree.  This is `Hⁿ(ℝP^∞;𝔽₂) ≅ 𝔽₂` for every `n`.
* `MegaSphereSW.sw_whitney_frobenius` — the Frobenius/Whitney identity
  `(1 + w)^{2^k} = 1 + w^{2^k}`: the total Stiefel–Whitney class of the
  `2^k`-fold Whitney sum `L^{⊕2^k}` is `1 + w^{2^k}`.
* `MegaSphereSW.sw_not_isUnit` — the total class `1 + w` is **not** a unit in the
  polynomial (finite-dimensional truncated) cohomology ring.
* `MegaSphereSW.dual_sw_series` — but after completing to power series (the mega
  ring `𝔽₂⟦w⟧`), `1 + w` **becomes** a unit, with inverse the geometric series
  `∑ wᵏ`; its coefficients are the *dual* Stiefel–Whitney classes `w̄ₖ = wᵏ`,
  all equal to `1`.
* `MegaSphereSW.sw_isUnit_completion` — hence `1 + w` is a unit in `𝔽₂⟦w⟧`.
-/

open MegaSphereSW

open Polynomial PowerSeries


/-! ## The graded structure: one class in each degree -/




/-! ## The Whitney / Frobenius identity -/



/-! ## The total class is not a unit before completion -/


/-! ## The mega ring: completing to power series -/







open MegaSphereSW in
theorem solution:
    (1 + wSeries) * dualSWSeries = 1 := by
  rw [dualSWSeries, wSeries]
  have h := PowerSeries.mk_one_mul_one_sub_eq_one (ZMod 2)
  have hm1 : (-1 : PowerSeries (ZMod 2)) = 1 := by
    have h2 : ((-1 : ZMod 2)) = (1 : ZMod 2) := by decide
    have hh : (PowerSeries.C (R := ZMod 2)) ((-1 : ZMod 2))
        = (PowerSeries.C (R := ZMod 2)) (1 : ZMod 2) := by rw [h2]
    rw [map_neg, map_one] at hh
    exact hh
  have hnegX : (-(PowerSeries.X : PowerSeries (ZMod 2))) = PowerSeries.X := by
    rw [← neg_one_mul, hm1, one_mul]
  have he : (1 - (PowerSeries.X : PowerSeries (ZMod 2))) = 1 + PowerSeries.X := by
    rw [sub_eq_add_neg, hnegX]
  rw [mul_comm, ← he]
  exact h
