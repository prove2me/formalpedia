-- Prove2me | solution 1 for Cryptography.IsogenySIDH.three_radical_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:54:06.090319+00:00
-- url     : https://prove2.me/submissions/b354176e-aefa-4e75-9ae0-773487a840ff

-- Sol generated from Cryptography/IsogenySIDH/ThreeIsogenyNonBacktracking.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyMontgomery
import Definitions.Def_Cryptography_IsogenySIDH_ThreeIsogenyNonBacktracking
/-
# Non-backtracking and the radical obstruction for Montgomery 3-isogenies

`ThreeIsogenyMontgomery` uniformised the Montgomery 3-isogeny by the kernel
abscissa `r`: the source is `mont3Source r`, the target is `mont3Target r`, and
the two `j`-invariants are a zero of `Φ₃`.  To *iterate* the construction one
must choose a point of order three on the target, i.e. a root of
`threeDivPoly (mont3Target r) X`.  This file analyses that quartic completely.

* `threeDual_kernel` — `X = -1/(3r)` is always a root: it is the kernel of the
  dual isogeny, so this is the backtracking choice.  (This is the `ℓ = 3`
  analogue of `radTwoIso_two_torsion_image` in `RadicalWalkStructure`.)
* `threeDivPoly_target_factor` — the quartic factors *over the base field* as
  `r · threeDivPoly (mont3Target r) X = (3rX + 1) · threeNextKernelPoly r X`
  with the explicit residual cubic
  `threeNextKernelPoly r X = X³ + 3r(2 - 3r²)X² + 3r²X - r`.
  So a non-backtracking 3-step means choosing a root of that cubic.
* `threeNextKernelPoly_depressed` — the Tschirnhaus shift `X = Y - r(2 - 3r²)`
  depresses the cubic to `Y³ + 9r²(3r² - 1)(1 - r²) Y + threeDepressedConst r`.
* `three_radical_obstruction` — **a negative result.**  Away from the loci
  `r = 0`, `r² = 1` and `3r² = 1` the depressed cubic has *nonzero* linear
  coefficient, hence it is never of the form `Y³ - c`: the abscissa of the next
  kernel is *not* obtainable by extracting a single cube root in the Montgomery
  coordinate.  This is why radical 3-isogeny formulas are written in Tate normal
  form rather than in Montgomery form, and it delimits precisely how far the
  `ℓ = 2` picture (where `α² = A + 2` *is* a single square root) generalises.
  The hypothesis `3 ≠ 0` is necessary: in characteristic three the cubic
  degenerates to `X³ - r`, which is a pure cube.
* `three_radical_locus` — **and the exception.**  Exactly on the locus
  `3r² = 1` the cubic collapses to the pure cube `(X + r)³ - 4r/3`, so there the
  next kernel *is* given by one cube root.
-/

set_option maxHeartbeats 1000000

open Cryptography.IsogenySIDH

variable {K : Type*} [Field K]

/-! ## The dual kernel -/


/-! ## The residual cubic -/




/-! ## Depressing the cubic -/


/-- The Tschirnhaus shift removes the quadratic term of the residual cubic; the
resulting linear coefficient is `9r²(3r² - 1)(1 - r²)`. -/
theorem threeNextKernelPoly_depressed (r Y : K) :
    threeNextKernelPoly r (Y - r * (2 - 3 * r ^ 2))
      = Y ^ 3 + 9 * r ^ 2 * (3 * r ^ 2 - 1) * (1 - r ^ 2) * Y + threeDepressedConst r := by
  simp only [threeNextKernelPoly, threeDepressedConst]
  ring




open Cryptography.IsogenySIDH in
theorem solution{r : K} (htwo : (2 : K) ≠ 0) (hthree : (3 : K) ≠ 0)
    (hr : r ≠ 0) (h1 : r ^ 2 - 1 ≠ 0) (h3 : 3 * r ^ 2 - 1 ≠ 0) :
    ¬ ∃ c : K, ∀ Y : K, threeNextKernelPoly r (Y - r * (2 - 3 * r ^ 2)) = Y ^ 3 - c := by
  rintro ⟨c, hc⟩
  have h9 : (9 : K) ≠ 0 := by
    have h : (9 : K) = 3 * 3 := by norm_num
    rw [h]; exact mul_ne_zero hthree hthree
  have hL : 9 * r ^ 2 * (3 * r ^ 2 - 1) * (1 - r ^ 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero h9 (pow_ne_zero 2 hr)) h3) ?_
    intro h
    exact h1 (by linear_combination -h)
  have e1 := hc 1
  have e2 := hc (-1)
  rw [threeNextKernelPoly_depressed] at e1 e2
  have hsum : 2 * (9 * r ^ 2 * (3 * r ^ 2 - 1) * (1 - r ^ 2)) = 0 := by
    linear_combination e1 - e2
  rcases mul_eq_zero.mp hsum with h | h
  · exact htwo h
  · exact hL h
