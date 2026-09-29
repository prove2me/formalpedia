-- Prove2me | solution 1 for QuasiSymmetricComposition.AntilipschitzOnWith.comp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:19:53.047908+00:00
-- url     : https://prove2.me/submissions/d93dfb2f-b0dd-4783-8df6-59672392015a

-- Sol generated from Geometry/NumberTheory/QuasiSymmetricComposition.lean
import Mathlib
import Definitions.Def_Geometry_NumberTheory_QuasiSymmetricComposition
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Set-local distortion of Hausdorff dimension: the composition layer

Mathlib records how *global* maps distort Hausdorff dimension:
`LipschitzOnWith.dimH_image_le` (Lipschitz maps do not increase `dimH`),
`HolderOnWith.dimH_image_le` (a Hölder map of exponent `r` divides `dimH` by `r`),
and `AntilipschitzWith.le_dimH_image` (a *globally* antilipschitz map does not
decrease `dimH`).  The last one is only available globally; there is no
set-local antilipschitz predicate in Mathlib.

This file introduces `QuasiSymmetricComposition.AntilipschitzOnWith`, the
set-local analogue of `AntilipschitzWith`, and develops exactly the closure and
distortion theory needed to run a *composition / semigroup* programme on
Hausdorff dimension:

* `AntilipschitzOnWith.injOn` — a set-local antilipschitz map is injective on `s`;
* `AntilipschitzOnWith.le_dimH_image` — the missing set-local lower bound
  `dimH s ≤ dimH (f '' s)`, proved by feeding the (Lipschitz) left inverse
  `Function.invFunOn f s` into `LipschitzOnWith.dimH_image_le`;
* `AntilipschitzOnWith.comp` — closure under composition, constants multiplying;
* `dimH_image_eq` — a set-local bi-Lipschitz map preserves `dimH (f '' s)`;
* `dimH_image_comp_eq` — bi-Lipschitz maps compose to a dimension-preserving map;
* `dimH_image_comp_holder_le` — the product-exponent composite Hölder bound.

These are the foundations consumed by `Geometry/QuasiSymmetricIterate.lean`,
which specialises composition to the self-map / iteration setting.
-/


open MeasureTheory Set Function
open scoped NNReal ENNReal

open QuasiSymmetricComposition

variable {X Y Z : Type*} [EMetricSpace X] [EMetricSpace Y] [EMetricSpace Z]
variable {K K' : ℝ≥0} {f : X → Y} {s : Set X}

/-
!-- Lab Notebook -- !--
Hypothesis:  The bi-Lipschitz invariance `dimH (f '' s) = dimH s` should be
  recoverable set-locally, even though Mathlib only exposes the antilipschitz
  lower bound for *globally* defined maps (`AntilipschitzWith.le_dimH_image`).
Result:      Defining `AntilipschitzOnWith` and routing through the Lipschitz
  left inverse `Function.invFunOn f s` recovers the lower bound, giving
  `dimH_image_eq` with no global hypotheses on `f`.
Insight:     The set-local lower bound is *not* new geometry — it is the
  global upper bound `LipschitzOnWith.dimH_image_le` applied to the inverse map.
  Antilipschitz-on-`s` is precisely "the inverse is Lipschitz on `f '' s`".
Failure:     A direct `rw [← LeftInvOn.image_image]` rewrote *both* copies of `s`
  in `dimH s ≤ dimH (f '' s)`; isolating the left-hand `s` via a `calc` step
  (rewriting only the equality's RHS) fixed it.
-/


/-
!-- If `f x = f y` for `x, y ∈ s` then `edist x y ≤ K · 0 = 0`, so `x = y`. -!--
A set-local antilipschitz map is injective on its set. -/

/-
!-- The left inverse `g = invFunOn f s` is `K`-Lipschitz on `f '' s` (this is
exactly the antilipschitz inequality read backwards), and `g '' (f '' s) = s`, so
`dimH s = dimH (g '' (f '' s)) ≤ dimH (f '' s)` by `LipschitzOnWith.dimH_image_le`. -!--

The set-local lower bound: a set-local antilipschitz map does not decrease the
Hausdorff dimension of `s`.  This is the set-local analogue of
`AntilipschitzWith.le_dimH_image`. -/

/-
!-- Chain the two antilipschitz inequalities: `edist x y ≤ Kf · edist (f x) (f y)`
and `edist (f x) (f y) ≤ Kg · edist (g (f x)) (g (f y))`, multiplying constants. -!--

Closure under composition: set-local antilipschitz maps compose, with constants
multiplying.  (Here `f` maps `s` into `t` and `g` is antilipschitz on `t`.) -/

/-
!-- Antisymmetry of `≤`: the Lipschitz hypothesis gives `≤`, the antilipschitz
hypothesis gives `≥`. -!--

A set-local bi-Lipschitz map preserves the Hausdorff dimension of `s`. -/

/-
!-- `LipschitzOnWith.comp` and `AntilipschitzOnWith.comp` make `g ∘ f` bi-Lipschitz
on `s`; apply `dimH_image_eq`. -!--

Bi-Lipschitz maps compose to a dimension-preserving map: if `f` is set-local
bi-Lipschitz on `s` into `t` and `g` is set-local bi-Lipschitz on `t`, then
`g ∘ f` preserves `dimH (· '' s)`. -/

/-
!-- `HolderOnWith.comp` multiplies the exponents to `rg * rf`; feed the composite
into `HolderOnWith.dimH_image_le` with `0 < rg * rf`. -!--

The product-exponent composite Hölder distortion bound: composing Hölder maps of
exponents `rf`, `rg` divides the dimension by their product `rg * rf`. -/


open QuasiSymmetricComposition in
theorem solution{Kg Kf : ℝ≥0} {g : Y → Z} {f : X → Y} {t : Set Y}
    (hg : AntilipschitzOnWith Kg g t) (hf : AntilipschitzOnWith Kf f s)
    (hmaps : MapsTo f s t) : AntilipschitzOnWith (Kf * Kg) (g ∘ f) s := by
  intro x hx y hy
  calc edist x y ≤ Kf * edist (f x) (f y) := hf hx hy
    _ ≤ (Kf : ℝ≥0∞) * (Kg * edist (g (f x)) (g (f y))) := by
        gcongr; exact hg (hmaps hx) (hmaps hy)
    _ = ((Kf * Kg : ℝ≥0) : ℝ≥0∞) * edist (g (f x)) (g (f y)) := by
        rw [ENNReal.coe_mul]; ring
