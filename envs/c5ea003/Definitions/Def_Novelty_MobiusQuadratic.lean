-- Prove2me | Definitions.Def_Novelty_MobiusQuadratic
-- name    : Novelty_MobiusQuadratic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:45.34924+00:00
-- url     : https://prove2.me/theorems/bf4da8d6-508e-460a-8d87-ac2f6cb58e40
-- title:
--   Aether Catalog definitions — Novelty_MobiusQuadratic
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MobiusQuadratic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MobiusQuadratic.lean by skeleton subtraction
import Mathlib

/-!
# Möbius action on real quadratic irrationals (Phase A, v19c)

For an integer `2×2` matrix `M = ![![p, q], ![r, s]]` with `det M = p s - q r ≠ 0`, the
*linear fractional* (Möbius) action on a real number is

`mobius p q r s x = (p x + q) / (r x + s)`.

This is the action that underlies the **ratio spectrum** `k(M x) / k(x)` of the
Lagarias–Shallit theory of Lagrange constants under integer linear fractional
transformations.  Before one can speak of the spectrum restricted to real
quadratic irrational badly approximable numbers, one needs the basic *closure*
fact:

> the Möbius image of a real quadratic irrational under an integer matrix of
> nonzero determinant is again a real quadratic irrational.

This is exactly the algebraic shadow of Lagrange's theorem (real quadratic
irrationals = Filter.eventually periodic continued fractions): the `GL₂(ℤ)`-class of an
Filter.eventually periodic continued fraction is preserved, and more generally any
integer nonzero-determinant matrix maps the quadratic-irrational locus into
itself.

Main results:

* `RatioSpectrum.quadForm_ne_zero` — for an irrational root `x` of
  `a x² + b x + c` (`a ≠ 0`), the binary quadratic form `a m² - b m n + c n²`
  has no nontrivial integer zero.  (Discriminant non-square ⇒ anisotropic.)
* `RatioSpectrum.irrational_mobius` — the Möbius image of an irrational number
  under an integer matrix of nonzero determinant is irrational.
* `RatioSpectrum.QuadIrr` — predicate: real quadratic irrational.
* `RatioSpectrum.quadIrr_mobius` — **closure**: the Möbius image of a quadratic
  irrational is a quadratic irrational.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the ratio spectrum `k(Mx)/k(x)` is only well-posed if
the restriction class (real quadratic irrationals) is *invariant* under the
integer Möbius action.  Bold form: invariance holds for every integer matrix of
nonzero determinant, not merely for `GL₂(ℤ)`.

Experiment (Experimenter): closure splits into (i) irrationality of the image and
(ii) producing an integer quadratic vanishing on the image.  Substituting the
inverse Möbius map `x = (s y - q)/(p - r y)` into `a x² + b x + c = 0` and
clearing `(p - r y)²` yields an integer quadratic in `y` with leading coefficient
`a s² - b s r + c r² = quadForm`.  Anisotropy of `quadForm` (the discriminant
`b² - 4ac` is not a perfect square because `x` is irrational) forces this leading
coefficient to be nonzero, so the image is genuinely degree two.

Analysis (Analyst): the only delicate point is the leading coefficient.  The
clean device is `4a·(a m² - b m n + c n²) = (2 a m - b n)² - (b²-4ac) n²`, which
reduces anisotropy to "`b²-4ac` is not a rational square", itself equivalent to
irrationality of `2 a x + b` (and hence of `x`).

Critique (Critic): the determinant hypothesis is load-bearing twice — it forces
`(s, r) ≠ (0,0)` (else `quadForm` is the zero form) and it forces irrationality
of the image (a degenerate matrix can collapse `x` to a constant).  The
denominator hypothesis `r x + s ≠ 0` is necessary for `mobius` to be a genuine
real number.

Synthesis (PI): closure of the quadratic-irrational locus is the structural
prerequisite for the ratio-spectrum density program; it isolates the algebra from
the (much harder) continued-fraction dynamics.
-/

namespace RatioSpectrum

open scoped Classical

/-- The Möbius (linear fractional) action of the integer matrix `![![p,q],![r,s]]`
on a real number. -/
noncomputable def mobius (p q r s : ℤ) (x : ℝ) : ℝ :=
  ((p : ℝ) * x + q) / ((r : ℝ) * x + s)

/-- Real quadratic irrational: irrational and a root of an integer quadratic with
nonzero leading coefficient. -/
def QuadIrr (x : ℝ) : Prop :=
  Irrational x ∧ ∃ a b c : ℤ, a ≠ 0 ∧ (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0

/-
For `a ≠ 0`, `2 a x + b` is irrational whenever `x` is.
-/

/-
**Anisotropy of the quadratic form.**  If `x` is an irrational root of
`a x² + b x + c` with `a ≠ 0`, then the binary form `a m² - b m n + c n²`
(the leading coefficient of the transformed quadratic) has no nontrivial integer
zero.
-/

/-
**Irrationality of the Möbius image.**  Under an integer matrix of nonzero
determinant the Möbius image of an irrational number is irrational.
-/

/-
**Closure of the quadratic-irrational locus under the integer Möbius action.**
The image of a real quadratic irrational under an integer matrix of nonzero
determinant (with nonvanishing denominator) is again a real quadratic irrational.
-/

end RatioSpectrum


