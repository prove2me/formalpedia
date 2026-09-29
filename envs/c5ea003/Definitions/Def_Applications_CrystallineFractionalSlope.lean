-- Prove2me | Definitions.Def_Applications_CrystallineFractionalSlope
-- name    : Applications_CrystallineFractionalSlope
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:54.071923+00:00
-- url     : https://prove2.me/theorems/34481189-9853-45c2-9204-8f7a0c1d5da3
-- title:
--   Aether Catalog definitions — Applications_CrystallineFractionalSlope
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CrystallineFractionalSlope`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CrystallineFractionalSlope.lean by skeleton subtraction
import Mathlib

/-!
# Irreducibility of mod `p` reductions of crystalline representations at fractional slope

For an odd prime `p`, an even weight `k ≥ 2`, and a Frobenius trace `a_p` in the
algebraic closure of `ℚ_p` with valuation `v(a_p) > 0` that is *not* an integer
(a **fractional slope**), a folklore conjecture asserts that the semisimplified mod `p`
reduction `V̄_{k,a_p}` of the two–dimensional crystalline representation `V_{k,a_p}`
of `G_{ℚ_p}` is **irreducible**.

This file isolates the *arithmetic engine* behind the conjecture. The two Frobenius
eigenvalues of `V_{k,a_p}` are the roots of the polynomial

  `X² − a_p·X + p^{k−1}`,

whose Newton polygon (normalising `v(p) = 1`) has vertices `(0, k−1)`, `(1, v(a_p))`,
`(2, 0)`. When `v(a_p) < (k−1)/2` the polygon breaks, and the two root valuations
(the *Frobenius slopes*) are

  `lowSlope  = v(a_p)`,      `highSlope = (k−1) − v(a_p)`.

A reducible reduction would express `V̄` as a sum of two crystalline characters, each
of whose Frobenius slopes is an **integer**. Thus a fractional slope is an obstruction
to reducibility: both Newton slopes are then non-integral and distinct. We complement
this valuation-theoretic layer with the linear-algebra layer that governs irreducibility
of any two–dimensional representation: a representation with Frobenius trace `a` and
determinant `d` acquires an invariant line exactly when its characteristic polynomial
`X² − a·X + d` has a root, i.e. when the discriminant `a² − 4d` is a square. The two
layers together form a *cross-domain bridge* (`p`-adic valuations ↔ quadratic linear
algebra) which is the conceptual heart of the fractional-slope irreducibility statement.

## Main results

* `CrystallineFractionalSlope.slopes_sum` — the two Frobenius slopes sum to `k − 1`.
* `CrystallineFractionalSlope.lowSlope_lt_highSlope` — below the balanced point the
  slopes are strictly ordered.
* `CrystallineFractionalSlope.highSlope_not_isInt` / `lowSlope_not_isInt` — a fractional
  low slope forces *both* slopes to be non-integral.
* `CrystallineFractionalSlope.middle_slope_half_integer` — for even weight the balanced
  slope `(k−1)/2` is itself non-integral (a genuine half-integer).
* `CrystallineFractionalSlope.exists_root_iff_disc_isSquare` — the quadratic-formula
  criterion linking roots of `X² − a·X + d` to squareness of the discriminant.
* `CrystallineFractionalSlope.irreducible_iff_disc_not_isSquare` — a two–dimensional
  representation is irreducible (no invariant line) iff the discriminant is a non-square.
* `CrystallineFractionalSlope.fractional_slope_irreducibility_certificate` — the
  synthesis: even weight and a fractional sub-balanced slope yield distinct, non-integral
  Frobenius slopes summing to `k − 1`, the arithmetic certificate of irreducibility.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): fractional slope obstructs reducibility because a reducible
reduction is a sum of crystalline characters carrying *integer* slopes. Bold form: the
obstruction is purely arithmetic (non-integrality of a valuation) and is decoupled from
the residual linear algebra, which supplies an independent squareness criterion.

Experiment (Experimenter): formalised the Newton-slope pair and proved (i) their sum is
`k−1`, (ii) non-integrality propagates from the low slope to the high slope, (iii) strict
ordering below the balanced point, and (iv) the completing-the-square equivalence between
roots and square discriminants over any field of characteristic `≠ 2`.

Analysis (Analyst): the naive reduction of the Frobenius matrix is misleading — modulo `p`
the determinant `p^{k−1} ≡ 0`, so the naive characteristic polynomial `X² − ā·X` always
splits. The true semisimplified reduction is governed instead by the *slope*, an invariant
of the integral (Wach/Fontaine–Laffaille) structure rather than of the naive matrix. This
is exactly why the fractional-slope case is subtle: the obstruction lives at the level of
valuations, captured here by `highSlope_not_isInt` and `middle_slope_half_integer`.

Critique (Critic): distinctness of the two slopes needs the strict bound `2·v(a_p) < k−1`
(the low slope is the smaller Newton slope); even weight alone does not prevent the balanced
case `v(a_p) = (k−1)/2`. We keep the even-weight hypothesis because it is part of the stated
setting and it makes the balanced slope a genuine half-integer, but we record that the
strict slope bound is the load-bearing hypothesis for distinctness.

Synthesis (PI): the fractional-slope certificate bundles four independent facts (ordering,
two non-integralities, and the slope sum), giving a self-contained arithmetic witness that
the Frobenius data cannot split into integer-slope crystalline characters.
-/

namespace CrystallineFractionalSlope

/-! ## Section A — Newton slope arithmetic

The two Frobenius slopes of `X² − a_p·X + p^{k−1}` under the normalisation `v(p) = 1`,
with `s := v(a_p)` the low (smaller) slope. -/

/-- The low Frobenius slope `v(a_p)`. The weight `_k` is carried for symmetry with
`highSlope` (which depends on it), but the low slope equals `v(a_p)` regardless. -/
def lowSlope (_k : ℤ) (s : ℚ) : ℚ := s

/-- The high Frobenius slope `(k−1) − v(a_p)`. -/
def highSlope (k : ℤ) (s : ℚ) : ℚ := (k : ℚ) - 1 - s







/-! ## Section B — Quadratic linear algebra (the residual/irreducibility layer)

For any field of characteristic `≠ 2`, roots of the characteristic polynomial
`X² − a·X + d` are controlled by the discriminant `a² − 4d` via completing the square. -/

/-- The discriminant of the characteristic polynomial `X² − a·X + d`. -/
def disc {F : Type*} [Field F] (a d : F) : F := a ^ 2 - 4 * d



/-! ## Section D — Synthesis: the fractional-slope irreducibility certificate -/


/-! ## Examples (PEGB: concrete instantiation) -/

-- The two Frobenius slopes of weight `k = 6`, slope `s = 1/3` (fractional, `< 5/2`):
-- `lowSlope = 1/3`, `highSlope = 5 − 1/3 = 14/3`, summing to `5 = k − 1`.
-- A concrete irreducible reduction: over `𝔽₅` the discriminant `1² − 4·2 = -7 ≡ 3`
-- is a non-square, so `X² − X + 2` has no root — the residual representation is irreducible.
end CrystallineFractionalSlope


