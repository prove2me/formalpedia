-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_ArithmeticHeightUltrametric
-- name    : Bridges_TropicalAlgebra_ArithmeticHeightUltrametric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:26.746931+00:00
-- url     : https://prove2.me/theorems/d0750158-a8c7-47ba-9d0f-9052560fda1b
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_ArithmeticHeightUltrametric
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.ArithmeticHeightUltrametric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/ArithmeticHeightUltrametric.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_CategoricalTropicalUltrametric
/-
  # Arithmetic-Height-Induced Ultrametrics
  ## A nonarchimedean bridge from p-adic arithmetic height/depth data to
  ## ultrametric distances and to the catalog's tropical–ultrametric object layer.

  Bridge: Number theory (p-adic valuation / arithmetic height) ↔ Metric geometry
  (ultrametric / strong triangle inequality) ↔ the categorical tropical–ultrametric
  interface (`CategoricalTropicalUltrametric.UltraNormObj`).

  **Core principle.** A valuation-style *arithmetic depth* on rational differences
  induces a genuine ultrametric distance `d(x,y) = padicNorm p (x - y)`, and the
  *integer* divisibility-depth packages as a multiplicative ℕ-valued seminorm — a
  bona fide `TropicalValuationCarrier`, hence (via `valuationReconstruct`) an
  `UltraNormObj`.  A representation/rigidity result explains *why* the carrier must
  live on the integers rather than the field: on a field every multiplicative
  ℕ-valued norm is trivial on nonzero elements.

  -- !-- Lab Notebook -- !--
  Hypothesis: arithmetic height/depth data on ℚ yields a strong (max-type) triangle
    inequality, and the discrete divisibility depth on ℤ is a multiplicative
    ultrametric ℕ-seminorm that instantiates the catalog `UltraNormObj` interface.
  Result: proved identity / symmetry / strong-triangle for `hDist p` on ℚ, built
    `arithDepthCarrier p : TropicalValuationCarrier`, reconstructed it into an
    ultrametric object via the catalog's `valuationReconstruct`, and proved the
    field-rigidity obstruction forcing the carrier to be ℤ rather than ℚ.
  Insight: the catalog `UltraNormObj` norm axioms (ℕ-valued, multiplicative,
    `norm_add ≤ max`) are satisfiable nontrivially only on a non-field: on ℚ
    multiplicativity + `norm 1 = 1` collapses the norm to the nonzero-indicator
    (`field_norm_rigid`).  Quantitative depth therefore lives in the *real-valued*
    `padicNorm` distance, while the *categorical object* lives over ℤ via the
    prime-divisibility (residue-field) indicator `val n = if p ∣ n then 0 else 1`,
    which is exactly the indicator of nonvanishing in `ZMod p` (`valInt_eq_one_iff_residue`).
  Failure analysis: a first attempt put the divisibility indicator on all of ℚ; it
    fails multiplicativity (v_p = 1 times v_p = -1 gives a unit), so the carrier was
    restricted to ℤ, where p-adic valuations are nonnegative and Euclid's lemma
    makes the indicator multiplicative.
  -- !-- Lab Notebook -- !--
-/

open scoped Classical
open CategoricalTropicalUltrametric

namespace ArithmeticHeightUltrametric

noncomputable section

/-! ## §1. The arithmetic-height depth distance on ℚ

The quantitative heart: `hDist p x y := padicNorm p (x - y)` is a real (ℚ-valued)
ultrametric whose value is `p ^ (-(arithmetic depth of x - y))`. -/

/-- The arithmetic-height-induced distance: the p-adic norm of the difference,
    equal to `p ^ (-(padicValRat p (x - y)))`. -/
def hDist (p : ℕ) (x y : ℚ) : ℚ := padicNorm p (x - y)

variable {p : ℕ} [Fact p.Prime]

-- !-- The p-adic norm is always nonnegative. -- !--

-- !-- `x - x = 0` and `padicNorm p 0 = 0`. -- !--

-- !-- `padicNorm` vanishes iff its argument is `0`, and `x - y = 0 ↔ x = y`. -- !--

-- !-- `x - y = -(y - x)` and `padicNorm` is invariant under negation. -- !--

-- !-- Write `x - z = (x - y) + (y - z)` and apply the nonarchimedean inequality
-- for `padicNorm`. -- !--

-- !-- Both distances are nonnegative, so `max a b ≤ a + b`. -- !--

/-! ## §2. The discrete arithmetic-divisibility depth on ℤ

The *categorical* carrier.  On the integers the p-adic valuation is nonnegative, so
the prime-divisibility indicator `valInt n = if (p:ℤ) ∣ n then 0 else 1` is a
multiplicative ℕ-valued ultrametric seminorm — a `TropicalValuationCarrier`. -/

/-- Arithmetic divisibility depth on ℤ: `0` exactly on the multiples of `p`
    (the "deep" integers), `1` on the p-adic units. -/
def valInt (p : ℕ) (n : ℤ) : ℕ := if (p : ℤ) ∣ n then 0 else 1

-- !-- `(p:ℤ) ∣ 0` holds, so the indicator is `0`. -- !--
omit [Fact p.Prime] in
theorem valInt_zero : valInt p 0 = 0 := if_pos (dvd_zero _)

-- !-- `(p:ℤ) ∣ -n ↔ (p:ℤ) ∣ n`. -- !--
omit [Fact p.Prime] in
theorem valInt_neg (n : ℤ) : valInt p (-n) = valInt p n := by
  simp [valInt]

-- !-- Euclid's lemma: a prime divides a product iff it divides a factor, so the
-- {0,1}-indicator is multiplicative. -- !--
theorem valInt_mul (m n : ℤ) : valInt p (m * n) = valInt p m * valInt p n := by
  unfold valInt
  split_ifs <;> simp_all [← ZMod.intCast_zmod_eq_zero_iff_dvd]

-- !-- If `p ∤ (m+n)` then `p` divides at most one of `m, n` (else it divides the
-- sum), so the indicator of the sum is `≤ max`. -- !--
omit [Fact p.Prime] in
theorem valInt_add (m n : ℤ) : valInt p (m + n) ≤ max (valInt p m) (valInt p n) := by
  by_cases hm : (p : ℤ) ∣ m <;> by_cases hn : (p : ℤ) ∣ n <;> simp [*, valInt]
  · exact dvd_add hm hn
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num

-- !-- Unfolding the indicator, `valInt p n = 1 ↔ ¬ (p:ℤ) ∣ n`, and
-- `(n : ZMod p) = 0 ↔ (p:ℤ) ∣ n`. -- !--

/-! ## §3. Bridge constructor into the catalog object layer -/

/-- **Bridge constructor.** Package the integer arithmetic-divisibility depth as a
    `TropicalValuationCarrier`, the source object for the catalog's
    `valuationReconstruct` functor into `UltraNormObj`. -/
def arithDepthCarrier (p : ℕ) [Fact p.Prime] : TropicalValuationCarrier where
  K := ℤ
  add_op := (· + ·)
  neg_op := Neg.neg
  zero_val := 0
  sub_op := (· - ·)
  sub_def := fun x y => by ring
  mul_op := (· * ·)
  one_val := 1
  val := valInt p
  val_zero := valInt_zero
  val_neg := valInt_neg
  val_mul := valInt_mul
  val_add := valInt_add

-- !-- After unfolding `valuationReconstruct` and `arithDepthCarrier`, the norm is
-- `valInt p` and the goal is exactly `valInt_add`. -- !--

/-! ## §4. Field rigidity: why the carrier must be ℤ, not ℚ

A representation/rigidity obstruction.  On a field, multiplicativity together with
`norm 1 = 1` forces the ℕ-valued norm to be the nonzero-indicator (`= 1` on every
nonzero element): all quantitative arithmetic depth is invisible to an ℕ-valued
*multiplicative* norm over a field.  This is precisely why §1's genuine depth must be
real-valued, while the categorical carrier of §2–§3 lives over ℤ. -/

-- !-- In ℕ the only unit is `1`; in a field `x * x⁻¹ = 1`, so `f x * f x⁻¹ = 1` in
-- ℕ forces `f x = 1`. -- !--

end

end ArithmeticHeightUltrametric


