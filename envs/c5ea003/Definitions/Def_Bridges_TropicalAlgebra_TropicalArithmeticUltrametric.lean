-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_TropicalArithmeticUltrametric
-- name    : Bridges_TropicalAlgebra_TropicalArithmeticUltrametric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:17.341869+00:00
-- url     : https://prove2.me/theorems/4de07b64-b9e0-4b8c-b259-ba6451596142
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_TropicalArithmeticUltrametric
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.TropicalArithmeticUltrametric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/TropicalArithmeticUltrametric.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_CategoricalTropicalUltrametric
import Definitions.Def_Bridges_PosetTheory_ArithmeticVCDimension
/-
  # Ultrametric Lipschitz Bounds Induced by Tropical Valuations
  ## on Arithmetic Height Spaces

  Bridge: connects arithmetic height theory (`Bridges/ArithmeticVCDimension.lean`)
  ↔ tropical–ultrametric reconstruction (`Bridges/CategoricalTropicalUltrametric.lean`)
  ↔ nonarchimedean metric regularity / certified robustness.

  ## Research narrative

  The catalog already contains two complementary objects that had never been
  connected by a concrete metric-regularity theorem:

  * `ArithmeticVCDim.ratArithHeight : ℚ → ℕ`, an arithmetic height on the rationals,
    together with positivity (`ratArithHeight_pos`) and symmetry
    (`ratArithHeight_neg`) lemmas.
  * `CategoricalTropicalUltrametric.valuationReconstruct`, a *quantitative functor*
    turning tropical valuation data into ultrametric seminorms, together with the
    transfer theorem
    `CategoricalTropicalUltrametric.tropical_nonexpansive_implies_ultrametric_nonexpansive`.

  This file builds the missing bridge: it turns a *valuation monotonicity* inequality
  into a *concrete metric regularity* statement (nonexpansiveness) on rational
  arithmetic data, and isolates the sharp hypotheses under which the bridge is valid.

  ## Adversarial ground truth (the sharp hypothesis)

  The naive guess — that the arithmetic height itself is an ultrametric valuation —
  is **false**.  We prove this as `ratArithHeight_not_nonarchimedean`: the height
  fails the strong (max-form) triangle inequality already on `1 + 1`.  This is the
  precise obstruction the concept warned about ("the exact metric definition may fail
  to satisfy the desired inequalities without the right normalization").  The correct
  normalization is the *p-adic valuation*, which **does** yield a genuine rational
  ultrametric; that ultrametric is what supports the Lipschitz/nonexpansive bridge.

  ## Main results

  * `ratArithHeight_not_nonarchimedean` — the height is not an ultranorm (falsifier).
  * `RatUltraValuation` + `RatUltraValuation.dist_strong_triangle` — strong (max-form)
    triangle law for the induced rational ultradistance.
  * `valuation_mono_nonexpansive` — the **bridge theorem**: an additive map whose
    valuation does not increase induces a nonexpansive map of ultrametric spaces.
  * `nonexpansive_comp` / `lipschitz_comp` — compositional closure of nonexpansive
    (resp. Lipschitz) arithmetic maps.
  * `padicRatUltra` — the p-adic instance: a genuine rational ultravaluation.
  * `pow_padicValNat_le_ratArithHeight` — height comparison linking valuation depth
    to `ratArithHeight`.
-/

open Function

noncomputable section

namespace TropicalArithmeticUltrametric

/-! ## §1. Adversarial ground truth: the arithmetic height is not an ultranorm

Bridge: pressure-tests the naive identification `height = ultrametric valuation`. -/

-- !-- Lab Notebook -- !--
-- Hypothesis: maybe `ratArithHeight` already satisfies the strong triangle law,
--   `h(q+r) ≤ max (h q) (h r)`, so it would directly be an ultranorm.
-- Result: FALSE. On `q = r = 1` we get `h(2) = 3 > 2 = max (h 1) (h 1)`.
-- Insight: the height is *sub*additive-ish but grows under addition; the genuine
--   ultrametric must come from a p-adic valuation, not the height itself.
-- Failure analysis: any bridge attempting to use `ratArithHeight` as the norm of
--   `valuationReconstruct` would violate `val_add`; the right carrier uses padicNorm.
-- !-- Lab Notebook -- !--


/-! ## §2. Rational ultravaluations and the induced ultradistance

Bridge: a rational arithmetic metric space whose distance is induced by a
(genuine) valuation, the corrected analogue of `valuationReconstruct` over ℚ. -/

/-- A **rational ultravaluation**: an absolute-value–like map `ℚ → ℚ` satisfying the
    nonarchimedean (max-form) triangle inequality.  This is the rational, real-valued
    counterpart of `CategoricalTropicalUltrametric.TropicalValuationCarrier`
    (which is ℕ-valued and multiplicative). -/
structure RatUltraValuation where
  val : ℚ → ℚ
  val_nonneg : ∀ x, 0 ≤ val x
  val_zero : val 0 = 0
  val_eq_zero : ∀ x, val x = 0 → x = 0
  val_neg : ∀ x, val (-x) = val x
  val_add_le : ∀ x y, val (x + y) ≤ max (val x) (val y)
  val_mul : ∀ x y, val (x * y) = val x * val y

namespace RatUltraValuation

variable (V : RatUltraValuation)

/-- The ultradistance induced by a rational ultravaluation: `d(x,y) = val (x - y)`.
    Bridge: rational arithmetic metric induced by valuation depth. -/
def dist (x y : ℚ) : ℚ := V.val (x - y)






end RatUltraValuation

/-! ## §3. The bridge theorem: valuation monotonicity ⇒ nonexpansiveness

Bridge: turns a valuation inequality (`val (f x) ≤ val x`) into a concrete metric
regularity statement (`dist (f x) (f y) ≤ dist x y`).  This is the rational, metric
counterpart of
`CategoricalTropicalUltrametric.tropical_nonexpansive_implies_ultrametric_nonexpansive`. -/

/-- `f` is **nonexpansive** for the ultradistance of `V`. -/
def Nonexpansive (V : RatUltraValuation) (f : ℚ → ℚ) : Prop :=
  ∀ x y, V.dist (f x) (f y) ≤ V.dist x y

/-- `f` is **`C`-Lipschitz** for the ultradistance of `V`. -/
def LipschitzWithRat (V : RatUltraValuation) (C : ℚ) (f : ℚ → ℚ) : Prop :=
  ∀ x y, V.dist (f x) (f y) ≤ C * V.dist x y

-- !-- Lab Notebook -- !--
-- Hypothesis: a valuation-monotone additive map should be nonexpansive.
-- Result: TRUE under exactly two hypotheses — additivity on differences
--   (`f (a - b) = f a - f b`) and valuation monotonicity (`val (f a) ≤ val a`).
-- Insight: additivity is the bridge that converts the *pointwise* valuation bound
--   into a *metric* bound on differences; dropping it breaks the argument.
-- Failure analysis: without additivity, `f x - f y ≠ f (x - y)`, so the valuation
--   bound on `f` cannot be transported to the distance.
-- !-- Lab Notebook -- !--



/-! ## §4. Compositional closure

Bridge: nonexpansive (resp. Lipschitz) arithmetic maps remain so under composition —
the reusable "metric-control layer" for arithmetic pipelines. -/




/-! ## §5. The p-adic instance: a genuine rational ultravaluation

Bridge: the corrected normalization — the p-adic norm — actually realizes the
abstract `RatUltraValuation`, in contrast to the failed `ratArithHeight`. -/

-- !-- Lab Notebook -- !--
-- Hypothesis: padicNorm p gives a genuine RatUltraValuation, unlike ratArithHeight.
-- Result: TRUE. All seven axioms hold from Mathlib's nonarchimedean p-adic API.
-- Insight: this is the "right normalization" the concept demanded; the bridge
--   theorem then yields nonexpansiveness for integer-scaling arithmetic maps.
-- Failure analysis: none — the only subtlety is `val_eq_zero`, via
--   `zero_of_padicNorm_eq_zero`.
-- !-- Lab Notebook -- !--

/-- The p-adic norm assembles into a genuine rational ultravaluation. -/
def padicRatUltra (p : ℕ) [Fact (Nat.Prime p)] : RatUltraValuation where
  val := padicNorm p
  val_nonneg := padicNorm.nonneg
  val_zero := padicNorm.zero
  val_eq_zero := fun _ h => padicNorm.zero_of_padicNorm_eq_zero h
  val_neg := padicNorm.neg
  val_add_le := fun _ _ => padicNorm.nonarchimedean
  val_mul := padicNorm.mul



/-! ## §6. Height comparison: valuation depth is bounded by arithmetic height

Bridge: links `Bridges/ArithmeticVCDimension.ratArithHeight` to p-adic valuation
depth, so the bounded ultradistance can be read off arithmetic data. -/

-- !-- Lab Notebook -- !--
-- Hypothesis: p-adic valuation depth of an integer is bounded by its height.
-- Result: TRUE. `p ^ v_p(n) ∣ n.natAbs ≤ n.natAbs + 1 = ratArithHeight (n:ℚ)`.
-- Insight: the largest p-power dividing n never exceeds the arithmetic height,
--   making valuation depth an arithmetically-computable quantity bounded by height.
-- Failure analysis: requires n ≠ 0 (else v_p is unbounded / height collapses).
-- !-- Lab Notebook -- !--



end TropicalArithmeticUltrametric

end


