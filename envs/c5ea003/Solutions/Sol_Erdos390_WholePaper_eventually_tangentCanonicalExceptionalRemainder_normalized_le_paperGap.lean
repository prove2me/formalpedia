-- Prove2me | solution 1 for Erdos390.WholePaper.eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:07:13.321133+00:00
-- url     : https://prove2.me/submissions/2c584826-6206-4ff3-a4ec-edd4396b310d

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_008

/- Source module: Erdos390.Full.Scale -/
section


/-!
# Exact scale identities

This file records the elementary identities behind the fixed choice
`y = n^(2/9)` used throughout the marked and smooth bridge.  Keeping them as
equalities avoids repeatedly treating `U = 9/2` and the four-mark cofactor
margin as informal arithmetic simplifications.
-/

open Filter Topology

namespace Erdos390.Full.Scale

open ArithmeticModel















/-- Four marked prime factors use precisely the exponent `8/9`. -/
theorem y_pow_four (n : ℕ) :
    y n ^ 4 = (n : ℝ) ^ (8 / 9 : ℝ) := by
  calc
    y n ^ 4 = ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 4 := rfl
    _ = (n : ℝ) ^ ((2 / 9 : ℝ) * (4 : ℕ)) :=
      (Real.rpow_mul_natCast (Nat.cast_nonneg n) (2 / 9 : ℝ) 4).symm
    _ = (n : ℝ) ^ (8 / 9 : ℝ) := by norm_num













end Erdos390.Full.Scale

end

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/



















































/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/






















































/-- The integral cutoff `floor(n^(2/9))` retains enough logarithmic size
for the complete four-mark coordinate range. -/
theorem eventually_one_fifth_L_le_log_yNat :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually
      (Filter.eventually_ge_atTop (45 * Real.log 2))] with n hn hyn hLn
  have hypos : 0 < y n := y_pos hn
  have hyNatLower : y n / 2 ≤ (yNat n : ℝ) := by
    have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogLower : Real.log (y n / 2) ≤ Real.log (yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    (1 / 5 : ℝ) * L n ≤ Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      linarith
    _ ≤ Real.log (yNat n : ℝ) := hlogLower






end Erdos390.Full.FriableAsymptotic

end

/- Source module: Erdos390.WholePaper.TangentExceptionalSelbergReduction -/
section


/-!
# Exceptional tangent rows: the verified Selberg reduction

Section 9 of the paper bounds the common multipliers with
`2n / R_y(a) < X0` by writing

`a = R_y(a) * b`

and applying an interval Selberg sieve separately for each smooth factor
`b`.  This file formalizes all of that finite reduction and connects it to
the literal common-list deletion ledger.

The analytic availability boundary is important here.  The Mathlib module
`Mathlib.NumberTheory.SelbergSieve` currently supplies the abstract theorem

`BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`,

but it does not yet construct the paper's Lambda-squared coefficients,
diagonalize their main term, or prove the required lower bound for the
sieve-density sum.  In particular, the specialized estimate

`H / log y + y^4 / (log y)^2`

cannot honestly be deduced from the available library theorem alone.
Accordingly, this file does not assume that estimate or its desired
cardinality consequence.  It proves instead the strongest available
statement:

* the interval sieve is a literal `BoundingSieve` with `nu(d)=1/d`;
* its remainder has the sharp elementary bound `|R_d| < 1`;
* every exceptional common multiplier injects into the disjoint union of
  the corresponding rough reduced-residue intervals;
* any verified upper-Moebius coefficients therefore give an explicit real
  majorant, and its natural ceiling substitutes for the exceptional term in
  both the generic and the sharp bank deletion ledgers.

Thus, at this reduction layer, the analytic obligation is isolated exactly
as the choice and estimation of concrete upper-Moebius coefficients, rather
than hidden inside an assumed exceptional-cardinality bound.  The downstream
Lambda-square modules discharge that obligation.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## A literal interval `BoundingSieve` -/

















/-! ## The exact endpoint remainder, with constant one -/













/-! ## Exact factorization of exceptional common multipliers -/























/-! ## Substitution of the verified abstract sieve bound -/

















/-! ## The `delta_* < 1/18`, `y^4=n^(8/9)` remainder arithmetic -/



/-- The integral cutoff can only decrease that fourth power. -/
theorem tangentExceptional_yNat_pow_four_le (n : ℕ) :
    (yNat n : ℝ) ^ 4 ≤ (n : ℝ) ^ (8 / 9 : ℝ) := by
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  calc
    (yNat n : ℝ) ^ 4 ≤ y n ^ 4 := by gcongr
    _ = (n : ℝ) ^ (8 / 9 : ℝ) := y_pow_four n

/-- The numerical threshold in Section 9 leaves the explicit power saving
`delta_* + 8/9 - 1 < -1/18`. -/
theorem tangentExceptional_deltaStar_remainder_exponent
    {deltaStar : ℝ} (hdeltaStar : deltaStar < 1 / 18) :
    deltaStar + 8 / 9 - 1 < -(1 / 18 : ℝ) := by
  linarith

/-- In particular the power occurring before the harmless logarithmic
denominator tends to zero. -/
theorem tangentExceptional_remainderPower_tendsto_zero
    {deltaStar : ℝ} (hdeltaStar : deltaStar < 1 / 18) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (deltaStar + 8 / 9 - 1))
      atTop (nhds 0) := by
  have hexponent : deltaStar + 8 / 9 - 1 < 0 :=
    (tangentExceptional_deltaStar_remainder_exponent hdeltaStar).trans
      (by norm_num)
  have h :=
    (tendsto_rpow_neg_atTop (neg_pos.mpr hexponent)).comp
      tendsto_natCast_atTop_atTop
  simpa only [neg_neg] using h

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentExceptionalCanonicalBounds -/
section


/-!
# Analytic bounds for the canonical exceptional-row Lambda-squared sieve

This file closes the two analytic inputs left open by
`TangentExceptionalLambdaSquareSieve`.  The constants are deliberately
coarse and fixed.  The PNT error constant and cutoff inherited from
`PrimeBandQuadrature` are named noncomputable choices, rather than numerical
values.  The proof has three ingredients.

* The verified interval Mertens theorem in `Full.PrimeBandQuadrature`
  gives a lower bound for the Euler product
  `prod_{p <= y} (1 + 1/(p-1))`.
* A logarithmic first-moment argument shows that truncating the squarefree
  divisor sum at `y^2` retains at least one tenth of that Euler product.
* A nonnegative Dirichlet-convolution majorant bounds the canonical
  Lambda `l1` norm by `exp 4 * y^2 / G`.

Thus the only constants in the final result are a named finite Mertens
loss, `10 * exp(loss)` for the main term, and an additional factor `exp 4`
for the Lambda norm.  No prime-product or coefficient estimate is assumed.
-/

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.sigma ArithmeticFunction.zeta
open Filter Set Topology

namespace Erdos390.WholePaper

noncomputable section

open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

/-! ## Multiplicative functions used in the Euler-product ledgers -/

































/-! ## Full density and logarithmic first moment -/









/-! A powerset moment inequality.  It is the finite probabilistic estimate
behind the truncation: the first moment of independent nonnegative local
weights is at most their partition function times `sum b_p a_p`. -/





/-! ## Prime sums at the rough-head modulus -/











/-! ## Mertens lower bound for the full Euler product -/



















/-! ## Retaining a fixed fraction below level `y^2` -/





/-! ## A universal `exp 4` coefficient-mean bound -/















/-! ## The canonical Lambda norm -/







/-! ## Fixed eventual constants and the closed interval theorem -/





theorem tangentSelbergCanonicalMainConstant_pos :
    0 < tangentSelbergCanonicalMainConstant := by
  unfold tangentSelbergCanonicalMainConstant
  positivity

theorem tangentSelbergCanonicalLambdaConstant_pos :
    0 < tangentSelbergCanonicalLambdaConstant := by
  unfold tangentSelbergCanonicalLambdaConstant
  exact mul_pos (Real.exp_pos 4) tangentSelbergCanonicalMainConstant_pos











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCanonicalCleanListLower -/
section


/-!
# Canonical eventual lower bounds for tangent clean lists

This file composes the three previously separate parts of the tangent-list
cardinality argument.

* `FixedModulusReducedResidueCount` gives a lower bound for the literal
  candidate interval

  `(n / v, tangentBroadUpper n K h / u]`

  with modulus `roughHeadModulus W`.  The endpoint loss is the literal
  modulus, not an absorbed constant.
* `TangentExceptionalCanonicalBounds` is applied to every rough-label
  interval indexed by a smooth factor `b`.  The resulting exceptional upper
  bound is assumption-free eventually in `y` and then in `yNat n`.
* `TangentCleanListCardinalityBridge` subtracts that exceptional bound and
  the declared deterministic deletion budget from the candidate lower bound.

The accumulated canonical remainder is displayed as

`(X0 / u) * C_lambda^2 * y^4 / log(y)^2`.

After normalization by the candidate scale `n/u`, it is bounded by the
explicit quantity

`C_lambda^2 * (X0 * y^4 / n) / log(y)^2`.

Thus the power-saving input is genuinely `X0*y^4/n`; the logarithmic square
does not conceal the required scale.  The final paper wrappers leave only an
explicit comparison between the candidate floor and the effective lower-card
ceiling plus the exceptional and deterministic losses.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal candidate lower bound -/







/-! ## Assumption-free canonical exceptional upper bound -/













/-- The accumulated remainder really has relative scale `X0*y^4/n` after
normalization by `n/u`.  No logarithmic or floor loss is hidden here. -/
theorem tangentCanonicalExceptionalRemainder_normalized_le
    {n X0 y u : ℕ} (hn : 0 < n) (hu : 0 < u) :
    (u : ℝ) / n * tangentCanonicalExceptionalRemainder X0 y u ≤
      tangentSelbergCanonicalLambdaConstant ^ 2 *
        ((X0 : ℝ) * (y : ℝ) ^ 4 / n) /
          Real.log (y : ℝ) ^ 2 := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have huReal : 0 < (u : ℝ) := by exact_mod_cast hu
  have hfloorDiv :
      ((X0 / u : ℕ) : ℝ) ≤ (X0 : ℝ) / u :=
    Nat.cast_div_le
  let endpointTerm :=
    tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
      Real.log (y : ℝ) ^ 2
  have hendpointNonneg : 0 ≤ endpointTerm := by
    dsimp only [endpointTerm]
    positivity
  have hcancel : ∀ z : ℝ,
      (u : ℝ) / n * (((X0 : ℝ) / u) * z) =
        (X0 : ℝ) / n * z := by
    intro z
    field_simp [hnReal.ne', huReal.ne']
  calc
    (u : ℝ) / n * tangentCanonicalExceptionalRemainder X0 y u =
        (u : ℝ) / n * (((X0 / u : ℕ) : ℝ) * endpointTerm) := by
      rfl
    _ ≤ (u : ℝ) / n * (((X0 : ℝ) / u) * endpointTerm) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right hfloorDiv hendpointNonneg
      · exact div_nonneg huReal.le hnReal.le
    _ = (X0 : ℝ) / n * endpointTerm := hcancel endpointTerm
    _ = tangentSelbergCanonicalLambdaConstant ^ 2 *
        ((X0 : ℝ) * (y : ℝ) ^ 4 / n) /
          Real.log (y : ℝ) ^ 2 := by
      dsimp only [endpointTerm]
      ring

/-! ## Effective lower cards and eventual bridge theorems -/











namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentPaperCleanListAbsorption -/
section


/-!
# Closing the paper-scale tangent clean-list inequality

This file fixes the moving parameters used in Section 9 of the paper:

* `h = upperTailLength c n = ceil(c n / log n)`;
* `Phead = roughHeadModulus W`;
* `X0 = ceil(n ^ deltaStar)`;
* `y = yNat n = floor(n ^ (2/9))`;
* `W < v <= u <= y` and `u / v <= r0 < 3/2`.

For fixed `W`, `K`, `c`, `r0`, and `deltaStar`, the head-density gap is

`roughHeadDensity W * (2 - r0)`.

We reserve one sixteenth of that gap as the effective list density.  A
slightly conservative explicit version of the paper's one-time cutoff makes
the canonical Selberg main term at most one quarter of the gap.  The
Lambda-squared endpoint remainder and the sharp bank deletion census are
then `o(n/u)`, uniformly for `u <= yNat n`.  The fixed-modulus endpoint loss,
the natural floors and ceilings, and `K*h` are absorbed at the same scale.

Consequently the final candidate-floor-versus-loss inequality is proved
eventually; it is not retained as a premise of the paper-facing wrapper.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Literal Section 9 parameters -/













/-- The safe ceiling changes the paper's real cutoff by strictly less than
one. -/
theorem tangentPaperExceptionalCutoff_cast_lt_add_one
    (deltaStar : ℝ) (n : ℕ) :
    (tangentPaperExceptionalCutoff deltaStar n : ℝ) <
      (n : ℝ) ^ deltaStar + 1 := by
  unfold tangentPaperExceptionalCutoff
  exact Nat.ceil_lt_add_one
    (Real.rpow_nonneg (Nat.cast_nonneg n) deltaStar)







/-! ## The harmonic main term -/





/-! ## Moving-scale negligibility -/





/-! ## Eventual exceptional-loss absorption -/



/-- The literal `X0*yNat^4/n` Lambda-squared remainder is uniformly
negligible on the `n/u` scale when `deltaStar<1/18`. -/
theorem eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap
    {W : ℕ} {r0 deltaStar : ℝ}
    (hdeltaNonneg : 0 ≤ deltaStar)
    (hdelta : deltaStar < 1 / 18)
    (hgap : 0 < tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℕ, 0 < u →
      (u : ℝ) / (n : ℝ) *
          tangentCanonicalExceptionalRemainder
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u ≤
        tangentPaperHeadGap W r0 / 16 := by
  have hlambdaSq : 0 < tangentSelbergCanonicalLambdaConstant ^ 2 :=
    sq_pos_of_pos tangentSelbergCanonicalLambdaConstant_pos
  have hepsilon : 0 <
      tangentPaperHeadGap W r0 /
        (32 * tangentSelbergCanonicalLambdaConstant ^ 2) := by positivity
  have hpowerSmall :=
    (tangentExceptional_remainderPower_tendsto_zero hdelta).eventually
      (eventually_lt_nhds hepsilon)
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLfive := hLTop.eventually (eventually_ge_atTop (5 : ℝ))
  filter_upwards
    [eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      hpowerSmall, hLfive] with n hn hlogY hpower hLnFive
  intro u hu
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hL : 0 < L n := L_pos (by omega)
  have hlogYOne : 1 ≤ Real.log (yNat n : ℝ) := by
    nlinarith [hlogY]
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega))
      hdeltaNonneg
  have hcut :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        2 * (n : ℝ) ^ deltaStar := by
    calc
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
          (n : ℝ) ^ deltaStar + 1 :=
        (tangentPaperExceptionalCutoff_cast_lt_add_one
          deltaStar n).le
      _ ≤ 2 * (n : ℝ) ^ deltaStar := by linarith
  have hyFour := tangentExceptional_yNat_pow_four_le n
  have hpowerIdentity :
      (n : ℝ) ^ deltaStar * (n : ℝ) ^ (8 / 9 : ℝ) / (n : ℝ) =
        (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by
    rw [← Real.rpow_add hnR]
    calc
      (n : ℝ) ^ (deltaStar + 8 / 9) / (n : ℝ) =
          (n : ℝ) ^ (deltaStar + 8 / 9) /
            (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (deltaStar + 8 / 9 - 1) :=
        (Real.rpow_sub hnR (deltaStar + 8 / 9) 1).symm
  have hproduct :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 / (n : ℝ) ≤
        2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by
    calc
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 / (n : ℝ) ≤
        (2 * (n : ℝ) ^ deltaStar * (n : ℝ) ^ (8 / 9 : ℝ)) /
          (n : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul hcut hyFour (by positivity) (by positivity)) hnR.le
      _ = 2 *
          ((n : ℝ) ^ deltaStar * (n : ℝ) ^ (8 / 9 : ℝ) /
            (n : ℝ)) := by ring
      _ = 2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by
        rw [hpowerIdentity]
  have hdenom : 1 ≤ Real.log (yNat n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (yNat n : ℝ) - 1)]
  have hnormalized := tangentCanonicalExceptionalRemainder_normalized_le
    (X0 := tangentPaperExceptionalCutoff deltaStar n) (y := yNat n)
      hnPos hu
  calc
    (u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalRemainder
          (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u ≤
      tangentSelbergCanonicalLambdaConstant ^ 2 *
        ((tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 / (n : ℝ)) /
            Real.log (yNat n : ℝ) ^ 2 := hnormalized
    _ ≤ tangentSelbergCanonicalLambdaConstant ^ 2 *
        (2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1)) /
          Real.log (yNat n : ℝ) ^ 2 := by
      gcongr
    _ ≤ tangentSelbergCanonicalLambdaConstant ^ 2 *
        (2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1)) := by
      exact div_le_self (mul_nonneg (sq_nonneg _) (by positivity)) hdenom
    _ ≤ tangentSelbergCanonicalLambdaConstant ^ 2 *
        (2 * (tangentPaperHeadGap W r0 /
          (32 * tangentSelbergCanonicalLambdaConstant ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpower.le (by norm_num)) (sq_nonneg _)
    _ = tangentPaperHeadGap W r0 / 16 := by
      field_simp [tangentSelbergCanonicalLambdaConstant_pos.ne']
      norm_num

/-! ## The fixed-head candidate at the paper endpoints -/





/-! ## The literal candidate floor absorbs every canonical loss -/



/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {W : Nat} {r0 deltaStar : Real},
  LE.le.{0} (0 : Real) deltaStar →
    LT.lt.{0} deltaStar (1 / 18 : Real) →
      LT.lt.{0} (0 : Real) (Erdos390.WholePaper.tangentPaperHeadGap W r0) →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∀ (u : Nat),
            LT.lt.{0} (0 : Nat) u →
              LE.le.{0}
                (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} ↑u ↑n)
                  (Erdos390.WholePaper.tangentCanonicalExceptionalRemainder
                    (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n)
                    (Erdos390.Full.ArithmeticModel.yNat n) u))
                (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentPaperHeadGap W r0) (16 : Real)) := by
  exact @Erdos390.WholePaper.eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap
