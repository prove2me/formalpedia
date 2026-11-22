-- Prove2me | solution 1 for Erdos390.WholePaper.eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T16:07:03.005564+00:00
-- url     : https://prove2.me/submissions/10cbbc40-9598-45e1-8bbd-ddcdec5eb30b

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008

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











/-- The natural ceiling dominates the literal real exceptional cutoff. -/
theorem tangentPaperExceptionalCutoff_cast_ge
    (deltaStar : ℝ) (n : ℕ) :
    (n : ℝ) ^ deltaStar ≤
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) := by
  unfold tangentPaperExceptionalCutoff
  exact Nat.le_ceil _

/-- The safe ceiling changes the paper's real cutoff by strictly less than
one. -/
theorem tangentPaperExceptionalCutoff_cast_lt_add_one
    (deltaStar : ℝ) (n : ℕ) :
    (tangentPaperExceptionalCutoff deltaStar n : ℝ) <
      (n : ℝ) ^ deltaStar + 1 := by
  unfold tangentPaperExceptionalCutoff
  exact Nat.ceil_lt_add_one
    (Real.rpow_nonneg (Nat.cast_nonneg n) deltaStar)



/-- A nonnegative exponent and positive base make the natural exceptional
cutoff strictly positive. -/
theorem tangentPaperExceptionalCutoff_pos
    {deltaStar : ℝ} (hdelta : 0 ≤ deltaStar)
    {n : ℕ} (hn : 1 ≤ n) :
    0 < tangentPaperExceptionalCutoff deltaStar n := by
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast hn) hdelta
  have hceil := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  have hcast : (1 : ℝ) ≤
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) := hone.trans hceil
  have hnat : 1 ≤ tangentPaperExceptionalCutoff deltaStar n := by
    exact_mod_cast hcast
  omega

/-- The ceiling cutoff has logarithm at most the paper exponent term plus
the single `log 2` ceiling loss. -/
theorem tangentPaperExceptionalCutoff_log_le
    {deltaStar : ℝ} (hdelta : 0 ≤ deltaStar)
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
      deltaStar * L n + Real.log 2 := by
  have hcutPos : (0 : ℝ) < tangentPaperExceptionalCutoff deltaStar n := by
    exact_mod_cast tangentPaperExceptionalCutoff_pos hdelta hn
  have hnPos : (0 : ℝ) < n := by positivity
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast hn) hdelta
  have hcutUpper :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        2 * (n : ℝ) ^ deltaStar := by
    calc
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
          (n : ℝ) ^ deltaStar + 1 :=
        (tangentPaperExceptionalCutoff_cast_lt_add_one
          deltaStar n).le
      _ ≤ 2 * (n : ℝ) ^ deltaStar := by linarith
  calc
    Real.log (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        Real.log (2 * (n : ℝ) ^ deltaStar) :=
      Real.log_le_log hcutPos hcutUpper
    _ = deltaStar * L n + Real.log 2 := by
      rw [Real.log_mul (by norm_num)
        (Real.rpow_pos_of_pos hnPos deltaStar).ne',
        Real.log_rpow hnPos]
      unfold L
      ring

/-! ## The harmonic main term -/

/-- The sum of all literal rough-label interval lengths is bounded by the
full harmonic sum up to `X0`.  This is the Mertens/harmonic main-term layer
of the exceptional deletion, before division by `log y`. -/
theorem tangentCanonicalExceptionalLengthSum_le_harmonic
    {n K h X0 u v : ℕ} (hu : 0 < u) :
    tangentCanonicalExceptionalLengthSum n K h X0 u v ≤
      (2 * (n : ℝ) / (u : ℝ)) *
        (1 + Real.log (X0 : ℝ)) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hbroad : tangentBroadUpper n K h ≤ 2 * n := by
    unfold tangentBroadUpper
    exact Nat.sub_le _ _
  have hterm : ∀ b ∈ tangentExceptionalSmoothIndices X0 u,
      (((tangentBroadUpper n K h / (u * b) -
          n / (v * b) : ℕ) : ℝ)) ≤
        (2 * (n : ℝ) / (u : ℝ)) * (1 / (b : ℝ)) := by
    intro b hb
    have hbData := Finset.mem_filter.mp hb
    have hbOne : 1 ≤ b := (Finset.mem_Icc.mp hbData.1).1
    have hbPos : 0 < b := Nat.zero_lt_of_lt hbOne
    have hbR : (0 : ℝ) < b := by exact_mod_cast hbPos
    calc
      (((tangentBroadUpper n K h / (u * b) -
          n / (v * b) : ℕ) : ℝ)) ≤
          ((tangentBroadUpper n K h / (u * b) : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le
          (tangentBroadUpper n K h / (u * b)) (n / (v * b))
      _ ≤ (tangentBroadUpper n K h : ℝ) / ((u * b : ℕ) : ℝ) :=
        Nat.cast_div_le
      _ ≤ ((2 * n : ℕ) : ℝ) / ((u * b : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hbroad)
          (Nat.cast_nonneg _)
      _ = (2 * (n : ℝ) / (u : ℝ)) * (1 / (b : ℝ)) := by
        push_cast
        field_simp [huR.ne', hbR.ne']
  have hsubset : tangentExceptionalSmoothIndices X0 u ⊆ Finset.Ioc 0 X0 := by
    intro b hb
    have hbData := Finset.mem_filter.mp hb
    have hbIcc := Finset.mem_Icc.mp hbData.1
    exact Finset.mem_Ioc.mpr ⟨by omega, hbIcc.2⟩
  have hreciprocal :
      (∑ b ∈ tangentExceptionalSmoothIndices X0 u, 1 / (b : ℝ)) ≤
        ∑ b ∈ Finset.Ioc 0 X0, 1 / (b : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro b hb _hnot
    have hbPos : 0 < b := (Finset.mem_Ioc.mp hb).1
    positivity
  have hharmonic :
      (∑ b ∈ tangentExceptionalSmoothIndices X0 u, 1 / (b : ℝ)) ≤
        1 + Real.log (X0 : ℝ) :=
    hreciprocal.trans
      (Erdos390.Full.FriableAsymptotic.harmonic_Ioc_le
        (z := 0) (y := X0))
  unfold tangentCanonicalExceptionalLengthSum
  calc
    (∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (((tangentBroadUpper n K h / (u * b) -
          n / (v * b) : ℕ) : ℝ))) ≤
      ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (2 * (n : ℝ) / (u : ℝ)) * (1 / (b : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = (2 * (n : ℝ) / (u : ℝ)) *
        ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
          1 / (b : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * (n : ℝ) / (u : ℝ)) *
        (1 + Real.log (X0 : ℝ)) :=
      mul_le_mul_of_nonneg_left hharmonic (by positivity)

/-- Normalizing the harmonic length sum by `n / u` removes the endpoint
scale exactly. -/
theorem tangentCanonicalExceptionalLengthSum_normalized_le_harmonic
    {n K h X0 u v : ℕ} (hn : 0 < n) (hu : 0 < u) :
    (u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalLengthSum n K h X0 u v ≤
      2 * (1 + Real.log (X0 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  calc
    (u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalLengthSum n K h X0 u v ≤
      (u : ℝ) / (n : ℝ) *
        ((2 * (n : ℝ) / (u : ℝ)) *
          (1 + Real.log (X0 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (tangentCanonicalExceptionalLengthSum_le_harmonic hu)
        (div_nonneg huR.le hnR.le)
    _ = 2 * (1 + Real.log (X0 : ℝ)) := by
      field_simp [hnR.ne', huR.ne']

/-! ## Moving-scale negligibility -/





/-! ## Eventual exceptional-loss absorption -/

/-- The canonical Mertens/Selberg main term is a fixed small fraction of the
head gap under the one-time `deltaStar` choice.  The constant `80` is a
conservative closed replacement for the paper's implicit sieve constant. -/
theorem eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap
    {W : ℕ} {r0 deltaStar : ℝ}
    (hdelta : 0 < deltaStar)
    (hsmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop, ∀ K h u v : ℕ, 0 < u →
      (u : ℝ) / (n : ℝ) *
          (tangentCanonicalExceptionalLengthSum n K h
              (tangentPaperExceptionalCutoff deltaStar n) u v *
            (tangentSelbergCanonicalMainConstant /
              Real.log (yNat n : ℝ))) ≤
        tangentPaperHeadGap W r0 / 4 := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdeltaL := hLTop.eventually
    (eventually_ge_atTop ((1 + Real.log 2) / deltaStar))
  filter_upwards
    [eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      hdeltaL] with n hn hlogY hLn
  intro K h u v hu
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hL : 0 < L n := L_pos (by omega)
  have hdeltaLDominates :
      1 + Real.log 2 ≤ deltaStar * L n := by
    have h := (div_le_iff₀ hdelta).mp hLn
    simpa only [mul_comm] using h
  have hlogYPos : 0 < Real.log (yNat n : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL).trans_le hlogY
  have hcutLog := tangentPaperExceptionalCutoff_log_le hdelta.le
    (show 1 ≤ n by omega)
  have hlength :=
    tangentCanonicalExceptionalLengthSum_normalized_le_harmonic
      (K := K) (h := h) (X0 := tangentPaperExceptionalCutoff deltaStar n)
      (v := v) hnPos hu
  have hlength' :
      (u : ℝ) / (n : ℝ) *
          tangentCanonicalExceptionalLengthSum n K h
            (tangentPaperExceptionalCutoff deltaStar n) u v ≤
        4 * deltaStar * L n := by
    calc
      _ ≤ 2 *
          (1 + Real.log
            (tangentPaperExceptionalCutoff deltaStar n : ℝ)) := hlength
      _ ≤ 2 * (1 + (deltaStar * L n + Real.log 2)) := by
        gcongr
      _ ≤ 4 * deltaStar * L n := by
        nlinarith
  have hinv : 1 / Real.log (yNat n : ℝ) ≤
      1 / ((1 / 5 : ℝ) * L n) :=
    one_div_le_one_div_of_le
      (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL) hlogY
  have hcoefficient :
      tangentSelbergCanonicalMainConstant / Real.log (yNat n : ℝ) ≤
        5 * tangentSelbergCanonicalMainConstant / L n := by
    calc
      tangentSelbergCanonicalMainConstant / Real.log (yNat n : ℝ) =
          tangentSelbergCanonicalMainConstant *
            (1 / Real.log (yNat n : ℝ)) := by ring
      _ ≤ tangentSelbergCanonicalMainConstant *
          (1 / ((1 / 5 : ℝ) * L n)) :=
        mul_le_mul_of_nonneg_left hinv
          tangentSelbergCanonicalMainConstant_pos.le
      _ = 5 * tangentSelbergCanonicalMainConstant / L n := by
        field_simp [hL.ne']
  have hlengthNonneg : 0 ≤
      (u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalLengthSum n K h
          (tangentPaperExceptionalCutoff deltaStar n) u v := by
    apply mul_nonneg (div_nonneg huR.le hnR.le)
    unfold tangentCanonicalExceptionalLengthSum
    apply Finset.sum_nonneg
    intro b _hb
    exact Nat.cast_nonneg _
  calc
    (u : ℝ) / (n : ℝ) *
        (tangentCanonicalExceptionalLengthSum n K h
            (tangentPaperExceptionalCutoff deltaStar n) u v *
          (tangentSelbergCanonicalMainConstant /
            Real.log (yNat n : ℝ))) =
      ((u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalLengthSum n K h
          (tangentPaperExceptionalCutoff deltaStar n) u v) *
        (tangentSelbergCanonicalMainConstant /
          Real.log (yNat n : ℝ)) := by ring
    _ ≤ (4 * deltaStar * L n) *
        (5 * tangentSelbergCanonicalMainConstant / L n) :=
      mul_le_mul hlength' hcoefficient
        (div_nonneg tangentSelbergCanonicalMainConstant_pos.le hlogYPos.le)
        (hlengthNonneg.trans hlength')
    _ = 20 * tangentSelbergCanonicalMainConstant * deltaStar := by
      field_simp [hL.ne']
      ring
    _ ≤ tangentPaperHeadGap W r0 / 4 := by linarith



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
  LT.lt.{0} (0 : Real) deltaStar →
    LT.lt.{0}
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (80 : Real) Erdos390.WholePaper.tangentSelbergCanonicalMainConstant)
          deltaStar)
        (Erdos390.WholePaper.tangentPaperHeadGap W r0) →
      ∀ᶠ (n : Nat) in Filter.atTop.{0},
        ∀ (K h u v : Nat),
          LT.lt.{0} (0 : Nat) u →
            LE.le.{0}
              (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} ↑u ↑n)
                (HMul.hMul.{0, 0, 0}
                  (Erdos390.WholePaper.tangentCanonicalExceptionalLengthSum n K h
                    (Erdos390.WholePaper.tangentPaperExceptionalCutoff deltaStar n) u v)
                  (HDiv.hDiv.{0, 0, 0} Erdos390.WholePaper.tangentSelbergCanonicalMainConstant
                    (Real.log ↑(Erdos390.Full.ArithmeticModel.yNat n)))))
              (HDiv.hDiv.{0, 0, 0} (Erdos390.WholePaper.tangentPaperHeadGap W r0) (4 : Real)) := by
  exact @Erdos390.WholePaper.eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap
