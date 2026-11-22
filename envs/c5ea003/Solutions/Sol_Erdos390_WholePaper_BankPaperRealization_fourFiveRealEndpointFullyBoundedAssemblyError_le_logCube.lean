-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.fourFiveRealEndpointFullyBoundedAssemblyError_le_logCube
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:57:31.008428+00:00
-- url     : https://prove2.me/submissions/1a80ef4d-be80-41e2-988e-ed93b0998f3d

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_009

/- Source module: Erdos390.Full.PrimeBandQuadrature -/
section


/-!
# Audited harmonic prime quadrature on moving positive cells

The continuum transfer in Lemma 8.4 uses prime cells whose endpoints are
powers of the smoothness scale.  This file starts the required arithmetic
quadrature from the actual Chebyshev function.  The key identity below has no
Mertens constant: it subtracts Abel summation at two endpoints and isolates
the quantitative PNT remainder exactly.
-/

open scoped BigOperators
open Set
open Filter Topology Asymptotics

noncomputable section

namespace Erdos390.Full.PrimeBandQuadrature

open MeasureTheory
open Erdos390.Full.PrimeSums
open Erdos390.Full.FriableAsymptotic



























/-! ## The first logarithmic moment -/















/-! ## Quantitative PNT remainder -/





















/-! ## Exact alignment with the paper's logarithmic coordinate -/





















theorem fullReciprocalSumUniformConstant_pos :
    0 < fullReciprocalSumUniformConstant :=
  (Classical.choose_spec
    exists_fullReciprocalSum_interval_error_bound).1







end Erdos390.Full.PrimeBandQuadrature

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveOrderedLastPrimeExpansion -/
section


/-!
# Exact last-prime expansion in the four/five chamber

This file exposes the last prime in each ordered layer before any analytic
approximation is made.  The existing finite reduction represents ordered
prime factors by lists.  Here those lists are identified with fixed-length
tuples, a tuple of length `m + 1` is split into its first `m` entries and its
last entry, and the last-entry fibre is identified with the literal prime
interval

`(max y (A / q), B / q]`,  where `q` is the prefix product.

The final theorem applies the uniform `pi-li` endpoint theorem at these exact
moving endpoints and sums its errors.  In particular, no relative estimate
for a short prime interval is used or assumed.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

/-! ## Fixed-length tuples and the existing ordered-list layer -/















/-! ## Splitting off the last coordinate -/





















/-! ## Every last-prime fibre is an exact clipped prime interval -/







/-- A prime prefix has positive product. -/
theorem fourFiveOrderedPrimePrefix_prod_pos
    {m y B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    0 < ∏ i, q i := by
  apply Finset.prod_pos
  intro i _hi
  exact (mem_fourFiveOrderedPrimePrefixSet.mp hq i).2.2.pos



/-! ## Applying the endpoint theorem fibrewise -/

















end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveReciprocalPrimeBV -/
section


/-!
# Reciprocal-prime bounded-variation transfer for the four/five chamber

This file turns the audited two-endpoint Mertens estimate in
`PrimeBandQuadrature` into a finite signed-measure statement that can be
iterated in the ordered-prime mixture.

On every integer cell `(m-1,m]` we subtract the continuum mass

`log(log m) - log(log (m-1))`

from the actual reciprocal-prime atom.  The prefix of this signed cell
measure is exactly the two-endpoint reciprocal-prime discrepancy.  Finite
Abel summation then bounds its pairing with an arbitrary sequence by the
uniform discrepancy times the right-endpoint value plus the sequence's
discrete variation.  No smoothness hypothesis and no new analytic axiom are
used.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

























theorem fourFiveReciprocalBVSafeCutoff_ge_two :
    2 <= fourFiveReciprocalBVSafeCutoff :=
  le_max_right _ _























end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveProductMeasureTelescope -/
section


/-!
# The finite product-measure telescope in the four/five chamber

The ordered-prime argument replaces at most three reciprocal-prime
coordinates by their continuum log-log cell masses.  This file carries out
that replacement literally on the finite cell set `(A,Y]`.

There are two separate ingredients.

* `fourFiveFiniteProductOne/Two/Three` record the one-, two-, and
  three-coordinate product pairings.  Their subtraction identities are
  purely algebraic telescopes.
* The specializations to reciprocal-prime and log-log cell weights identify
  every telescope summand with the one-dimensional BV defect proved in
  `BankPaperFourFiveReciprocalPrimeBV`.  Absolute outer mass and discrete BV
  norms then give the losses `M^0`, `M^1`, and `M^2` for one, two, and three
  coordinates respectively.

No independence, positivity, smoothness, or analytic hypothesis is hidden in
the telescope identities.  The quantitative theorems ask only for the
displayed finite mass and conditional discrete-BV bounds.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeBandQuadrature

/-! ## Generic finite product pairings and exact telescopes -/













/-! ## Two elementary norm ledgers -/







/-! ## Reciprocal-prime specialization -/



theorem fourFiveReciprocalBVError_pos
    {A : Nat} (hA : fourFiveReciprocalBVSafeCutoff <= A) :
    0 < fourFiveReciprocalBVError A := by
  have hA2 : 2 <= A :=
    fourFiveReciprocalBVSafeCutoff_ge_two.trans hA
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  unfold fourFiveReciprocalBVError
  exact div_pos
    (mul_pos (by norm_num) fullReciprocalSumUniformConstant_pos)
    (pow_pos hlogA 3)



















/-! ## Quantitative one-, two-, and three-coordinate transfer -/







end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveRealLastPrimeEndpoint -/
section


/-!
# Real moving endpoints for the exposed last prime

The natural quotient endpoints used for the first exact cardinal expansion
are convenient combinatorially, but they introduce an avoidable unit-cell
rounding loss before the physical substitution `t = qv`.  The prime-counting
endpoint theorem accepts arbitrary real endpoints.  We therefore apply it at

`a = max y (A/q)` and `b = B/q`

in the real field.  Their natural floors are exactly the earlier quotient
endpoints, so the prime fibre is unchanged.  After this refinement the
physical substitution has the exact endpoints `max (q*y) A` and `B`.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization



theorem fourFiveRealPrefixProduct_pos
    {m y B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    0 < fourFiveRealPrefixProduct q := by
  unfold fourFiveRealPrefixProduct
  exact_mod_cast fourFiveOrderedPrimePrefix_prod_pos hq















theorem fourFiveLastPrimeRealLower_ge_y
    {m y A : Nat} (q : Fin m -> Nat) :
    (y : Real) <= fourFiveLastPrimeRealLower q y A := by
  exact le_max_left _ _



















/-! ## Quantitative fifth-log ledger -/





/-- Ordered prefix reciprocal mass is exactly the `m`th power of the
one-coordinate prime-band mass. -/
theorem fourFiveOrderedPrimePrefixReciprocalMass_eq_pow
    (m y B : Nat) :
    fourFiveOrderedPrimePrefixReciprocalMass m y B =
      fourFivePrimeCoordinateReciprocalMass y B ^ m := by
  unfold fourFiveOrderedPrimePrefixReciprocalMass
    fourFiveOrderedPrimePrefixSet
    fourFivePrimeCoordinateReciprocalMass
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro q _hq
  unfold fourFiveRealPrefixProduct
  rw [Nat.cast_prod, ← Finset.prod_inv_distrib]

theorem fourFivePrimeCoordinateReciprocalMass_nonneg
    (y B : Nat) :
    0 <= fourFivePrimeCoordinateReciprocalMass y B := by
  unfold fourFivePrimeCoordinateReciprocalMass
  positivity

/-- One fibre's real-endpoint PNT loss is its reciprocal-prefix weight times
the common fifth-log factor at `y`. -/
theorem fourFiveLastPrimeRealEndpointError_le_reciprocalWeight
    {m y A B : Nat} {q : Fin m -> Nat} {C : Real}
    (hC : 0 <= C) (hy : 2 <= y)
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveLastPrimeRealEndpointError C q y A B <=
      (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
        (fourFiveRealPrefixProduct q)⁻¹ := by
  have hQpos : 0 < fourFiveRealPrefixProduct q :=
    fourFiveRealPrefixProduct_pos hq
  have hlogy : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hyRealPos : (0 : Real) < (y : Real) := by
    exact_mod_cast (show 0 < y by omega)
  have hyRealOne : (1 : Real) < (y : Real) := by
    exact_mod_cast (show 1 < y by omega)
  by_cases hLU : fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B
  · have hLowerPos : 0 < fourFiveLastPrimeRealLower q y A :=
      hyRealPos.trans_le
        (fourFiveLastPrimeRealLower_ge_y q)
    have hlogLower : 0 < Real.log (fourFiveLastPrimeRealLower q y A) :=
      Real.log_pos (hyRealOne.trans_le
        (fourFiveLastPrimeRealLower_ge_y q))
    have hlogLe : Real.log (y : Real) <=
        Real.log (fourFiveLastPrimeRealLower q y A) :=
      Real.log_le_log (by exact_mod_cast (show 0 < y by omega))
        (fourFiveLastPrimeRealLower_ge_y q)
    have hpow : Real.log (y : Real) ^ 5 <=
        Real.log (fourFiveLastPrimeRealLower q y A) ^ 5 :=
      pow_le_pow_left₀ hlogy.le hlogLe 5
    have hUpperNonneg : 0 <= fourFiveLastPrimeRealUpper q B := by
      unfold fourFiveLastPrimeRealUpper
      positivity
    unfold fourFiveLastPrimeRealEndpointError
    rw [if_pos hLU]
    calc
      3 * C * fourFiveLastPrimeRealUpper q B /
          Real.log (fourFiveLastPrimeRealLower q y A) ^ 5 <=
        3 * C * fourFiveLastPrimeRealUpper q B /
          Real.log (y : Real) ^ 5 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg (by norm_num) hC) hUpperNonneg)
          (pow_pos hlogy 5) hpow
      _ = (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
          (fourFiveRealPrefixProduct q)⁻¹ := by
        unfold fourFiveLastPrimeRealUpper
        field_simp [hQpos.ne', hlogy.ne']
  · unfold fourFiveLastPrimeRealEndpointError
    rw [if_neg hLU]
    positivity

/-- Summed real-endpoint loss with the exact prefix reciprocal mass. -/
theorem fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_prefixMass
    {C : Real} (hC : 0 <= C) {m y A B : Nat} (hy : 2 <= y) :
    fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B <=
      (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
        fourFiveOrderedPrimePrefixReciprocalMass m y B := by
  unfold fourFiveOrderedLastPrimeRealEndpointErrorLayer
    fourFiveOrderedPrimePrefixReciprocalMass
  calc
    (∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        fourFiveLastPrimeRealEndpointError C q y A B) <=
      ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
          (fourFiveRealPrefixProduct q)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      exact fourFiveLastPrimeRealEndpointError_le_reciprocalWeight
        hC hy hq
    _ = (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
        ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
          (fourFiveRealPrefixProduct q)⁻¹ := by
      rw [Finset.mul_sum]

/-- If the one-coordinate reciprocal mass is at most `M`, the layer endpoint
loss is at most `3 C B M^m / log(y)^5`. -/
theorem fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_massPow
    {C M : Real} (hC : 0 <= C) {m y A B : Nat} (hy : 2 <= y)
    (hmass : fourFivePrimeCoordinateReciprocalMass y B <= M) :
    fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B <=
      (3 * C * (B : Real) / Real.log (y : Real) ^ 5) * M ^ m := by
  have hcoeff : 0 <=
      3 * C * (B : Real) / Real.log (y : Real) ^ 5 := by
    positivity
  have hmassPow : fourFivePrimeCoordinateReciprocalMass y B ^ m <= M ^ m :=
    pow_le_pow_left₀ (fourFivePrimeCoordinateReciprocalMass_nonneg y B)
      hmass m
  calc
    fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B <=
        (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
          fourFiveOrderedPrimePrefixReciprocalMass m y B :=
      fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_prefixMass hC hy
    _ = (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
        fourFivePrimeCoordinateReciprocalMass y B ^ m := by
      rw [fourFiveOrderedPrimePrefixReciprocalMass_eq_pow]
    _ <= (3 * C * (B : Real) / Real.log (y : Real) ^ 5) * M ^ m :=
      mul_le_mul_of_nonneg_left hmassPow hcoeff





end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveMovingFaceCellOscillation -/
section


/-!
# Log-log cells at the strict moving face

The continuum replacement in the four/five chamber is a finite collection
of the paper's literal cells `(n-1,n]`, with measure `dx/(x log x)`.  This
file proves the right-endpoint quadrature estimate for the one-dimensional
conditional moving-face kernel.

There are two contributions.  On cells whose right endpoint is active, the
reciprocal kernel is increasing and the cell oscillations telescope to at
most one.  There is at most one further cell whose interior is active while
its right endpoint is inactive; that unique strict-face cell costs at most
one.  Thus the total oscillation envelope is at most two.  Since every
paper cell has mass at most

`delta_A = 1 / (A log A)`,

the finite cell quadrature defect is at most `2 delta_A`.  No limiting mesh
or convergence hypothesis occurs.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## The real conditional moving face -/























/-! ## The unique cell crossed by the strict face -/









/-! ## A two-unit finite oscillation envelope -/

















/-! ## Pointwise right-endpoint control -/



/-! ## The mesh is derived from the literal paper cells -/



theorem fourFiveLogLogCellMeshBound_pos
    {A : Nat} (hA : 2 <= A) :
    0 < fourFiveLogLogCellMeshBound A := by
  have hAreal : 0 < (A : Real) := by positivity
  have hlog : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  unfold fourFiveLogLogCellMeshBound
  positivity















/-! ## The finite one-dimensional quadrature defect -/





























end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveSignedCoreErrorAdapter -/
section


/-!
# Error adapter from the four/five assembly to a signed smooth core

The four/five continuum calculation ends with a completely explicit error
ledger.  This file performs the remaining algebra needed by the signed
exceptional-core argument:

* compress the four factorially weighted assembly errors to one
  `Z / log(y)^3` bound;
* add the repeated-prime transfer and convert `log(y)` to the paper scale
  `L`;
* freeze the continuum mixture kernel at one reference logarithmic
  coordinate;
* expose the exact balanced normalization for the paper multiplicity
  `K0 + 1`;
* combine three independently estimated physical intervals without losing
  the signed periodic main term.

The module deliberately does not identify a literal smooth-core fibre with
the three rough intervals.  That finite reindexing is an independent input
to the final connector.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Compression of the explicit four-layer error ledger -/





theorem fourFiveEndpointFactorialMassPolynomial_nonneg
    {M : Real} (hM : 0 <= M) :
    0 <= fourFiveEndpointFactorialMassPolynomial M := by
  unfold fourFiveEndpointFactorialMassPolynomial
  positivity

theorem fourFiveTransferFactorialMassPolynomial_nonneg
    {M : Real} (hM : 0 <= M) :
    0 <= fourFiveTransferFactorialMassPolynomial M := by
  unfold fourFiveTransferFactorialMassPolynomial
  positivity





/-- The literal fully bounded assembly error is `O(Z/log(y)^3)`.

The assumptions `B <= Z`, `log(y) <= y`, and `1 <= log(y)` are precisely
the elementary scale facts used in the conversion.  No asymptotic theorem
is hidden in this statement. -/
theorem fourFiveRealEndpointFullyBoundedAssemblyError_le_logCube
    {C M Z : Real} {y A B : Nat}
    (hC : 0 <= C) (hM : 0 <= M)
    (hy : 2 <= y) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hlogOne : 1 <= Real.log (y : Real))
    (hlogLeY : Real.log (y : Real) <= (y : Real))
    (hZ : (B : Real) <= Z) (hZ0 : 0 <= Z)
    (hprimeMass : fourFivePrimeCoordinateReciprocalMass y B <= M) :
    fourFiveRealEndpointFullyBoundedAssemblyError C y A B M <=
      fourFiveSignedCoreAssemblyLogCubeConstant C M *
        (Z / Real.log (y : Real) ^ 3) := by
  let s := Real.log (y : Real)
  let length := (B : Real) - (A : Real)
  let q := 3 * C * (B : Real) / s ^ 5
  let outer := (1 / s) * length
  let E := fourFiveReciprocalBVError y
  let mesh := fourFiveLogLogCellMeshBound y
  have hs : 0 < s := by
    dsimp only [s]
    linarith
  have hyReal : (0 : Real) < (y : Real) := by positivity
  have hlength0 : 0 <= length := by
    dsimp only [length]
    exact sub_nonneg.mpr (by exact_mod_cast hAB)
  have hlength : length <= Z := by
    dsimp only [length]
    have hA0 : (0 : Real) <= (A : Real) := by positivity
    linarith
  have hq0 : 0 <= q := by
    dsimp only [q, s]
    positivity
  have hE0 : 0 <= E := by
    dsimp only [E]
    exact (fourFiveReciprocalBVError_pos hcut).le
  have hmesh0 : 0 <= mesh := by
    dsimp only [mesh]
    exact (fourFiveLogLogCellMeshBound_pos hy).le
  have houter0 : 0 <= outer := by
    dsimp only [outer]
    positivity
  have hend0 :=
    fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_massPow
      (C := C) (M := M) (m := 0) (y := y) (A := A) (B := B)
      hC hy hprimeMass
  have hend1 :=
    fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_massPow
      (C := C) (M := M) (m := 1) (y := y) (A := A) (B := B)
      hC hy hprimeMass
  have hend2 :=
    fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_massPow
      (C := C) (M := M) (m := 2) (y := y) (A := A) (B := B)
      hC hy hprimeMass
  have hend3 :=
    fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_massPow
      (C := C) (M := M) (m := 3) (y := y) (A := A) (B := B)
      hC hy hprimeMass
  change
      fourFiveOrderedLastPrimeRealEndpointErrorLayer C 0 y A B <=
        q * M ^ 0 at hend0
  change
      fourFiveOrderedLastPrimeRealEndpointErrorLayer C 1 y A B <=
        q * M ^ 1 at hend1
  change
      fourFiveOrderedLastPrimeRealEndpointErrorLayer C 2 y A B <=
        q * M ^ 2 at hend2
  change
      fourFiveOrderedLastPrimeRealEndpointErrorLayer C 3 y A B <=
        q * M ^ 3 at hend3
  have hledger :
      fourFiveRealEndpointFullyBoundedAssemblyError C y A B M <=
        q * fourFiveEndpointFactorialMassPolynomial M +
          (outer * E + outer * mesh) *
            fourFiveTransferFactorialMassPolynomial M := by
    norm_num [pow_zero, pow_one] at hend0 hend1
    rw [show
      fourFiveRealEndpointFullyBoundedAssemblyError C y A B M =
        fourFiveOrderedLastPrimeRealEndpointErrorLayer C 0 y A B +
          fourFiveOrderedLastPrimeRealEndpointErrorLayer C 1 y A B / 2 +
          fourFiveOrderedLastPrimeRealEndpointErrorLayer C 2 y A B / 6 +
          fourFiveOrderedLastPrimeRealEndpointErrorLayer C 3 y A B / 24 +
          (outer * E + outer * mesh) *
            fourFiveTransferFactorialMassPolynomial M by
      unfold fourFiveRealEndpointFullyBoundedAssemblyError
        fourFiveFactorialErrorLedger
        fourFiveTransferFactorialMassPolynomial
      dsimp [fourFiveMovingFaceProductError,
        fourFiveLebesgueCellAggregationBudget,
        fourFivePhysicalOuterScaledBVError, outer, E, mesh]
      ring]
    unfold fourFiveEndpointFactorialMassPolynomial
    nlinarith [hend0, hend1, hend2, hend3]
  have hsThreeFour : s ^ 3 <= s ^ 4 := by
    have hsOne : 1 <= s := by simpa only [s] using hlogOne
    calc
      s ^ 3 = s ^ 3 * 1 := by ring
      _ <= s ^ 3 * s :=
        mul_le_mul_of_nonneg_left hsOne (pow_nonneg hs.le 3)
      _ = s ^ 4 := by ring
  have hsThreeFive : s ^ 3 <= s ^ 5 := by
    have hsOne : 1 <= s := by simpa only [s] using hlogOne
    have hsSq : 1 <= s ^ 2 := one_le_pow₀ (n := 2) hsOne
    calc
      s ^ 3 = s ^ 3 * 1 := by ring
      _ <= s ^ 3 * s ^ 2 :=
        mul_le_mul_of_nonneg_left hsSq (pow_nonneg hs.le 3)
      _ = s ^ 5 := by ring
  have hq :
      q <= 3 * C * (Z / s ^ 3) := by
    dsimp only [q]
    have hnum : 0 <= 3 * C * (B : Real) := by positivity
    calc
      3 * C * (B : Real) / s ^ 5 <=
          3 * C * (B : Real) / s ^ 3 :=
        div_le_div_of_nonneg_left hnum (pow_pos hs 3) hsThreeFive
      _ <= 3 * C * Z / s ^ 3 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hZ (by positivity))
          (pow_pos hs 3).le
      _ = 3 * C * (Z / s ^ 3) := by ring
  have hBV :
      outer * E <=
        (5 * fullReciprocalSumUniformConstant) *
          (Z / s ^ 3) := by
    have hdiv :
        length / s ^ 4 <= Z / s ^ 3 := by
      apply (div_le_div_iff₀ (pow_pos hs 4) (pow_pos hs 3)).2
      calc
        length * s ^ 3 <= Z * s ^ 3 :=
          mul_le_mul_of_nonneg_right hlength (pow_nonneg hs.le 3)
        _ <= Z * s ^ 4 :=
          mul_le_mul_of_nonneg_left hsThreeFour hZ0
    dsimp only [outer, E, s]
    unfold fourFiveReciprocalBVError
    calc
      (1 / Real.log (y : Real)) * length *
          (5 * fullReciprocalSumUniformConstant /
            Real.log (y : Real) ^ 3) =
        (5 * fullReciprocalSumUniformConstant) *
          (length / Real.log (y : Real) ^ 4) := by ring
      _ <=
        (5 * fullReciprocalSumUniformConstant) *
          (Z / Real.log (y : Real) ^ 3) :=
        mul_le_mul_of_nonneg_left hdiv
          (mul_nonneg (by norm_num)
            fullReciprocalSumUniformConstant_pos.le)
  have hmesh :
      outer * mesh <= Z / s ^ 3 := by
    have hbase :
        length / ((y : Real) * s ^ 2) <= Z / s ^ 3 := by
      apply (div_le_div_iff₀
        (mul_pos hyReal (pow_pos hs 2)) (pow_pos hs 3)).2
      have hlengthLog : length * s <= Z * (y : Real) := by
        calc
          length * s <= Z * s :=
            mul_le_mul_of_nonneg_right hlength hs.le
          _ <= Z * (y : Real) :=
            mul_le_mul_of_nonneg_left
              (by simpa only [s] using hlogLeY) hZ0
      calc
        length * s ^ 3 = (length * s) * s ^ 2 := by ring
        _ <= (Z * (y : Real)) * s ^ 2 :=
          mul_le_mul_of_nonneg_right hlengthLog (pow_nonneg hs.le 2)
        _ = Z * ((y : Real) * s ^ 2) := by ring
    dsimp only [outer, mesh, s]
    unfold fourFiveLogLogCellMeshBound
    calc
      (1 / Real.log (y : Real)) * length *
          (1 / ((y : Real) * Real.log (y : Real))) =
        length /
          ((y : Real) * Real.log (y : Real) ^ 2) := by ring
      _ <= Z / Real.log (y : Real) ^ 3 := hbase
  have htransfer :
      outer * E + outer * mesh <=
        (5 * fullReciprocalSumUniformConstant + 1) *
          (Z / s ^ 3) := by
    calc
      outer * E + outer * mesh <=
          (5 * fullReciprocalSumUniformConstant) *
              (Z / s ^ 3) +
            Z / s ^ 3 := add_le_add hBV hmesh
      _ =
          (5 * fullReciprocalSumUniformConstant + 1) *
            (Z / s ^ 3) := by ring
  have hendpointPoly :=
    fourFiveEndpointFactorialMassPolynomial_nonneg hM
  have htransferPoly :=
    fourFiveTransferFactorialMassPolynomial_nonneg hM
  calc
    fourFiveRealEndpointFullyBoundedAssemblyError C y A B M <=
        q * fourFiveEndpointFactorialMassPolynomial M +
          (outer * E + outer * mesh) *
            fourFiveTransferFactorialMassPolynomial M := hledger
    _ <=
        (3 * C * (Z / s ^ 3)) *
            fourFiveEndpointFactorialMassPolynomial M +
          ((5 * fullReciprocalSumUniformConstant + 1) *
            (Z / s ^ 3)) *
              fourFiveTransferFactorialMassPolynomial M :=
      add_le_add
        (mul_le_mul_of_nonneg_right hq hendpointPoly)
        (mul_le_mul_of_nonneg_right htransfer htransferPoly)
    _ =
        fourFiveSignedCoreAssemblyLogCubeConstant C M *
          (Z / Real.log (y : Real) ^ 3) := by
      dsimp only [s]
      unfold fourFiveSignedCoreAssemblyLogCubeConstant
      ring



/-! ## Freezing the common continuum kernel -/







/-! ### Quotient endpoints and ideal physical lengths -/





/-! ## Exact `K0+1` balance and signed three-interval algebra -/







/-! ## Positive cutoff-band algebra -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution :
∀ {C M Z : Real} {y A B : Nat},
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) M →
      LE.le.{0} (2 : Nat) y →
        LE.le.{0} A B →
          LE.le.{0} Erdos390.WholePaper.BankPaperRealization.fourFiveReciprocalBVSafeCutoff y →
            LE.le.{0} (1 : Real) (Real.log ↑y) →
              LE.le.{0} (Real.log ↑y) ↑y →
                LE.le.{0} (↑B) Z →
                  LE.le.{0} (0 : Real) Z →
                    LE.le.{0} (Erdos390.WholePaper.BankPaperRealization.fourFivePrimeCoordinateReciprocalMass y B) M →
                      LE.le.{0}
                        (Erdos390.WholePaper.BankPaperRealization.fourFiveRealEndpointFullyBoundedAssemblyError C y A B
                          M)
                        (HMul.hMul.{0, 0, 0}
                          (Erdos390.WholePaper.BankPaperRealization.fourFiveSignedCoreAssemblyLogCubeConstant C M)
                          (HDiv.hDiv.{0, 0, 0} Z (HPow.hPow.{0, 0, 0} (Real.log ↑y) (3 : Nat)))) := by
  exact @Erdos390.WholePaper.BankPaperRealization.fourFiveRealEndpointFullyBoundedAssemblyError_le_logCube
