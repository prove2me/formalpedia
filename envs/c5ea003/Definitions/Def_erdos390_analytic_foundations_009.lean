-- Prove2me | Definitions.Def_erdos390_analytic_foundations_009
-- name    : erdos390_analytic_foundations_009
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T15:04:20.583723+00:00
-- url     : https://prove2.me/theorems/49ae7163-2a42-4e3c-8273-9c804d3e1735
-- title:
--   Sharp Saias variation and signed exceptional four-to-five geometry
-- statement:
--   This bundle defines fully-real Saias normal forms, natural Buchstab-cell remainders, quotient blocks and oscillation ledgers, balanced source selectors, signed guard/exceptional residuals, and the ordered prime-tuple and simplex integrals used in the four-to-five rough chamber.
--
--   For $X,m\in\mathbb N$, write $q_m=\lfloor X/m\rfloor$. The selector cell ledger separates quotient drop from reciprocal-logarithmic drift:
--   $$S_X(m)=\frac{q_m-q_{m+1}}{\log m}+q_{m+1}\left(\frac1{\log m}-\frac1{\log(m+1)}\right).$$
--   For real residual components, the complete signed residual is defined by
--   $$R_{\rm complete}=R_{\rm raw}-R_{\rm exceptional}-R_{\rm row}+R_{\rm guard}.$$
--   The four-to-five interfaces record ordered prime products, last-prime fibres, discrete reciprocal-prime versus continuum log-log measures, moving and fixed simplex kernels, and their endpoint, variation and aggregation error quantities.
--
--   These definitions retain the signs and moving cutoffs needed for sharp valuation-deficit estimates. Geometry and chamber-estimate structures explicitly package required hypotheses; their definitions alone do not supply the corresponding bounds.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/RoughSaiasFullyRealBuchstabCells.lean; grouped definitions extracted from multiple source modules at this commit, including Erdos390.WholePaper.RoughSaiasFullyRealNormalForm, Erdos390.WholePaper.RoughSaiasFunctionalBuchstab, Erdos390.WholePaper.RoughSaiasFullyRealBuchstabCells, with the remaining originating modules identified by source-module comments in the definition body.

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_008


/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealNormalForm -/
section


/-!
# The Saias normal form with a genuinely real base

Continuous Buchstab produces inner terms `Lambda(x/s,s)` with a real base
`s`.  The project's original `roughSaiasG` takes a natural base, so it
cannot state that identity directly.  This file supplies the literal real
analogue, proves the same signed base-free substitution, and identifies it
exactly with the finite Stieltjes functional.  At natural bases it reduces
definitionally to the existing normal form.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Fully real Saias data -/

noncomputable def roughSaiasFullyRealFractionalWeight
    (y v : ℝ) : ℝ :=
  Int.fract (y ^ v) * y ^ (-v)

noncomputable def roughSaiasFullyRealG (y u : ℝ) : ℝ :=
  rho u - ∫ v in (0 : ℝ)..5,
    roughSaiasDickmanDerivative (u - v) *
      roughSaiasFullyRealFractionalWeight y v

noncomputable def roughSaiasFullyRealLambdaNormalForm
    (x y : ℝ) : ℝ :=
  x * roughSaiasFullyRealG y (Real.log x / Real.log y) - Int.fract x

noncomputable def roughSaiasFullyRealBaseFreeFractionalKernel
    (x y t : ℝ) : ℝ :=
  roughSaiasDickmanDerivative
      ((Real.log x - Real.log t) / Real.log y) *
    Int.fract t / (Real.log y * t ^ (2 : ℕ))

noncomputable def roughSaiasFullyRealBaseFreeFractionalIntegral
    (x y : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..y ^ (5 : ℝ),
    roughSaiasFullyRealBaseFreeFractionalKernel x y t







/-! ## Exact real-base substitution -/























@[simp]
theorem roughSaiasFullyRealFractionalWeight_nat (m : ℕ) (v : ℝ) :
    roughSaiasFullyRealFractionalWeight (m : ℝ) v =
      roughSaiasFractionalWeight m v := rfl

@[simp]
theorem roughSaiasFullyRealG_nat (m : ℕ) (u : ℝ) :
    roughSaiasFullyRealG (m : ℝ) u = roughSaiasG m u := by
  rfl

@[simp]
theorem roughSaiasFullyRealLambdaNormalForm_nat
    (x : ℝ) (m : ℕ) :
    roughSaiasFullyRealLambdaNormalForm x (m : ℝ) =
      roughSaiasLambdaNormalForm x m := by
  rfl

@[simp]
theorem roughSaiasFullyRealBaseFreeKernel_nat
    (x : ℝ) (m : ℕ) (t : ℝ) :
    roughSaiasFullyRealBaseFreeFractionalKernel x (m : ℝ) t =
      roughSaiasRealBaseFreeFractionalKernel x m t := by
  rfl

/-! ## Exact Stieltjes identification at a real base -/











end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFunctionalBuchstab -/
section


/-!
# Lifting pointwise continuous Buchstab through the finite signed functional

The pointwise identity in `RoughSaiasContinuousBuchstab` is now lifted
through the finite atom-minus-density functional.  The finite atomic swap is
proved unconditionally.  The density swap is stated with its exact compact
Fubini datum; that datum is ordinary product integrability of an explicit
bounded measurable kernel, not an endpoint or defect estimate.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full.DickmanBasic

noncomputable section

/-- The compact two-variable density kernel in the Fubini step. -/
noncomputable def roughSaiasBuchstabDensityKernel
    (x : ℝ) (s t : ℝ) : ℝ :=
  roughSaiasContinuousBuchstabProfile x s t *
    roughSaiasFloorDensity t

/-- The precise ordinary-integrability datum needed for the density
Fubini swap.  No counting function, normal-form defect, or error bound
occurs here. -/
def RoughSaiasBuchstabDensityFubini
    (R : ℕ) (x y z : ℝ) : Prop :=
  IntegrableOn
      (fun t ↦ roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (R : ℝ)) ∧
    IntegrableOn
      (fun t ↦ roughSaiasStieltjesDickmanProfile x z t *
        roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (R : ℝ)) ∧
    Integrable (Function.uncurry (roughSaiasBuchstabDensityKernel x))
      ((volume.restrict (Set.Ioc y z)).prod
        (volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ))))



/-! ## Discharging the compact Fubini datum -/























/-! ## The finite atomic lift -/



/-! ## The density Fubini lift -/



/-! ## Functional continuous Buchstab -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealBuchstabCells -/
section


/-!
# Unit-cell decomposition of the fully real Buchstab integral

The functional continuous-Buchstab identity is converted here into the
project's natural-base normal forms.  On a cell `s ∈ [m,m+1]`, the inner
term is split exactly into

* quotient drift at the current real base `s`, and
* real-base drift from `s` to the natural endpoint `m+1`.

No equality between the real and natural bases is left as a premise.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full

noncomputable section

noncomputable def roughSaiasFullyRealBuchstabNormalIntegrand
    (X : ℕ) (s : ℝ) : ℝ :=
  roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s /
    Real.log s

noncomputable def roughSaiasRealQuotientSelectorIntegrand
    (X : ℕ) (s : ℝ) : ℝ :=
  (((⌊(X : ℝ) / s⌋₊ : ℕ) : ℝ)) / Real.log s











/-! ## Natural unit cells -/













noncomputable def roughSaiasFullyRealBuchstabCellRemainder
    (X m : ℕ) : ℝ :=
  ∫ s in (m : ℝ)..(m + 1 : ℕ),
    (roughSaiasFullyRealBuchstabNormalIntegrand X s -
      roughSaiasNormalFormThetaWeight X (m + 1))







noncomputable def roughSaiasSelectorCellLedger (X m : ℕ) : ℝ :=
  (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
      Real.log (m : ℝ) +
    ((X / (m + 1) : ℕ) : ℝ) *
      (1 / Real.log (m : ℝ) -
        1 / Real.log ((m + 1 : ℕ) : ℝ))















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSelectorLedgerBound -/
section


/-!
# Summing the upper-cell quotient-selector ledger

On cells above the square-root transition the fully real Buchstab
integrand is the elementary quotient selector

`floor (X / s) / log s`.

The cell ledger from `RoughSaiasFullyRealBuchstabCells` has two pieces.
The natural quotient drops telescope exactly, while the reciprocal-log
variation is bounded by the convergent `sum 1 / m^2` tail.  This file makes
that summation quantitative without any asymptotic or defect premise.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- The natural quotient drop occurring in the upper selector ledger. -/
noncomputable def roughSaiasNaturalQuotientDrop (X m : ℕ) : ℝ :=
  ((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealNaturalCells -/
section


/-!
# Fully real cells with the floor/frac-paired natural endpoint sample

Sampling a fully real Buchstab cell by the continuous real-quotient theta
weight leaves a separate signed floor correction.  Sampling instead by the
natural quotient theta weight pairs that correction inside the cell.  The
sum of these paired cells is therefore exactly the natural integer Abel
consistency defect, with no signed-floor term left over.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- Unit-cell quadrature remainder with the floor/frac-paired natural
endpoint sample. -/
noncomputable def roughSaiasFullyRealNaturalBuchstabCellRemainder
    (X m : ℕ) : ℝ :=
  roughSaiasFullyRealBuchstabCellRemainder X m +
    roughSaiasFractionalCorrectionThetaWeight X (m + 1)

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasNaturalThetaLedgerBound -/
section


/-!
# Deterministic reduction of the natural-theta transfer ledger

The fourth-power PNT input is already unconditional in the project.  This
file bounds both endpoint coefficients in its finite-Abel ledger and leaves
only one explicit weighted discrete variation of the paired natural theta
weight.  Thus neither a defect bound nor a signed-floor estimate remains as
an input to the theta transfer.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- The sole interior term left in the natural-theta finite-Abel ledger. -/
noncomputable def roughSaiasNaturalThetaPNTVariationLedger
    (A C : ℝ) (X y Z : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc y (Z - 1),
    |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m| *
      (C * ((m : ℝ) / Real.log (m : ℝ) ^ A))

/-- Elementary endpoint envelope after using `|G| ≤ 16`. -/
noncomputable def roughSaiasNaturalThetaPNTEndpointEnvelope
    (A C : ℝ) (X y Z : ℕ) : ℝ :=
  (16 * (X : ℝ) / ((Z : ℝ) * Real.log (Z : ℝ))) *
      (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ A)) +
    (16 * (X : ℝ) /
        (((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ))) *
      (C * ((y : ℝ) / Real.log (y : ℝ) ^ A))















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasCellTransitionSplit -/
section


/-!
# Splitting at the square-root selector transition

The upper selector cells and the Dickman core of the theta transfer are
already of inverse-log-square size.  This file records the exact split at
an arbitrary transition `M`.  It isolates precisely two remaining explicit
terms: the lower paired-cell block and the natural-minus-Dickman theta
residual.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Canonical natural transition just above `sqrt X`, enlarged to retain
the original left endpoint. -/
def roughSaiasSelectorTransition (X y : ℕ) : ℕ :=
  max y (Nat.sqrt X + 1)



















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasQuotientBlocks -/
section


/-!
# Hyperbola blocks for the Saias base variation

The transformed sawtooth kernel has a fixed natural quotient on each fibre
of `m ↦ X / m`.  This file records the elementary, but useful, fact that
those fibres are honest intervals and gives a fibrewise decomposition of
finite sums.  No estimate is used here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- The bases in `(y,Z]` having the fixed hyperbola quotient `q`. -/
def roughSaiasQuotientBlock (X q y Z : ℕ) : Finset ℕ :=
  (Finset.Ioc y Z).filter (fun m => X / m = q)



/-- A natural quotient is `q` exactly between its two multiplication
inequalities.  The positive-denominator hypothesis is the only boundary
condition needed. -/
theorem natDiv_eq_iff_mul_bounds
    {X m q : ℕ} (hm : 0 < m) :
    X / m = q ↔ q * m ≤ X ∧ X < (q + 1) * m := by
  constructor
  · intro h
    constructor
    · apply (Nat.le_div_iff_mul_le hm).mp
      rw [h]
    · apply (Nat.div_lt_iff_lt_mul hm).mp
      rw [h]
      omega
  · rintro ⟨hlo, hhi⟩
    apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hm).mpr hhi)
    · exact (Nat.le_div_iff_mul_le hm).mpr hlo

/-- Positive quotient fibres have the usual hyperbola interval
description `(X/(q+1), X/q]`. -/
theorem natDiv_eq_iff_mem_hyperbolaIoc
    {X m q : ℕ} (hm : 0 < m) (hq : 0 < q) :
    X / m = q ↔ X / (q + 1) < m ∧ m ≤ X / q := by
  rw [natDiv_eq_iff_mul_bounds hm]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)).mpr
      simpa [Nat.mul_comm] using hhi
    · apply (Nat.le_div_iff_mul_le hq).mpr
      simpa [Nat.mul_comm] using hlo
  · rintro ⟨hlo, hhi⟩
    constructor
    · have h := (Nat.le_div_iff_mul_le hq).mp hhi
      simpa [Nat.mul_comm] using h
    · have h :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)).mp hlo
      simpa [Nat.mul_comm] using h

@[simp]
theorem mem_roughSaiasQuotientBlock
    {X q y Z m : ℕ} :
    m ∈ roughSaiasQuotientBlock X q y Z ↔
      y < m ∧ m ≤ Z ∧ X / m = q := by
  simp only [roughSaiasQuotientBlock, Finset.mem_filter,
    Finset.mem_Ioc]
  tauto













/-! ## The dual hyperbola partition -/

/-- The quotient interval dual to the base cell `[m,m+1]`.  Its members
are exactly the positive denominators `q` for which `X / q = m`. -/
def roughSaiasDualQuotientInterval (X m : ℕ) : Finset ℕ :=
  Finset.Ioc (X / (m + 1)) (X / m)

@[simp]
theorem mem_roughSaiasDualQuotientInterval
    {X m q : ℕ} (hm : 0 < m) (hq : 0 < q) :
    q ∈ roughSaiasDualQuotientInterval X m ↔ X / q = m := by
  rw [roughSaiasDualQuotientInterval, Finset.mem_Ioc,
    ← natDiv_eq_iff_mem_hyperbolaIoc hq hm]





















/-! ## Adjacent edges: stable quotient fibres and quotient jumps -/

/-- Adjacent bases in the Abel variation range on which `m ↦ X / m`
does not jump. -/
def roughSaiasStableQuotientEdges (X y Z : ℕ) : Finset ℕ :=
  (Finset.Ioc y (Z - 1)).filter
    (fun m => X / (m + 1) = X / m)

/-- The complementary adjacent edges on which the hyperbola quotient
strictly changes. -/
def roughSaiasJumpQuotientEdges (X y Z : ℕ) : Finset ℕ :=
  (Finset.Ioc y (Z - 1)).filter
    (fun m => X / (m + 1) ≠ X / m)



/-- The stable adjacent edges carrying a fixed quotient `q`. -/
def roughSaiasStableQuotientEdgeBlock
    (X q y Z : ℕ) : Finset ℕ :=
  (roughSaiasStableQuotientEdges X y Z).filter (fun m => X / m = q)

@[simp]
theorem mem_roughSaiasStableQuotientEdges
    {X y Z m : ℕ} :
    m ∈ roughSaiasStableQuotientEdges X y Z ↔
      y < m ∧ m ≤ Z - 1 ∧ X / (m + 1) = X / m := by
  simp only [roughSaiasStableQuotientEdges, Finset.mem_filter,
    Finset.mem_Ioc]
  tauto

@[simp]
theorem mem_roughSaiasJumpQuotientEdges
    {X y Z m : ℕ} :
    m ∈ roughSaiasJumpQuotientEdges X y Z ↔
      y < m ∧ m ≤ Z - 1 ∧ X / (m + 1) ≠ X / m := by
  simp only [roughSaiasJumpQuotientEdges, Finset.mem_filter,
    Finset.mem_Ioc]
  tauto

@[simp]
theorem mem_roughSaiasStableQuotientEdgeBlock
    {X q y Z m : ℕ} :
    m ∈ roughSaiasStableQuotientEdgeBlock X q y Z ↔
      y < m ∧ m ≤ Z - 1 ∧ X / m = q ∧ X / (m + 1) = q := by
  simp only [roughSaiasStableQuotientEdgeBlock,
    roughSaiasStableQuotientEdges, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨⟨hym, hmZ⟩, hstable⟩, hq⟩
    exact ⟨hym, hmZ, hq, hstable.trans hq⟩
  · rintro ⟨hym, hmZ, hq, hnext⟩
    exact ⟨⟨⟨hym, hmZ⟩, hnext.trans hq.symm⟩, hq⟩

























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpVariation -/
section


/-!
# Sharp active-face variation of the base-free Saias kernel

On the active Dickman faces the apparently competing changes in the
Dickman coordinate and in `1 / log m` cancel algebraically.  If

`u_m(t) = (log q - log t) / log m`,

then

`rho'(u_m(t)) / log m = -rho (u_m(t) - 1) / (log q - log t)`.

The denominator on the right is independent of `m`.  Consequently, while
`t <= q / m` and the coordinates remain on the five constructed faces, the
scaled kernel is antitone as the base increases.  Its absolute consecutive
variation on an all-active finite block therefore telescopes exactly.  No
triangle inequality between the coordinate and coefficient changes is used.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

















































/-! ## The genuinely real hyperbola path inside natural cells -/

/-- The Dickman coordinate occurring when both the quotient `X / s` and
the smoothness base `s` move continuously along the real hyperbola. -/
noncomputable def roughSaiasFullyRealHyperbolaCoordinate
    (X : ℕ) (s t : ℝ) : ℝ :=
  (Real.log ((X : ℝ) / s) - Real.log t) / Real.log s

/-- The Dickman derivative divided by the moving base logarithm on the
genuinely real hyperbola path.  The fully real base-free kernel is this
quantity times the common nonnegative sawtooth factor
`fract(t) / t^2`. -/
noncomputable def roughSaiasFullyRealHyperbolaScaledDickmanKernel
    (X : ℕ) (s t : ℝ) : ℝ :=
  roughSaiasDickmanDerivative
      (roughSaiasFullyRealHyperbolaCoordinate X s t) /
    Real.log s

/-- A deterministic envelope for the oscillation from a point in the
natural cell `[m,m+1]` to its right endpoint.  On a fully active cell it is
the exact endpoint drop.  On the unique cell that can cross the support
boundary it is the uniform inverse-log envelope, and after the boundary it
vanishes. -/
noncomputable def roughSaiasFullyRealHyperbolaCellKernelOscillation
    (X m : ℕ) (t : ℝ) : ℝ :=
  if t ≤ (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) then
    roughSaiasFullyRealHyperbolaScaledDickmanKernel X (m : ℝ) t -
      roughSaiasFullyRealHyperbolaScaledDickmanKernel
        X ((m + 1 : ℕ) : ℝ) t
  else if t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) then
    1 / Real.log (m : ℝ)
  else 0























/-- The sawtooth-weighted version of the real-hyperbola cell envelope. -/
noncomputable def roughSaiasFullyRealHyperbolaCellFractionalOscillation
    (X m : ℕ) (t : ℝ) : ℝ :=
  (Int.fract t / t ^ (2 : ℕ)) *
    roughSaiasFullyRealHyperbolaCellKernelOscillation X m t

/-- The integrated sawtooth envelope on the common smallest cap. -/
noncomputable def roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
    (X a m : ℕ) : ℝ :=
  ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
    roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t



























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCorrectionTarget -/
section


/-!
# The sharp fully real correction target

The reverse defect splits directly into:

1. the ordinary Dickman continuous-integral versus prime-theta
   discrepancy, already closed by the existing Riemann and fourth-power
   PNT estimates; and
2. one fully real Saias correction integral versus its matching residual
   prime weight.

This is the minimal analytic target left after all exact base changes,
floor pairings, upper-selector cells, and standard Dickman estimates have
been discharged.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section







/-- The irreducible signed discrepancy on the unit cell `[m,m+1]`: its
paired natural quadrature remainder is kept together with the local
prime-minus-integer mass at the same right endpoint. -/
noncomputable def roughSaiasLocalNaturalPrimeCellDiscrepancy
    (X m : ℕ) : ℝ :=
  roughSaiasFullyRealNaturalBuchstabCellRemainder X m -
    roughSaiasNaturalQuotientThetaWeight X (m + 1) *
      (FriableAsymptotic.primeLogIncrement (m + 1) - 1)



























/-! ## Closing the lower fully-real quadrature -/

























































/-! ## Closed sharp defect and endpoint witnesses -/

/-- A concrete inverse-log-square constant for the fully closed reverse
normal-form defect.  The lower hyperbola block costs `40`; the remaining
integer-Abel and fourth-power theta terms cost
`3 + 243 * roughSaiasThetaFourthPowerConstant`. -/
noncomputable def roughSaiasSharpDefectConstant : ℝ :=
  43 + 243 * roughSaiasThetaFourthPowerConstant

/-- The only extra lower cutoff needed by the closed sharp defect is `3`. -/
noncomputable def roughSaiasSharpDefectCutoff : ℕ :=
  max 3 roughSaiasThetaFourthPowerCutoff







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpFixedHeadIntervalShift -/
section


/-!
# Sharp fixed-head interval shifts

The endpointwise fixed-head estimate loses one logarithm because it takes
absolute values before subtracting the two endpoints of an interval.  This
file retains that subtraction.  The Dickman main terms are first compared
at the interval level; the two residual increments are then bounded by the
already-proved sharp Saias endpoint approximation.

No new analytic predicate is introduced.  In particular, the only
approximation used below is
`roughSaiasSharpEndpointApproximationUpToFive`.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The interval-level Dickman cancellation -/

/-- The continuous translation defect before the natural quotient is
floored.  At a single endpoint it has size `X log(d)/(d log(y))`; its
difference on an interval has size proportional only to the interval
length. -/
noncomputable def roughFriableContinuousFixedDivisorDefect
    (X y d : ℕ) : ℝ :=
  (X : ℝ) / (d : ℝ) *
    (rho (FriableAsymptotic.dickmanU X y -
        Real.log (d : ℝ) / Real.log (y : ℝ)) -
      rho (FriableAsymptotic.dickmanU X y))







/-! ## Adding the two residual increments -/

/-- Exact budget for an interval fixed-divisor shift.  The first term is
the interval Dickman cancellation above.  The second is the residual
increment on the divided interval, and the third is `1/d` times the
residual increment on the original interval. -/
noncomputable def roughSaiasIntervalFixedDivisorShiftBudget
    (eta : ℕ → ℝ) (A B y d : ℕ) : ℝ :=
  6 + ((B - A : ℕ) : ℝ) *
      (Real.log (d : ℝ) + 2) /
        ((d : ℝ) * Real.log (y : ℝ)) +
    roughSaiasPairTransitionBudget eta (A / d) (B / d) y +
    roughSaiasPairTransitionBudget eta A B y / (d : ℝ)



/-! ## The closed inverse-log-square specialization -/

/-- A convenient explicit upper budget after substituting the closed sharp
endpoint rate.  Its four summands are respectively the quotient-floor
constant, the quotient-length floor constant, the main interval
translation, and the two sharp endpoint envelopes. -/
noncomputable def roughSaiasSharpIntervalFixedDivisorBudget
    (A B y d : ℕ) : ℝ :=
  6 + 5 / Real.log (y : ℝ) +
    ((B - A : ℕ) : ℝ) *
      (Real.log (d : ℝ) + 12) /
        ((d : ℝ) * Real.log (y : ℝ)) +
    20 * roughSaiasSharpDefectConstant *
      ((A : ℝ) + (B : ℝ)) /
        ((d : ℝ) * Real.log (y : ℝ) ^ 2)





/-! ## Physical blocks and the finite head -/











/-- All-row sharp fixed-head allowance.  Large rows use the interval
cancellation budget; when `d` exceeds the lower endpoint, the whole row is
below `2d` and the fixed constant branch applies. -/
noncomputable def roughCanonicalSharpFixedHeadShiftBudgetAllRows
    (W n h K y : ℕ) (alpha beta L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) : ℝ :=
  ∑ d ∈ (roughHeadModulus W).divisors,
    |(ArithmeticFunction.moebius d : ℝ)| *
      if d ≤ n / row.1 then
        (|alpha| *
            roughSaiasSharpIntervalFixedDivisorBudget
              ((2 * n - K * h) / row.1) ((2 * n) / row.1) y d +
          |beta / L| *
            roughSaiasSharpIntervalFixedDivisorBudget
              (n / row.1) ((2 * n - K * h) / row.1) y d)
      else
        4 * (|alpha| + |beta / L|)





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCanonicalRowPaperScale -/
section


/-!
# Canonical sharp Saias row-scale geometry

This file specializes the closed sharp endpoint and fixed-head estimates to
the paper's literal balanced raw point.  The high-block multiplicity is
written as `K0 + 1`, so its positivity is built into the data rather than
assumed separately.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Uniform control of the literal balanced coefficient -/







/-! ## Fixed constants for the three row ledgers -/

/-- The uniform bound for the literal balanced coefficient when the high
block multiplicity is written as `K0 + 1`. -/
noncomputable def roughBalancedAlphaConstant
    (W K0 : ℕ) (c beta : ℝ) : ℝ :=
  1 / (((K0 + 1 : ℕ) : ℝ) * roughHeadDensity W) +
    |beta| / (((K0 + 1 : ℕ) : ℝ) * c)



/-- A fixed coefficient paying the Dickman displacement ledger and its
four quotient-floor errors. -/
noncomputable def roughCanonicalSharpMainRowScaleConstant
    (W K0 : ℕ) (c beta : ℝ) : ℝ :=
  (30 * c + 15) +
    (roughBalancedAlphaConstant W K0 c beta + |beta|) *
      (10 * (((K0 + 1 : ℕ) : ℝ)) * c + 5) +
    10 * |beta| +
    (2 + 2 * roughBalancedAlphaConstant W K0 c beta +
      2 * |beta|)

/-- A fixed coefficient paying the three weighted sharp Saias pair
budgets.  The broad pair already carries its defining `beta/L` factor. -/
noncomputable def roughCanonicalSharpTransitionRowScaleConstant
    (W K0 : ℕ) (c beta : ℝ) : ℝ :=
  (3000 * roughSaiasSharpDefectConstant + 50 * c + 25) +
    roughBalancedAlphaConstant W K0 c beta *
      (1500 * roughSaiasSharpDefectConstant +
        50 * (((K0 + 1 : ℕ) : ℝ)) * c + 25) +
    |beta| * (1000 * roughSaiasSharpDefectConstant + 75)

/-- The coefficient attached to one fixed head divisor.  It pays both
sharp interval branches as well as the bounded small-row branch. -/
noncomputable def roughCanonicalSharpHeadDivisorRowScaleConstant
    (W K0 d : ℕ) (c beta : ℝ) : ℝ :=
  roughBalancedAlphaConstant W K0 c beta *
      (31 +
        (Real.log (d : ℝ) + 12) / (d : ℝ) *
          (10 * (((K0 + 1 : ℕ) : ℝ)) * c + 5) +
        3000 * roughSaiasSharpDefectConstant / (d : ℝ)) +
    |beta| *
      (31 + 10 * (Real.log (d : ℝ) + 12) / (d : ℝ) +
        2000 * roughSaiasSharpDefectConstant / (d : ℝ)) +
    4 * (roughBalancedAlphaConstant W K0 c beta + |beta|)

/-- The fixed-head divisor sum is finite before `n` is chosen, hence gives
one honest constant depending only on the fixed paper parameters. -/
noncomputable def roughCanonicalSharpHeadRowScaleConstant
    (W K0 : ℕ) (c beta : ℝ) : ℝ :=
  ∑ d ∈ (roughHeadModulus W).divisors,
    |(ArithmeticFunction.moebius d : ℝ)| *
      roughCanonicalSharpHeadDivisorRowScaleConstant W K0 d c beta

/-- One fixed constant which simultaneously dominates the main,
transition, and fixed-head row ledgers. -/
noncomputable def roughCanonicalSharpUnifiedRowScaleConstant
    (W K0 : ℕ) (c beta : ℝ) : ℝ :=
  roughCanonicalSharpMainRowScaleConstant W K0 c beta +
    roughCanonicalSharpTransitionRowScaleConstant W K0 c beta +
    roughCanonicalSharpHeadRowScaleConstant W K0 c beta

/-! ## Quotient and logarithmic geometry -/





























/-! ## The balanced Dickman main ledger -/





/-! ## The weighted sharp Saias transition ledger -/



/-! ## Absorption of the sharp fixed-head divisor sum -/



/-! ## One unified canonical raw-row allowance -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure -/
section


/-!
# Canonical nonsmooth endpoint-slack closure

This module connects the sharp balanced raw-row estimate to the literal
guarded constant-pool correction used at the actual Proposition 8.7
endpoint.

There are two finite guard estimates.  The sharp one assumes the usual
raw-point box and proves that passing through all numerical guards changes
one active row discrepancy by at most `2`.  The assumption-free one uses
the already proved uniform absolute bound for the balanced coefficient and
gives a fixed (slightly larger) numerator constant.  The latter is the
version used in the eventual theorem, so no unproved eventual feasibility
of `roughHeadBalancedAlpha` is hidden in the endpoint-slack conclusion.

The final bounds use the paper split

`beta = betaProt + betaAct`, `0 < betaAct`, `sigma <= betaProt`.

Thus the lower nonsmooth margin has the fixed strict reserve `betaAct/L`.
The upper margin follows once `L` exceeds the fixed sum of the parameters.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.Scale
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Filter Topology
open scoped BigOperators

noncomputable section

namespace BankPaperRealization

/-! ## Active rows contain no fixed exceptional factor -/









/-! ## The sharp finite `+2` guard numerator -/



/-! ## An assumption-free fixed guard numerator -/

/-- Uniform absolute bound used for every balanced raw coordinate after
writing the high multiplicity as `K0+1`. -/
def roughCanonicalBalancedRawWeightGuardBound
    (W K0 : Nat) (c beta : Real) : Real :=
  roughBalancedAlphaConstant W K0 c beta + |beta|





/-- Fixed numerator constant for the assumption-free guard estimate. -/
def roughCanonicalBalancedGuardNumeratorConstant
    (W K0 : Nat) (c beta : Real) : Real :=
  1 + 3 * roughCanonicalBalancedRawWeightGuardBound W K0 c beta





end BankPaperRealization

/-! ## Eventual sharp raw-row estimate on every active canonical row -/









namespace BankPaperRealization

/-! ## From the raw numerator to the guarded correction density -/











/-! ## The eventual paper beta/sigma nonsmooth bounds -/

/-- Exact nonsmooth-bounds package consumed by the actual endpoint-slack
producer, specialized to the balanced raw level and the paper split
`betaProt + betaAct`. -/
def RoughCanonicalBalancedNonsmoothBounds
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K0 : Nat)
    (betaProt betaAct sigma : Real) : Prop :=
  forall label,
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
      sigma / L n +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W (K0 + 1) label
            (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              (betaProt + betaAct) (L n))
            (betaProt + betaAct) (L n)| <=
        (betaProt + betaAct) / L n ∧
      (betaProt + betaAct) / L n +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W (K0 + 1) label
            (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              (betaProt + betaAct) (L n))
            (betaProt + betaAct) (L n)| <=
        1 - sigma / L n











end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalPostHfitSlackConnector -/
section


/-!
# Exact Post-Hfit endpoint/slack connector

This file joins the three finite interfaces immediately before the remaining
Section 9 tangent-flow and traffic assembly:

* the global corrected source and its two-zero-head-cell structured placement;
* the split-seed Post-Hfit endpoint handoff; and
* the balanced nonsmooth density bounds used by the actual endpoint-slack
  theorem.

The placement seed is the two-cell rebalance of `oldSeed`.  The actual bridge
measure, marked target, frozen weights, P87 path, and endpoint all retain the
single input `activeSeed`.  The returned package records the exact path and
defines `endpoint` to be the push-forward of that same path and active seed.

This connector deliberately stops at
`BankPaperCanonicalGuardedEndpointSlackConstruction`.  It does not assume or
conclude a tangent flow, collision census, clean-list traffic estimate, or a
terminal Section 9 output.  Those obligations remain visible downstream.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Canonical balanced source and structured preselector -/

/-- The balanced postcharge parameter used at the actual rough level
`K0 + 1`. -/
def bankPaperCanonicalPostHfitBalancedAlpha
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (c : Real) (K0 : Nat)
    (betaProt betaAct : Real) : Real :=
  roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
    (upperTailLength c B.sampleData.n) (K0 + 1)
    (betaProt + betaAct) B.L





/-! ## Exact finite output package -/



/-! ## Production connector -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTopFrozenSourceConnector -/
section


/-!
# The frozen smooth-top source at the Section 8 initial stage

The paper's smooth-row initialization has three distinct layers:

* the `alpha`-weighted top block;
* the protected `betaProt / L` broad layer; and
* the structured active seed of total mass `qTilde`.

The older global corrected source retained the latter two layers on the
guarded broad pool, but its complete-label-one branch contained only the
ambient active seed.  In particular it did not contain the top block.

This connector defines a separate, finite `qTilde`-stage source which adds
that missing top layer.  On the guarded complete smooth row it is pointwise
equal to the literal raw weight with broad parameter `betaProt`, plus the
ambient old seed.  Consequently, when the old seed has total mass equal to
the guarded `betaAct` base mass, its whole guarded smooth-row sum is exactly
the balanced raw sum with broad parameter `betaProt + betaAct`.

No asymptotic estimate, post-height-fit displacement, or Section 9 source
state is asserted here.  The identities are finite and exact.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The missing smooth top layer -/

/-- The paper's frozen smooth top component: the literal raw weight with
zero broad coefficient.  The logarithmic scale is retained as an argument
so the definition can be compared directly with the existing raw weight. -/
def bankPaperCanonicalSmoothTopWeight
    (W n h K : Nat) (alpha logScale : Real) (a : Nat) : Real :=
  roughHeadCompatibleRawWeight W n h K alpha 0 logScale a

/-- On complete label one, add the frozen smooth top layer to the ambient
old seed.  Exceptional nonsmooth rows vanish, while active nonexceptional
rows keep the existing guarded postcharge corrected weight. -/
def bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real) (a : Nat) : Real := by
  classical
  exact
    if completeRoughLabel (yNat B.sampleData.n) a = 1 then
      bankPaperCanonicalSmoothTopWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha B.L a +
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a
    else
      if RoughCanonicalExceptionalLabel B.sampleData.n deltaStar
          (completeRoughLabel (yNat B.sampleData.n) a) then
        0
      else
        R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar B.sampleData.W K
            (completeRoughLabel (yNat B.sampleData.n) a)
              alpha beta B.L a

/-- The protected two-zero-cell source, with the missing top component
restored on the remainder of complete label one. -/
def bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real) : Nat -> Real :=
  bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
    B R certificate deltaStar betaProt oldSeed
      (bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
        B R certificate deltaStar alpha beta oldSeed)

/-! ## Pointwise smooth-row identification -/

/-- Away from the guarded head-free broad pool, the top-only weight equals
the raw weight with any broad coefficient on the guarded smooth row.

Indeed, a surviving smooth-row coordinate is in the high or broad block.
In the broad block, head freedom would put it in the guarded broad pool, so
outside that pool it has zero raw weight. -/
theorem bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha beta : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hnotPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalSmoothTopWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha B.L a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha beta B.L a := by
  have haData := mem_completeRoughRowFiber.mp ha
  have haRaw :
      a ∈ roughRawCandidateSet B.sampleData.n
        (upperTailLength c B.sampleData.n) K :=
    R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
      certificate deltaStar K haData.1
  have haSurvives :
      a ∉ R.roughCanonicalGuardSet certificate deltaStar := by
    have hmem := haData.1
    rw [roughCanonicalGuardedCandidateSet, Finset.mem_sdiff] at hmem
    exact hmem.2
  rw [roughRawCandidateSet, Finset.mem_union] at haRaw
  rcases haRaw with haHigh | haBroad
  · have hnotBroad :
        a ∉ roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K := by
      intro haBroad
      exact Finset.disjoint_left.mp
        (roughHighLowerBlock_disjoint_roughBroadLowerBlock
          B.sampleData.n (upperTailLength c B.sampleData.n) K)
        haHigh haBroad
    simp [bankPaperCanonicalSmoothTopWeight,
      roughHeadCompatibleRawWeight, roughFiniteIndicator, hnotBroad]
  · by_cases hcop :
      Nat.Coprime a (roughHeadModulus B.sampleData.W)
    · have haRawBroad :
          a ∈ roughCanonicalBroadCorrectionPool B.sampleData.W
            B.sampleData.n (upperTailLength c B.sampleData.n) K
              (yNat B.sampleData.n) 1 := by
        apply mem_completeRoughRowFiber.mpr
        exact
          ⟨mem_roughHeadFree.mpr ⟨haBroad, hcop⟩, haData.2⟩
      exfalso
      apply hnotPool
      exact Finset.mem_sdiff.mpr ⟨haRawBroad, haSurvives⟩
    · simp [bankPaperCanonicalSmoothTopWeight,
        roughHeadCompatibleRawWeight, hcop]

/-- Exact pointwise label-one bridge: the restored source is the frozen
raw `alpha + betaProt / L` layer plus the ambient old active seed. -/
@[simp] theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
  by_cases hpool :
      a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1
  · have hraw :=
      roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
        (alpha := alpha) (beta := betaProt) (L := B.L)
        (R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
          certificate deltaStar B.sampleData.W K 1 hpool)
    simpa [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
      bankPaperCanonicalTwoZeroHeadCellSourceSelector, hpool] using
        congrArg
          (fun x : Real =>
            x + bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a)
          hraw.symm
  · have hlabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp ha).2
    have htop :=
      bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
        (B := B) R certificate (alpha := alpha) (beta := betaProt)
          ha hpool
    simpa [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
      bankPaperCanonicalTwoZeroHeadCellSourceSelector, hpool,
      bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
      hlabel] using
        congrArg
          (fun x : Real =>
            x + bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a)
          htop

/-! ## Exact guarded-row mass identities -/











end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightTopFrozenInitialMassConnector -/
section


/-!
# Initial selector mass from the frozen-top smooth-row bridge

This connector is the asymptotic integration boundary for the separate
`qTilde`-stage source constructed in
`BankPaperCanonicalSectionEightTopFrozenSourceConnector`.

The family-facing premise below is an exact construction equation:
the initial selector has the same guarded label-one row sum as the balanced
literal raw selector.  Together with the existing exact nonsmooth-row state,
the charged row ledger reduces the whole selector-mass error to:

* the balanced raw label-one discrepancy;
* the two charged label-one multiplicities; and
* the balanced raw mass deleted by the numerical guard.

The first term is handled by the sharp Saias row theorem.  Fixed exceptional
factors and bank bases have zero label-one multiplicity in the paper range.
The remaining deleted row is contained in the promoted smooth residual
anchors, hence has cardinality at most `yNat`; the existing uniform balanced
raw-weight bound then absorbs it into `secondOrderScale / L`.

No final-selector quota, height displacement, or Section 9 source state is
used here.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The balanced raw selector used by the initial-mass interface -/

/-- The literal balanced raw weight with high multiplicity `K0 + 1`. -/
def bankPaperCanonicalBalancedRawWeight
    (W K0 : Nat) (c beta : Real) (n a : Nat) : Real :=
  roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
    (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
      beta (L n))
    beta (L n) a

/-! ## The two charged smooth-row multiplicities -/





/-! ## Full label-one guard deletion -/









/-! ## Paper-scale bounds for the smooth row -/











/-! ## Exact construction boundary and the charged mass ledger -/

/-- The exact finite witness consumed by the initial-mass theorem.

It identifies the three observable finite sets with one paper realization,
installs the already-constructed charged nonsmooth rows, and records only
the one additional fact needed on the smooth row: the initial selector and
the balanced literal raw selector have the same guarded label-one mass. -/
def BankPaperCanonicalTopFrozenBalancedInitialRealization
    (depth W K0 n : Nat) (c deltaStar beta : Real)
    (fixed bankBase candidates : Finset Nat)
    (initialSelector : Nat -> Real) : Prop :=
  ∃ Rn : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)),
  ∃ certn : GuardedCentralAnchorCertificate c depth n
      Rn.anchorGuardLeftCore Rn.anchorGuardRightCore
      (Rn.centralChangedMarkers depth),
    fixed = Rn.paperFixedExceptionalFactors deltaStar ∧
    bankBase = Rn.prechargeBaseState ∧
    candidates =
      Rn.roughCanonicalGuardedCandidateSet certn deltaStar (K0 + 1) ∧
    BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K0 + 1) Rn certn deltaStar initialSelector ∧
    (∑ a ∈ Rn.roughCanonicalGuardedRow certn deltaStar
        (K0 + 1) 1, initialSelector a) =
      ∑ a ∈ Rn.roughCanonicalGuardedRow certn deltaStar
        (K0 + 1) 1,
          bankPaperCanonicalBalancedRawWeight W K0 c beta n a



/-! ## Asymptotic initial-selector mass theorem -/



/-! ## The concrete WithTop/scaled-seed constructor -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateConnector -/
section


/-!
# Nearest-integer source state for the frozen-top selector

The finite frozen-top source at mass `qTilde` has the paper's literal
smooth-row mass, but that mass need not be an integer.  The initialization
step replaces `qTilde` by

`q0 = nearestInteger(mFrozen + qTilde) - mFrozen`.

This connector proves the exact part of that handoff:

* changing the scaled seed from `qTilde` to `q0` changes no nonsmooth row;
* the new smooth-row total is the declared nearest integer;
* the charged nonsmooth-row equations therefore imply integrality of every
  complete rough row; and
* feasibility and exact target agreement outside the tangent prime band
  then package the result as `BankPaperCanonicalSelectorSourceState`.

The last two properties are retained as explicit premises.  They are not
consequences of row-mass rounding: feasibility is pointwise, while target
agreement is a prime-valuation identity.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The exact frozen mass and nearest-integer source -/

/-- The part of the guarded smooth-row mass which is unchanged when the
active seed mass is replaced by its nearest-integer normalization. -/
def bankPaperCanonicalTopFrozenSmoothFrozenMass
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha : Real) : Real :=
  ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
    roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
      (upperTailLength c B.sampleData.n) K alpha betaProt B.L a

/-- The paper's normalized active mass `q0`, specialized to the literal
frozen-top guarded smooth row. -/
def bankPaperCanonicalTopFrozenRoundedActiveMass
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha qTilde : Real) : Real :=
  bankPaperCanonicalSmoothInitialActiveMass
    (bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
      B R certificate deltaStar betaProt alpha)
    qTilde

/-- Half of the nearest-integer mass correction.  The paper puts one copy
in each physical realization of the zero head cell, so no nonzero head
moment is changed. -/
def bankPaperCanonicalTopFrozenNearestIntegerCellMass
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha qTilde : Real) : Real :=
  (bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
      B R certificate deltaStar betaProt alpha qTilde - qTilde) / 2



/-- The actual nearest-integer seed.  It starts from the literal
`qTilde`-scaled barycentric seed and changes only the two zero-head cells. -/
def bankPaperCanonicalTopFrozenRoundedActiveSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha qTilde : Real) :
    B.sampleData.Sample -> Real :=
  bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
    (bankPaperCanonicalScaledActiveSeed T qTilde)
    (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
      B R certificate deltaStar betaProt alpha qTilde)
    (bankPaperCanonicalTopFrozenNearestIntegerCellMass (K := K)
      B R certificate deltaStar betaProt alpha qTilde)

/-- The frozen-top source after replacing the literal post-guard active
mass `qTilde` by the two-zero-cell nearest-integer correction. -/
def bankPaperCanonicalTopFrozenRoundedSourceSelector
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real) : Nat -> Real :=
  bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
    B R certificate deltaStar betaProt alpha betaTotal
      (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
        B R certificate T deltaStar betaProt alpha qTilde)

/-! ## Nonsmooth rows are independent of the active seed -/









/-! ## Exact smooth and nonsmooth row ledgers -/











/-! ## Exact feasibility transport through the two zero cells -/



/-! ## Complete-row integrality and the source-state handoff -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalArbitrarySourcePostHfitConnector -/
section


/-!
# Post-Hfit production from an arbitrary verified source

The original Post-Hfit connector fixes
`bankPaperCanonicalPostHfitGlobalSourceSelector` in both its placement and
its output package.  This file separates the part of that construction which
only needs a verified selector source state from the identities special to
that old source.

For an arbitrary `sourceSelector`, the exact additional inputs are:

* the signed whole-smooth-row prebridge ledger for `placementSeed`;
* pointwise feasibility of the resulting structured placement; and
* the nonsmooth-row identification of the source.

The source state supplies row integrality and exact agreement outside the
medium-prime band.  The prebridge theorem transports those two fields to the
structured placement.  Everything after that point--Proposition 8.7, the
split-seed endpoint, the rounded tangent input, and endpoint slack--is
source-agnostic.

The final section specializes this producer to the frozen-top
nearest-integer selector.  Its nonsmooth-row identification is proved here,
so the specialization does not route through the older no-top global source.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Source-parameterized preselector and package -/

/-- The structured Post-Hfit preselector built from an arbitrary base
selector and an independently supplied placement seed. -/
def bankPaperCanonicalPostHfitStructuredPreSelectorOfSource
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real) : Nat -> Real :=
  bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
    B R certificate deltaStar betaProt sourceSelector placementSeed

/-- The complete finite Post-Hfit output for an arbitrary verified source.

Unlike `BankPaperCanonicalPostHfitGuardedSlackPackage`, this package does
not hide a particular source definition or a particular two-cell placement
seed.  It records those two objects as parameters. -/
def BankPaperCanonicalPostHfitGuardedSlackPackageOfSource
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    (deltaStar betaProt alpha beta sigma : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    (radius : NNReal) (Cpost : Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (quota : Int) (path : Real -> B.ParamSpace)
    (endpoint : Nat -> Real) : Prop :=
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  let preSelector :=
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
      B R certificate deltaStar betaProt sourceSelector placementSeed
  let markedTarget :=
    bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
      candidates preSelector activeSeed
  let Delta := fun j => B.markedBandResidual markedTarget 0 j
  BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt
        sourceSelector placementSeed ∧
    B.HasPaperProposition87Conclusion
      Delta radius markedTarget B.q Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight B.sampleData candidates
        preSelector activeSeed)
      quota ∧
    B.IsPaperProposition87Path
      Delta radius markedTarget B.q Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight B.sampleData candidates
        preSelector activeSeed)
      quota path ∧
    endpoint =
      bankPaperCanonicalActualP87EndpointSelector B candidates
        preSelector activeSeed path ∧
    BankPaperCanonicalRoundedSelectorTangentInput R certificate fixed
      candidates B.partition.band cellIndex
      (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
      (tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
        B.partition.band cellIndex)
      endpoint ∧
    R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar B.sampleData.W K alpha beta B.L sigma endpoint

/-! ## Generic slack inputs -/





/-! ## Arbitrary-source producer -/



/-! ## Frozen-top rounded specialization -/

/-- The source-parameterized preselector specialized to the exact
nearest-integer frozen-top source. -/
def bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real)
    (placementSeed : B.sampleData.Sample -> Real) : Nat -> Real :=
  bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
    B R certificate deltaStar betaProt
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha beta qTilde)
      placementSeed

/-- Frozen-top specialization of the arbitrary-source output package. -/
def BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde sigma : Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    (radius : NNReal) (Cpost : Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (quota : Int) (path : Real -> B.ParamSpace)
    (endpoint : Nat -> Real) : Prop :=
  BankPaperCanonicalPostHfitGuardedSlackPackageOfSource (K := K)
    B R certificate fixed deltaStar betaProt alpha beta sigma
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha beta qTilde)
      placementSeed activeSeed radius Cpost cellIndex quota path endpoint





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPlacedMeasureConnector -/
section


/-!
# The post-height baseline under the literal frozen-top placement

The nearest-integer source, the height-changing placement, and the final
barycentric baseline are three different finite objects in the paper.  In
particular, the final baseline has literal mass

`q_n = q0 - d`

and need not equal the two-zero-cell seed used to change the integral row
height.

This file installs the scaled seed of
`bankPaperCanonicalSectionNinePostHeightTarget` directly as the active
layer of the literal frozen-top structured preselector.  The protected
layer then gives pointwise domination, hence the full
`BankPaperCanonicalActualActiveMeasureConstructor` at mass `q0-d`.

The optional feasibility theorem below isolates the remaining upper-bound
issue as the paper's finite geometry: an `O(n / log n)` bound for `q_n`,
a linear lower bound for every structured cell cardinality, and one large
`log n` inequality.  No abstract redistribution contract or equality with
the earlier rounding seed is assumed.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

namespace BankPaperRealization

/-! ## Literal post-height placed preselector -/

/-- The literal frozen-top source with the final post-height barycentric
seed installed as its structured active layer. -/
def bankPaperCanonicalSectionNinePostHeightPlacedPreSelector
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real) : Nat → Real :=
  bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector (K := K)
    B R certificate Tsource deltaStar betaProt alpha beta qTilde
      (bankPaperCanonicalSectionNinePostHeightActiveSeed
        B I hlo hhi H)



/-! ## Exact pointwise domination and active measure -/





/-! ## The finite capacity supplied by post-height geometry -/





/-! ## Actual measure and full selector feasibility -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedGuardResidual -/
section


/-!
# Signed exceptional and guard residual ledger

This module gives literal names to the two signed terms in the final rough
residual identity.  They are intentionally separate from the nonnegative
fixed-factor charge used for divisibility.

`roughCanonicalSignedExceptionalResidual` is the exceptional-row portion of
the raw upper-minus-lower comparison.  The order of its two finite sums is
not replaced by a sum of absolute values.  `roughCanonicalAggregateGuardResidual`
is the paper's three-term guard difference: restored raw weights deleted in
nonexceptional rows, restored exceptional donors, and the negative bank-base
charge.

The exact four-term sign convention and its triangle reduction are proved at
the end.  The aggregate guard term is bounded and absorbed unconditionally
from the literal finite census, and the correction-pool valuation census is
also closed by the global Legendre prefix bound.  The genuinely signed
exceptional estimate and the uniform correction-density estimate remain
exposed as named propositions rather than being confused with the already
proved nonnegative exceptional charge bound.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Elementary finite valuation envelopes -/







/-! ## Literal signed exceptional term -/

/-- Raw lower candidates in exceptional complete rough rows. -/
def roughCanonicalExceptionalRawLowerSet
    (n h K : Nat) (deltaStar : Real) : Finset Nat := by
  classical
  exact (roughRawCandidateSet n h K).filter fun a =>
    RoughCanonicalExceptionalLabel n deltaStar
      (completeRoughLabel (yNat n) a)

@[simp]
theorem mem_roughCanonicalExceptionalRawLowerSet
    {n h K a : Nat} {deltaStar : Real} :
    a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar ↔
      a ∈ roughRawCandidateSet n h K ∧
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) := by
  classical
  simp only [roughCanonicalExceptionalRawLowerSet, Finset.mem_filter]

/-- The paper's signed exceptional-row discrepancy
`sum_{a in E_exc} v_p(a) - sum_{a in H_exc} x_raw(a) v_p(a)`.

No absolute value is taken inside either sum. -/
def roughCanonicalSignedExceptionalResidual
    (n h K : Nat) (deltaStar : Real)
    (rawWeight : Nat -> Real) (p : Nat) : Real :=
  (∑ a ∈ paperExceptionalUpperFactors n h deltaStar,
      (a.factorization p : Real)) -
    ∑ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
      rawWeight a * (a.factorization p : Real)





/-! ## Literal aggregate guard difference -/

/-- Raw lower coordinates deleted by the numerical guards in
nonexceptional rows.  The smooth row is included whenever it is
nonexceptional, as in the paper's set `D_ne`. -/
def roughCanonicalNonexceptionalGuardDeletedSet
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) : Finset Nat := by
  classical
  exact ((roughRawCandidateSet n h K) ∩
      R.roughCanonicalGuardSet certificate deltaStar).filter fun a =>
    ¬ RoughCanonicalExceptionalLabel n deltaStar
      (completeRoughLabel (yNat n) a)

@[simp]
theorem mem_roughCanonicalNonexceptionalGuardDeletedSet
    {c : Real} {depth n h K a : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) :
    a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar K ↔
      a ∈ roughRawCandidateSet n h K ∧
        a ∈ R.roughCanonicalGuardSet certificate deltaStar ∧
        ¬ RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) := by
  classical
  simp only [roughCanonicalNonexceptionalGuardDeletedSet,
    Finset.mem_filter, Finset.mem_inter, and_assoc]

/-- Designated donors whose complete rough row is exceptional. -/
def roughCanonicalExceptionalDonorSet
    {n h : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) : Finset Nat := by
  classical
  exact R.prechargeDonorSet.filter fun a =>
    RoughCanonicalExceptionalLabel n deltaStar
      (completeRoughLabel (yNat n) a)

@[simp]
theorem mem_roughCanonicalExceptionalDonorSet
    {n h a : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : Real} :
    a ∈ R.roughCanonicalExceptionalDonorSet deltaStar ↔
      a ∈ R.prechargeDonorSet ∧
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) := by
  classical
  simp only [roughCanonicalExceptionalDonorSet, Finset.mem_filter]





/-- The complete signed guard difference from the paper:

* restore raw weight on lower coordinates deleted outside exceptional rows;
* restore donor terms which were already present in the signed exceptional
  discrepancy;
* subtract the bank-base tokens which replace those donors.
-/
def roughCanonicalAggregateGuardResidual
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) (rawWeight : Nat -> Real)
    (p : Nat) : Real :=
  (∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar K,
      rawWeight a * (a.factorization p : Real)) +
    (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
      (a.factorization p : Real)) -
    ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)



/-! ## A uniform finite guard-profile bound -/





/-- A realization-independent majorant for the whole literal guard
difference at one medium prime. -/
def roughCanonicalAggregateGuardResidualMajorant (n : Nat) : Real :=
  (2 + 4 * (bankPaperAnchorMarkerBudget n : Real)) *
    (Nat.log 2 (3 * n) : Real)





/-! ## Uniform absorption of the guard majorant -/

/-- The normalized real model needed after multiplying the guard error by
the largest permitted prime and by the extra logarithm in the strict rate. -/
def bankPaperGuardCubicNormalizedCost (n : Nat) : Real :=
  y n ^ 3 * L n ^ 2 / secondOrderScale n













/-! ## Literal aggregate nonsmooth row correction -/

/-- The attained raw complete-rough labels on which the paper applies its
constant-pool correction: nonsmooth and nonexceptional, with the real
cutoff convention left unchanged. -/
def roughCanonicalActiveRawCorrectionLabels
    (n h K : Nat) (deltaStar : Real) : Finset Nat := by
  classical
  exact
    (completeRoughLabelSet (yNat n) (roughRawCandidateSet n h K)).filter
      (RoughCanonicalActiveNonexceptionalLabel n deltaStar)

@[simp]
theorem mem_roughCanonicalActiveRawCorrectionLabels
    {n h K label : Nat} {deltaStar : Real} :
    label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar ↔
      label ∈ completeRoughLabelSet (yNat n)
        (roughRawCandidateSet n h K) ∧
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label := by
  classical
  simp only [roughCanonicalActiveRawCorrectionLabels, Finset.mem_filter]

/-- The signed constant added to every broad-pool coordinate in one raw
complete-rough row. -/
def roughCanonicalRawCorrectionDensityAtLabel
    (W n h K : Nat) (alpha beta logScale : Real)
    (label : Nat) : Real :=
  bankPaperConstantPoolCorrectionDensity
    (completeRoughRowFiber (yNat n) (roughRawCandidateSet n h K) label)
    (roughCanonicalBroadCorrectionPool W n h K (yNat n) label)
    (roughHeadCompatibleRawWeight W n h K alpha beta logScale)
    (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real)

/-- The paper's full signed row-correction contribution at one prime,
summed only after every active physical row has retained its sign. -/
def roughCanonicalAggregateRawRowCorrection
    (W n h K : Nat) (deltaStar alpha beta logScale : Real)
    (p : Nat) : Real :=
  ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
    ∑ a ∈ roughCanonicalBroadCorrectionPool W n h K (yNat n) label,
      roughCanonicalRawCorrectionDensityAtLabel
          W n h K alpha beta logScale label *
        (a.factorization p : Real)













/-! ## Exact final sign ledger and quantitative reduction -/

/-- The exact sign convention of the completed rough residual. -/
def roughCanonicalCompleteSignedResidual
    (rawResidual signedExceptional rowCorrection aggregateGuard : Real) :
    Real :=
  rawResidual - signedExceptional - rowCorrection + aggregateGuard





/-- The missing signed exceptional estimate, stated independently of the
nonnegative factor charge. -/
def RoughCanonicalSignedExceptionalResidualBound
    (n h K : Nat) (deltaStar : Real) (rawWeight : Nat -> Real)
    (p : Nat) (bound : Real) : Prop :=
  abs (roughCanonicalSignedExceptionalResidual n h K deltaStar
    rawWeight p) <= bound

/-- A transparent wrapper for a quantitative aggregate guard-profile
estimate.  Unlike the signed-exceptional wrapper, its paper-scale bound is
proved below from the literal guard census. -/
def RoughCanonicalAggregateGuardResidualBound
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) (rawWeight : Nat -> Real)
    (p : Nat) (bound : Real) : Prop :=
  abs (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
    rawWeight p) <= bound

/-- Public predicate for an exact aggregate row-correction estimate. -/
def RoughCanonicalAggregateRawRowCorrectionBound
    (W n h K : Nat) (deltaStar alpha beta logScale : Real)
    (p : Nat) (bound : Real) : Prop :=
  abs (roughCanonicalAggregateRawRowCorrection W n h K deltaStar
    alpha beta logScale p) ≤ bound

/-- The smallest remaining analytic row-correction input: a uniform bound
for the literal constant correction density on every active attained row.
By `roughCanonicalRawCorrectionDensityAtLabel_eq_quotaError_div`, this is
exactly a uniform quota-error-over-pool-cardinality estimate. -/
def RoughCanonicalUniformRawRowCorrectionDensityBound
    (W n h K : Nat) (deltaStar alpha beta logScale densityBound : Real) :
    Prop :=
  ∀ label ∈ roughCanonicalActiveRawCorrectionLabels n h K deltaStar,
    abs (roughCanonicalRawCorrectionDensityAtLabel
      W n h K alpha beta logScale label) ≤ densityBound















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedResidualSelectorIdentification -/
section


/-!
# Exact selector identification for the four-term signed rough residual

The quantitative signed-residual file defines the four scalar terms and
proves their bounds, while the selector handoff defines the literal
target-minus-selector valuation deficit.  This file isolates the finite
identity still needed to connect them.

There are two independent finite ledgers:

* the target ledger expands the charged selector target as the raw upper
  valuation, less fixed exceptional factors and the bank base, with
  exceptional donors restored;
* the selector ledger expands the concrete guarded source as the raw lower
  valuation, less exceptional and nonexceptional deleted coordinates, plus
  the aggregate row correction.

The target ledger is proved below in the medium-prime range from the existing
charge divisibility.  The selector ledger remains a named source-level input:
the current implementation uses guarded postcharge corrections, whereas the
available aggregate correction scalar is defined using raw rows and raw
broad pools, and no global valuation reindexing theorem identifies them.

Once the two ledgers are available, the exact four signs follow by ring
algebra.  A final transport theorem records the additional, already-defined
valuation moment introduced by structured smooth placement.  Thus the
remaining gap is localized without assuming the desired final equality.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

/-! ## Concrete raw and source ledgers -/

/-- The raw primewise residual before exceptional deletion, row correction,
and numerical guards. -/
def roughCanonicalRawSignedValuationResidual
    (n h K : Nat) (rawWeight : Nat -> Real) (p : Nat) : Real :=
  (∑ a ∈ roughUpperBlock n h, (a.factorization p : Real)) -
    ∑ a ∈ roughRawCandidateSet n h K,
      rawWeight a * (a.factorization p : Real)

/-- Exact charged-target expansion required by the paper's sign ledger. -/
def BankPaperCanonicalSignedResidualTargetLedger
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (p : Nat) : Prop :=
  ((certificate.selectorTailTarget R
      (R.paperFixedExceptionalFactors deltaStar)).factorization p : Real) =
    (∑ a ∈ roughUpperBlock n (upperTailLength c n),
      (a.factorization p : Real)) -
    (∑ a ∈ paperExceptionalUpperFactors n (upperTailLength c n) deltaStar,
      (a.factorization p : Real)) +
    (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
      (a.factorization p : Real)) -
    ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)



/-! ## Exact reduction of the source ledger -/

/-- The guarded candidates whose complete rough row is not exceptional. -/
def roughCanonicalNonexceptionalGuardedCandidateSet
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) : Finset Nat := by
  classical
  exact
    (R.roughCanonicalGuardedCandidateSet certificate deltaStar K).filter
      fun a =>
        ¬ RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a)

@[simp]
theorem mem_roughCanonicalNonexceptionalGuardedCandidateSet
    {c : Real} {depth n h K a : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) :
    a ∈ R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
        deltaStar K ↔
      a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K ∧
        ¬ RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) := by
  classical
  simp only [roughCanonicalNonexceptionalGuardedCandidateSet,
    Finset.mem_filter]



/-- The actual source contribution beyond surviving nonexceptional raw
weight.  It includes the smooth structured source, exceptional rows, and
the correction installed on every nonsmooth guarded row. -/
def roughCanonicalSourceValuationCorrectionMoment
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) (p : Nat) : Real :=
  (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      selector a * (a.factorization p : Real)) -
    ∑ a ∈ R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
        deltaStar K,
      roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta ell a * (a.factorization p : Real)

/-- The exact error made by replacing the correction moment of a supplied
source with the existing aggregate raw-pool correction. -/
def roughCanonicalSourceRawCorrectionValuationDefect
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) (p : Nat) : Real :=
  roughCanonicalSourceValuationCorrectionMoment
      (W := W) (K := K)
      R certificate deltaStar alpha beta ell selector p -
    roughCanonicalAggregateRawRowCorrection W n
      (upperTailLength c n) K deltaStar alpha beta ell p





/-! ## What the guarded postcharge correction actually contributes -/







/-- The correction moment installed by the implemented postcharge selector
on active nonsmooth rows.  Its guarded pools and guarded densities are
deliberately visible; this is not the raw correction used by the existing
quantitative residual bound. -/
def roughCanonicalAggregateGuardedPostchargeRowCorrection
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (p : Nat) : Real :=
  ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
      (upperTailLength c n) K deltaStar,
    R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
        deltaStar W K label alpha beta ell *
      ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K label,
        (a.factorization p : Real)





/-! ## The charged target ledger is already derivable -/





/-! ## Four-term identification and structured transport -/













/-! ## The literal Post-Hfit pre-selector -/



























end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardedRawCorrectionMomentDefectConnector -/
section


/-!
# Exact guarded-versus-raw correction-moment defect

The implemented nonsmooth selector spreads each postcharge discrepancy over
the guarded broad pool.  The quantitative signed residual instead uses the
older correction on the raw broad pool.  These corrections have the same
outer row index, but guarding changes both

* the correction numerator, through fixed/base charges and deleted raw mass;
* the normalized `p`-valuation moment of the correction pool.

Consequently, equality of the two aggregate correction moments is not a
set-theoretic reindex.  This file records the unconditional rowwise defect
and its exact aggregate sum.  Division is the totalized real division used by
the underlying correction densities, so none of the identities below needs a
pool-nonemptiness hypothesis.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

/-! ## Normalized pool moments and the postcharge numerator shift -/









/-! ## Density and row-moment identities -/







/-- The implemented guarded postcharge correction contribution of one
complete-rough label. -/
def roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) (alpha beta ell : Real)
    (p : Nat) : Real :=
  R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
      deltaStar W K label alpha beta ell *
    ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K label,
      (a.factorization p : Real)







/-! ## Aggregate defect -/

/-- The literal difference between the implemented guarded aggregate
correction moment and the older raw aggregate correction moment. -/
def roughCanonicalAggregateGuardedRawCorrectionValuationDefect
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (p : Nat) : Real :=
  R.roughCanonicalAggregateGuardedPostchargeRowCorrection certificate
      deltaStar W K alpha beta ell p -
    roughCanonicalAggregateRawRowCorrection W n
      (upperTailLength c n) K deltaStar alpha beta ell p













end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawRowCorrectionRateClosure -/
section


/-!
# Paper-rate closure for the raw nonsmooth row correction

The signed residual ledger isolates a uniform bound for the literal raw
row-correction density.  That bound is not an additional analytic input.
The sharp row theorem gives a numerator

`O_W((n / label) / L^2 + 1)`,

while the raw broad-pool theorem gives a denominator bounded below by a
fixed positive multiple of `n / label`.  On active nonexceptional rows the
same real cutoff in the definition of the row implies, uniformly,
`L^2 <= n / label`; hence the endpoint `+1` is absorbed.

This file records that conversion and then invokes the global valuation
census already proved in `BankPaperCanonicalSignedGuardResidual`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-- A fixed constant paying the sharp numerator and the reciprocal of the
linear raw broad-pool density.  The factor `24` is chosen so that dividing
by `4 L^2` leaves the pointwise density bound `6 C/(d L^2)`. -/
def roughCanonicalUniformRawRowCorrectionDensityConstant
    (W K0 : Nat) (c beta : Real) : Real :=
  24 * roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta /
    roughCanonicalRawBroadPoolDensity W











end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalCoreFirst -/
section


/-!
# Core-first cancellation for the signed exceptional residual

The exceptional term in Section 9 cannot be estimated by separating its
positive and negative halves.  The paper first fixes the complete smooth
core `b`, sums all physical rough pieces with that core, and only then takes
absolute values.  This file makes that order of summation literal.

The first part is completely finite.  It partitions both halves of
`roughCanonicalSignedExceptionalResidual` by `completeSmoothPart (yNat n)`,
transfers every low-prime valuation to that smooth part, and reindexes both
halves over one common positive prefix.  Thus the sign in each core is the
actual upper cardinality minus the actual weighted lower mass.

The second part records the elementary fixed-head cancellation used on the
leading term.  Its periodic coefficient has uniformly bounded partial sums;
finite Abel summation therefore bounds it against every sequence with the
paper's prime-power-by-prime-power variation estimate.  No rough-counting
asymptotic is used in these arguments.

The last part isolates the one genuinely new analytic input: the signed
four-to-five-prime chamber expansion for a fixed smooth core, before any
valuation sum or triangle inequality.  All subsequent core, valuation, and
endpoint ledgers are finite consequences of that expansion.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.LocalFugacityBounds

noncomputable section

namespace BankPaperRealization

/-! ## The literal common smooth-core partition -/

/-- Smooth cores which actually occur in the exceptional raw lower set. -/
def roughCanonicalExceptionalRawLowerSmoothParts
    (n h K : Nat) (deltaStar : Real) : Finset Nat :=
  (roughCanonicalExceptionalRawLowerSet n h K deltaStar).image
    (completeSmoothPart (yNat n))

/-- The exceptional raw lower factors with prescribed complete smooth core. -/
def roughCanonicalExceptionalRawLowerSmoothFiber
    (n h K : Nat) (deltaStar : Real) (b : Nat) : Finset Nat :=
  (roughCanonicalExceptionalRawLowerSet n h K deltaStar).filter
    (fun a => completeSmoothPart (yNat n) a = b)

@[simp]
theorem mem_roughCanonicalExceptionalRawLowerSmoothParts
    {n h K b : Nat} {deltaStar : Real} :
    b ∈ roughCanonicalExceptionalRawLowerSmoothParts n h K deltaStar ↔
      ∃ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
        completeSmoothPart (yNat n) a = b := by
  simp only [roughCanonicalExceptionalRawLowerSmoothParts,
    Finset.mem_image]

@[simp]
theorem mem_roughCanonicalExceptionalRawLowerSmoothFiber
    {n h K a b : Nat} {deltaStar : Real} :
    a ∈ roughCanonicalExceptionalRawLowerSmoothFiber n h K deltaStar b ↔
      a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar ∧
        completeSmoothPart (yNat n) a = b := by
  simp only [roughCanonicalExceptionalRawLowerSmoothFiber,
    Finset.mem_filter]















/-- The signed physical mass after fixing the complete smooth core `b`.
This is the literal upper count minus the literal weighted lower count. -/
def roughCanonicalSignedExceptionalCoreMass
    (n h K : Nat) (deltaStar : Real)
    (rawWeight : Nat → Real) (b : Nat) : Real :=
  ((paperExceptionalSmoothFiber n h deltaStar b).card : Real) -
    ∑ a ∈ roughCanonicalExceptionalRawLowerSmoothFiber
        n h K deltaStar b, rawWeight a







/-! ## The fixed-head periodic coefficient -/

/-- The paper's mean-zero fixed-head coefficient
`c_hd(b)=1-delta_hd^{-1} 1_{(b,P_hd)=1}`. -/
def roughHeadPeriodicCoreCoefficient (W b : Nat) : Real :=
  1 - if Nat.Coprime b (roughHeadModulus W) then
    1 / roughHeadDensity W else 0



/-- Partial sum of the fixed-head periodic coefficient. -/
def roughHeadPeriodicCorePrefix (W B : Nat) : Real :=
  ∑ b ∈ Finset.Icc 1 B, roughHeadPeriodicCoreCoefficient W b





/-- Prefix with a fixed coprime multiplier in the periodic argument. -/
def roughHeadPeriodicCoreMulPrefix (W D B : Nat) : Real :=
  ∑ b ∈ Finset.Icc 1 B, roughHeadPeriodicCoreCoefficient W (D * b)





/-! ## Finite Abel cancellation -/

/-- Total discrete variation relevant to Abel summation on `1,...,B`.
The value is zero for the empty prefix. -/
def roughCoreDiscreteVariation (F : Nat → Real) (B : Nat) : Real :=
  if B = 0 then 0 else
    |F B| + ∑ b ∈ Finset.Ioc 0 (B - 1), |F b - F (b + 1)|

/-- Weighted periodic core sum with a fixed multiplier. -/
def roughHeadPeriodicWeightedCoreSum
    (W D : Nat) (F : Nat → Real) (B : Nat) : Real :=
  ∑ b ∈ Finset.Icc 1 B,
    F b * roughHeadPeriodicCoreCoefficient W (D * b)







/-! ## Prime-power expansion of the periodic leading ledger -/



/-- The complete periodic leading ledger at one prime. -/
def roughHeadPeriodicValuationCoreSum
    (W p : Nat) (F : Nat → Real) (B : Nat) : Real :=
  ∑ b ∈ Finset.Icc 1 B,
    (b.factorization p : Real) *
      roughHeadPeriodicCoreCoefficient W b * F b





/-! ## Elementary valuation ledgers for the analytic remainders -/









/-! ## The isolated four-to-five chamber input -/

/-- The deep smooth-core prefix used before the cutoff band. -/
def roughCanonicalExceptionalDeepCoreSet
    (deltaStar : Real) (n : Nat) : Finset Nat :=
  Finset.Icc 1 (tangentPaperExceptionalCutoff deltaStar n / 2)

/-- The one fixed-ratio cutoff band `X0/2 < b ≤ 2X0`. -/
def roughCanonicalExceptionalCutoffCoreSet
    (deltaStar : Real) (n : Nat) : Finset Nat :=
  Finset.Ioc (tangentPaperExceptionalCutoff deltaStar n / 2)
    (2 * tangentPaperExceptionalCutoff deltaStar n)







/-- Smallest new analytic statement left by the finite reduction.

For each deep core it is precisely the signed four-to-five-prime expansion
after the three physical pieces have already been summed.  `kernelWeight`
contains the factor `K(log(2n/b)/log y)/b`; its prime-power discrete
variation records bounded `C^1` norm of `K`.  The cutoff-band clause is the
positive three-interval estimate.  Neither clause mentions valuations or
the target `N/(pL)` bound.
-/
def RoughCanonicalSignedExceptionalCoreChamberEstimate
    (W n h K : Nat) (deltaStar : Real) (rawWeight : Nat → Real)
    (kernelWeight coreError : Nat → Real)
    (deepConstant cutoffConstant variationConstant : Real) : Prop :=
  (∀ b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n,
      roughCanonicalSignedExceptionalCoreMass n h K deltaStar rawWeight b =
        ((h : Real) / Real.log (yNat n : Real)) *
          roughHeadPeriodicCoreCoefficient W b * kernelWeight b +
            coreError b) ∧
  (∀ b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n,
      |coreError b| ≤
        deepConstant * ((n : Real) / ((b : Real) * L n ^ 3) + 1)) ∧
  (∀ b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n,
      |roughCanonicalSignedExceptionalCoreMass n h K deltaStar rawWeight b| ≤
        cutoffConstant * ((n : Real) / ((b : Real) * L n ^ 2) + 1)) ∧
  (∀ p : Nat, p.Prime → W < p →
      ∀ k ∈ positiveExponents
          (tangentPaperExceptionalCutoff deltaStar n / 2),
        roughCoreDiscreteVariation
            (fun m => kernelWeight (p ^ k * m))
            ((tangentPaperExceptionalCutoff deltaStar n / 2) / p ^ k) ≤
          variationConstant / ((p ^ k : Nat) : Real))



/-! ## Endpoint absorption at the strict paper scale -/

/-- Normalized size of the exceptional smooth-core endpoint allowance. -/
def roughCanonicalExceptionalEndpointRatio
    (deltaStar : Real) (n : Nat) : Real :=
  (tangentPaperExceptionalCutoff deltaStar n : Real) * L n ^ 2 /
    (n : Real)







/-! ## Uniform paper-scale packaging -/

/-- Eventual form of the isolated chamber estimate for the literal balanced
raw point.  The constants are fixed before `n`, while the kernel and its
literal finite remainder may depend on `n`. -/
def RoughCanonicalSignedExceptionalCoreChamberEventually
    (W K : Nat) (c deltaStar beta : Real)
    (deepConstant cutoffConstant variationConstant : Real) : Prop :=
  ∀ᶠ n : Nat in atTop,
    ∃ kernelWeight coreError : Nat → Real,
      RoughCanonicalSignedExceptionalCoreChamberEstimate
        W n (upperTailLength c n) K deltaStar
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          (roughHeadBalancedAlpha W n (upperTailLength c n) K beta (L n))
          beta (L n))
        kernelWeight coreError deepConstant cutoffConstant variationConstant

/-- One fixed constant which pays all five terms in the finite core-first
ledger. -/
def roughCanonicalSignedExceptionalCoreBoundConstant
    (W : Nat) (c deltaStar deepConstant cutoffConstant
      variationConstant : Real) : Real :=
  20 * c * ((roughHeadModulus W : Real) / roughHeadDensity W) *
      variationConstant +
    (4 * deltaStar + 2) * deepConstant +
    12 * cutoffConstant





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveRoughChamberReduction -/
section


/-!
# Finite reduction for the four-to-five rough chamber

The rough-number lemma used in the bank argument is proved in the paper by
first counting ordered tuples of large primes and only afterwards passing to
ordinary integers.  This file formalizes that finite passage independently of
the analytic prime-number-theorem input.

For a natural interval `(A,B]`, the definitions below record

* integers all of whose prime factors exceed `y`;
* their layers with exactly `j` prime factors, counted with multiplicity;
* ordered prime-factor lists, represented canonically by the distinct
  permutations of `primeFactorsList`;
* the repeated-prime exceptional set.

If `B < (y+1)^5`, every rough integer in the interval lies in one of the four
layers `1 ≤ j ≤ 4`.  On the squarefree part the ordered multiplicity is
exactly `j!`; on the nonsquarefree part its deficit is bounded by `j!`.
Consequently the ordinary rough count differs from the factorially weighted
ordered count by at most the number of repeated-prime integers.  The latter is
at most `B/y`, by exact multiple counting and the elementary reciprocal-square
tail estimate.

Thus the only analytic input left by this module is an estimate for
`fourFiveOrderedPrimeMixture`.  No PNT statement, asymptotic assumption, or
unproved declaration occurs here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

namespace BankPaperRealization

noncomputable section

/-! ## Rough intervals and their Omega-layers -/

/-- The integers in `(A,B]` all of whose prime factors are strictly larger
than `y`.  Positivity is supplied by membership in `Ioc A B`. -/
def fourFiveRoughInterval (y A B : Nat) : Finset Nat :=
  (Finset.Ioc A B).filter
    (fun r => ∀ q, q ∈ r.primeFactorsList -> y < q)

/-- The layer of the rough interval with exactly `j` prime factors, counted
with multiplicity. -/
def fourFiveRoughOmegaLayer (j y A B : Nat) : Finset Nat :=
  (fourFiveRoughInterval y A B).filter
    (fun r => ArithmeticFunction.cardFactors r = j)

/-- The nonsquarefree part of the rough interval. -/
def fourFiveRoughRepeatedInterval (y A B : Nat) : Finset Nat :=
  (fourFiveRoughInterval y A B).filter (fun r => ¬Squarefree r)

/-- The `j`-th Omega-layer inside the nonsquarefree rough interval. -/
def fourFiveRoughRepeatedOmegaLayer (j y A B : Nat) : Finset Nat :=
  (fourFiveRoughRepeatedInterval y A B).filter
    (fun r => ArithmeticFunction.cardFactors r = j)

@[simp]
theorem mem_fourFiveRoughInterval {y A B r : Nat} :
    r ∈ fourFiveRoughInterval y A B ↔
      A < r ∧ r ≤ B ∧
        ∀ q, q ∈ r.primeFactorsList -> y < q := by
  simp only [fourFiveRoughInterval, Finset.mem_filter, Finset.mem_Ioc]
  tauto

@[simp]
theorem mem_fourFiveRoughOmegaLayer {j y A B r : Nat} :
    r ∈ fourFiveRoughOmegaLayer j y A B ↔
      r ∈ fourFiveRoughInterval y A B ∧
        ArithmeticFunction.cardFactors r = j := by
  simp only [fourFiveRoughOmegaLayer, Finset.mem_filter]

@[simp]
theorem mem_fourFiveRoughRepeatedInterval {y A B r : Nat} :
    r ∈ fourFiveRoughRepeatedInterval y A B ↔
      r ∈ fourFiveRoughInterval y A B ∧ ¬Squarefree r := by
  simp only [fourFiveRoughRepeatedInterval, Finset.mem_filter]

@[simp]
theorem mem_fourFiveRoughRepeatedOmegaLayer {j y A B r : Nat} :
    r ∈ fourFiveRoughRepeatedOmegaLayer j y A B ↔
      r ∈ fourFiveRoughRepeatedInterval y A B ∧
        ArithmeticFunction.cardFactors r = j := by
  simp only [fourFiveRoughRepeatedOmegaLayer, Finset.mem_filter]











/-! ## Ordered prime-factor lists -/

/-- Number of distinct orderings of the prime-factor multiset of `r`. -/
def fourFiveOrderedPrimeMultiplicity (r : Nat) : Nat :=
  r.primeFactorsList.permutations.toFinset.card

/-- All ordered prime-factor lists in the `j`-th rough layer.  This is the
literal finite ordered-tuple object; lists belonging to different products
are disjoint. -/
def fourFiveOrderedPrimeFactorLists
    (j y A B : Nat) : Finset (List Nat) :=
  (fourFiveRoughOmegaLayer j y A B).biUnion
    (fun r => r.primeFactorsList.permutations.toFinset)

/-- The ordered count in one Omega-layer. -/
def fourFiveOrderedPrimeLayerMass (j y A B : Nat) : Nat :=
  ∑ r ∈ fourFiveRoughOmegaLayer j y A B,
    fourFiveOrderedPrimeMultiplicity r





@[simp]
theorem mem_fourFiveOrderedPrimeFactorLists
    {j y A B : Nat} {l : List Nat} :
    l ∈ fourFiveOrderedPrimeFactorLists j y A B ↔
      ∃ r, r ∈ fourFiveRoughOmegaLayer j y A B ∧
        List.Perm l r.primeFactorsList := by
  simp only [fourFiveOrderedPrimeFactorLists, Finset.mem_biUnion,
    List.mem_toFinset, List.mem_permutations]







/-! ## Factorial weighting ∧ the repeated-prime deficit -/









/-- Factorially weighted ∑ of the four literal ordered-list counts. -/
def fourFiveOrderedPrimeMixture (y A B : Nat) : Real :=
  ∑ j ∈ Finset.Icc 1 4,
    (fourFiveOrderedPrimeLayerMass j y A B : Real) /
      (j.factorial : Real)



/-! ## The repeated-prime square ledger -/

/-- Rough integers in `(A,B]` divisible by the square of a prime above `y`. -/
def fourFiveRepeatedPrimeSquareSet (y A B : Nat) : Finset Nat := by
  classical
  exact (Finset.Ioc A B).filter (fun r =>
    ∃ q, q.Prime ∧ y < q ∧ q * q ∣ r)

/-- Multiples of `q^2` in the positive prefix through `B`. -/
def fourFiveSquareMultiples (q B : Nat) : Finset Nat :=
  (Finset.Ioc 0 B).filter (fun r => q * q ∣ r)

@[simp]
theorem mem_fourFiveRepeatedPrimeSquareSet {y A B r : Nat} :
    r ∈ fourFiveRepeatedPrimeSquareSet y A B ↔
      A < r ∧ r ≤ B ∧
        ∃ q, q.Prime ∧ y < q ∧ q * q ∣ r := by
  simp only [fourFiveRepeatedPrimeSquareSet, Finset.mem_filter,
    Finset.mem_Ioc]
  tauto

@[simp]
theorem mem_fourFiveSquareMultiples {q B r : Nat} :
    r ∈ fourFiveSquareMultiples q B ↔
      0 < r ∧ r ≤ B ∧ q * q ∣ r := by
  simp only [fourFiveSquareMultiples, Finset.mem_filter, Finset.mem_Ioc]
  tauto











/-! ## Minimal analytic interface and transfer -/

/-- The remaining analytic assertion, stripped of all finite combinatorics:
the factorially weighted ordered-prime mixture approximates a prescribed main
term with a prescribed error. -/
def FourFiveOrderedPrimeMixtureEstimate
    (y A B : Nat) (mainTerm error : Real) : Prop :=
  abs (fourFiveOrderedPrimeMixture y A B - mainTerm) ≤ error







end

end BankPaperRealization

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalPhysicalReindex -/
section


/-!
# Exact physical reindexing of the signed exceptional smooth core

This file is the finite, endpoint-exact bridge between the core-first
exceptional ledger and the four-to-five rough chamber.

The paper's exceptional condition is the literal real inequality

`2 * n / R < n ^ deltaStar`.

Accordingly, the natural lower endpoint for a rough label is the floor of
`2 * n / n ^ deltaStar`, not the quotient formed from the safe natural
ceiling used elsewhere for clean-list estimates.  After fixing a positive
smooth core `b`, multiplication by `b` gives a bijection between each
exceptional physical fibre and a rough interval whose lower endpoint is
clipped by that real exceptional floor.

The last theorem specializes the identity to the actual paper depth
`K0 + 1`, balanced alpha, upper-tail length, and logarithmic scale.  No
rough-counting estimate or asymptotic input occurs here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The literal real exceptional floor -/

/-- The largest natural rough label which can fail the paper's strict real
exceptional inequality.  Thus, for a positive rough label `r`,

`roughCanonicalRealExceptionalRoughCutoff n deltaStar < r`

is exactly `2*n/r < n^deltaStar`. -/
def roughCanonicalRealExceptionalRoughCutoff
    (n : Nat) (deltaStar : Real) : Nat :=
  ⌊2 * (n : Real) / (n : Real) ^ deltaStar⌋₊

/-- Exact conversion of the literal real exceptional inequality to the
strict natural cutoff supplied by the preceding floor. -/
theorem roughCanonicalRealExceptionalRoughCutoff_lt_iff
    {n r : Nat} {deltaStar : Real}
    (hn : 0 < n) (hr : 0 < r) :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar < r ↔
      RoughCanonicalExceptionalLabel n deltaStar r := by
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hrReal : (0 : Real) < (r : Real) := by
    exact_mod_cast hr
  have hpow : 0 < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  rw [roughCanonicalRealExceptionalRoughCutoff,
    Nat.floor_lt' hr.ne']
  unfold RoughCanonicalExceptionalLabel
  rw [div_lt_iff₀ hpow, div_lt_iff₀ hrReal]
  simp only [mul_comm]

/-! ## Three clipped rough physical intervals -/

/-- Rough labels in the physical interval obtained from `(lo,hi]` after
fixing the smooth core `b`, with the lower endpoint clipped by the literal
real exceptional floor. -/
def roughCanonicalExceptionalClippedRoughInterval
    (n : Nat) (deltaStar : Real) (b lo hi : Nat) : Finset Nat :=
  fourFiveRoughInterval (yNat n)
    (max (lo / b)
      (roughCanonicalRealExceptionalRoughCutoff n deltaStar))
    (hi / b)

/-- The clipped upper piece corresponding to `(2n,2n+h]`. -/
def roughCanonicalExceptionalUpperPhysicalRoughInterval
    (n h : Nat) (deltaStar : Real) (b : Nat) : Finset Nat :=
  roughCanonicalExceptionalClippedRoughInterval
    n deltaStar b (2 * n) (2 * n + h)

/-- The clipped high lower piece corresponding to `(2n-Kh,2n]`. -/
def roughCanonicalExceptionalHighPhysicalRoughInterval
    (n h K : Nat) (deltaStar : Real) (b : Nat) : Finset Nat :=
  roughCanonicalExceptionalClippedRoughInterval
    n deltaStar b (2 * n - K * h) (2 * n)

/-- The clipped broad lower piece corresponding to `(n,2n-Kh]`. -/
def roughCanonicalExceptionalBroadPhysicalRoughInterval
    (n h K : Nat) (deltaStar : Real) (b : Nat) : Finset Nat :=
  roughCanonicalExceptionalClippedRoughInterval
    n deltaStar b n (2 * n - K * h)

/-- Membership in a clipped interval is precisely intrinsic roughness,
literal real exceptionality, and membership of `b*r` in the original
physical interval. -/
@[simp]
theorem mem_roughCanonicalExceptionalClippedRoughInterval
    {n b lo hi r : Nat} {deltaStar : Real}
    (hn : 0 < n) (hb : 0 < b) :
    r ∈ roughCanonicalExceptionalClippedRoughInterval
        n deltaStar b lo hi ↔
      IsCompleteRoughLabel (yNat n) r ∧
        RoughCanonicalExceptionalLabel n deltaStar r ∧
        lo < b * r ∧ b * r ≤ hi := by
  rw [roughCanonicalExceptionalClippedRoughInterval,
    mem_fourFiveRoughInterval]
  constructor
  · rintro ⟨hrLower, hrUpper, hrough⟩
    have hrPos : 0 < r := by
      exact lt_of_le_of_lt (Nat.zero_le _) hrLower
    have hrLowerData := (max_lt_iff.mp hrLower)
    have hlo : lo < b * r := by
      have hlo' := (Nat.div_lt_iff_lt_mul hb).mp hrLowerData.1
      simpa only [Nat.mul_comm] using hlo'
    have hhi : b * r ≤ hi := by
      have hhi' := (Nat.le_div_iff_mul_le hb).mp hrUpper
      simpa only [Nat.mul_comm] using hhi'
    have hlabel : IsCompleteRoughLabel (yNat n) r := by
      refine ⟨hrPos, ?_⟩
      intro q hqFactor
      have hqMem : q ∈ r.primeFactorsList := by
        rw [← Nat.primeFactorsList_count_eq] at hqFactor
        exact List.count_pos_iff.mp (Nat.pos_of_ne_zero hqFactor)
      exact hrough q hqMem
    exact ⟨hlabel,
      (roughCanonicalRealExceptionalRoughCutoff_lt_iff
        hn hrPos).mp hrLowerData.2,
      hlo, hhi⟩
  · rintro ⟨hlabel, hexceptional, hlo, hhi⟩
    refine ⟨max_lt_iff.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · have hlo' := (Nat.div_lt_iff_lt_mul hb).mpr
        (by simpa only [Nat.mul_comm] using hlo)
      exact hlo'
    · exact
        (roughCanonicalRealExceptionalRoughCutoff_lt_iff
          hn hlabel.1).mpr hexceptional
    · exact (Nat.le_div_iff_mul_le hb).mpr
        (by simpa only [Nat.mul_comm] using hhi)
    · intro q hqMem
      apply hlabel.2 q
      rw [← Nat.primeFactorsList_count_eq]
      exact (List.count_pos_iff.mpr hqMem).ne'

/-! ## A generic physical smooth fibre -/

/-- Positive integers in `(lo,hi]` which lie in an exceptional complete
rough row and have complete smooth part exactly `b`. -/
def roughCanonicalExceptionalPhysicalSmoothFiber
    (n lo hi : Nat) (deltaStar : Real) (b : Nat) : Finset Nat := by
  classical
  exact (Finset.Ioc lo hi).filter fun a =>
    RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) ∧
        completeSmoothPart (yNat n) a = b

@[simp]
theorem mem_roughCanonicalExceptionalPhysicalSmoothFiber
    {n lo hi a b : Nat} {deltaStar : Real} :
    a ∈ roughCanonicalExceptionalPhysicalSmoothFiber
        n lo hi deltaStar b ↔
      lo < a ∧ a ≤ hi ∧
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) ∧
        completeSmoothPart (yNat n) a = b := by
  classical
  simp only [roughCanonicalExceptionalPhysicalSmoothFiber,
    Finset.mem_filter, Finset.mem_Ioc]
  tauto





/-! ## Identification of the literal upper and lower fibres -/

















/-! ## The exact three-piece core identity -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFourFivePrimeEndpoint -/
section


/-!
# The prime-counting endpoint used by the four/five chamber

The ordered-prime calculation needs a local prime-counting estimate with
enough logarithmic saving to survive the later partial summations.  This
file derives that estimate from the already audited power-saving PNT for
Chebyshev's theta function.

The main term below is the standard two-endpoint logarithmic-integral
increment

`B / log B - A / log A + integral_A^B dt / log(t)^2`.

Keeping this exact integration-by-parts presentation avoids introducing a
new global normalization for `li`.  Subtracting Mathlib's exact
`primeCounting_eq_theta_div_log_add_integral` identity at `A` and `B`
then leaves only the theta error.  A fourth-log theta error gives a
fifth-log local prime-counting error, uniformly in both endpoints.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory
open Erdos390.Full.PrimeBandQuadrature

/-- The two-endpoint logarithmic-integral main term, in the exact form
produced by integration by parts. -/
def fourFiveLogIntegralIncrement (A B : Real) : Real :=
  B / Real.log B - A / Real.log A +
    ∫ t in A..B, 1 / Real.log t ^ 2

/-- The theta-error integrand left after extracting the logarithmic-integral
main term from the exact prime-counting identity. -/
def fourFivePrimeCountingErrorKernel (t : Real) : Real :=
  thetaError t / (t * Real.log t ^ 2)

































end Erdos390.WholePaper.BankPaperRealization

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

/-- Prime coordinates available to a tuple whose total product is at most
`B`.  The upper bound is redundant after imposing the product condition, but
makes the ambient tuple set finite. -/
def fourFivePrimeCoordinateBand (y B : Nat) : Finset Nat :=
  (Finset.Ioc y B).filter Nat.Prime

/-- The literal fixed-length ordered-prime tuples with product in `(A,B]`. -/
def fourFiveOrderedPrimeTupleSet (j y A B : Nat) :
    Finset (Fin j -> Nat) :=
  (Fintype.piFinset
      (fun _i : Fin j => fourFivePrimeCoordinateBand y B)).filter
    (fun p => A < ∏ i, p i ∧ (∏ i, p i) <= B)

@[simp]
theorem mem_fourFivePrimeCoordinateBand {y B p : Nat} :
    p ∈ fourFivePrimeCoordinateBand y B ↔
      y < p ∧ p <= B ∧ p.Prime := by
  simp [fourFivePrimeCoordinateBand, and_assoc, and_left_comm,
    and_comm]

@[simp]
theorem mem_fourFiveOrderedPrimeTupleSet
    {j y A B : Nat} {p : Fin j -> Nat} :
    p ∈ fourFiveOrderedPrimeTupleSet j y A B ↔
      A < ∏ i, p i ∧ (∏ i, p i) <= B ∧
        ∀ i, y < p i ∧ p i <= B ∧ (p i).Prime := by
  simp only [fourFiveOrderedPrimeTupleSet, Finset.mem_filter,
    Fintype.mem_piFinset, mem_fourFivePrimeCoordinateBand]
  tauto

/-- The injective conversion from a fixed-length tuple to its coordinate
list. -/
def fourFiveTupleToListEmbedding (j : Nat) :
    (Fin j -> Nat) ↪ List Nat where
  toFun := List.ofFn
  inj' := List.ofFn_injective





/-! ## Splitting off the last coordinate -/

/-- Ambient tuples for the first `m` prime coordinates. -/
def fourFiveOrderedPrimePrefixSet (m y B : Nat) :
    Finset (Fin m -> Nat) :=
  Fintype.piFinset
    (fun _i : Fin m => fourFivePrimeCoordinateBand y B)

@[simp]
theorem mem_fourFiveOrderedPrimePrefixSet
    {m y B : Nat} {q : Fin m -> Nat} :
    q ∈ fourFiveOrderedPrimePrefixSet m y B ↔
      ∀ i, y < q i ∧ q i <= B ∧ (q i).Prime := by
  simp [fourFiveOrderedPrimePrefixSet]

/-- The allowed last primes after fixing the prefix `q`. -/
def fourFiveLastPrimeFiber
    {m : Nat} (q : Fin m -> Nat) (y A B : Nat) : Finset Nat :=
  (fourFivePrimeCoordinateBand y B).filter
    (fun p => A < (∏ i, q i) * p ∧ (∏ i, q i) * p <= B)

@[simp]
theorem mem_fourFiveLastPrimeFiber
    {m y A B : Nat} {q : Fin m -> Nat} {p : Nat} :
    p ∈ fourFiveLastPrimeFiber q y A B ↔
      y < p ∧ p <= B ∧ p.Prime ∧
        A < (∏ i, q i) * p ∧ (∏ i, q i) * p <= B := by
  simp only [fourFiveLastPrimeFiber, Finset.mem_filter,
    mem_fourFivePrimeCoordinateBand]
  tauto

/-- The finite set of prefix/last-prime pairs before reassembling them as
tuples of length `m + 1`. -/
def fourFiveLastPrimeSplitSet (m y A B : Nat) :
    Finset ((Fin m -> Nat) × Nat) :=
  ((fourFiveOrderedPrimePrefixSet m y B) ×ˢ
      fourFivePrimeCoordinateBand y B).filter
    (fun qp => A < (∏ i, qp.1 i) * qp.2 ∧
      (∏ i, qp.1 i) * qp.2 <= B)

@[simp]
theorem mem_fourFiveLastPrimeSplitSet
    {m y A B : Nat} {q : Fin m -> Nat} {p : Nat} :
    (q, p) ∈ fourFiveLastPrimeSplitSet m y A B ↔
      q ∈ fourFiveOrderedPrimePrefixSet m y B ∧
        p ∈ fourFiveLastPrimeFiber q y A B := by
  simp only [fourFiveLastPrimeSplitSet, Finset.mem_filter,
    Finset.mem_product]
  constructor
  · rintro ⟨⟨hq, hpBand⟩, hA, hB⟩
    exact ⟨hq, (mem_fourFiveLastPrimeFiber.mpr
      ⟨(mem_fourFivePrimeCoordinateBand.mp hpBand).1,
        (mem_fourFivePrimeCoordinateBand.mp hpBand).2.1,
        (mem_fourFivePrimeCoordinateBand.mp hpBand).2.2, hA, hB⟩)⟩
  · rintro ⟨hq, hp⟩
    have hpData := mem_fourFiveLastPrimeFiber.mp hp
    exact ⟨⟨hq, mem_fourFivePrimeCoordinateBand.mpr
      ⟨hpData.1, hpData.2.1, hpData.2.2.1⟩⟩,
      hpData.2.2.2.1, hpData.2.2.2.2⟩

/-- Append the last coordinate to a prefix, as an embedding. -/
def fourFiveSnocEmbedding (m : Nat) :
    ((Fin m -> Nat) × Nat) ↪ (Fin (m + 1) -> Nat) where
  toFun qp := Fin.snoc qp.1 qp.2
  inj' := by
    intro a b h
    apply Prod.ext
    · simpa using congrArg Fin.init h
    · simpa using congrFun h (Fin.last m)







/-! ## Every last-prime fibre is an exact clipped prime interval -/

/-- Natural lower endpoint after exposing the prefix product. -/
def fourFiveLastPrimeLower
    {m : Nat} (q : Fin m -> Nat) (y A : Nat) : Nat :=
  max y (A / ∏ i, q i)

/-- Natural upper endpoint after exposing the prefix product. -/
def fourFiveLastPrimeUpper
    {m : Nat} (q : Fin m -> Nat) (B : Nat) : Nat :=
  B / ∏ i, q i







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

/-- The actual reciprocal-prime atom at an integer. -/
def fourFiveReciprocalPrimeAtom (m : Nat) : Real :=
  if m.Prime then 1 / (m : Real) else 0

/-- The continuum primitive whose increments model reciprocal-prime mass. -/
def fourFiveLogLogPrimitive (m : Nat) : Real :=
  Real.log (Real.log (m : Real))

/-- The reciprocal-prime atom restricted to the strict tail above `A`. -/
def fourFiveAnchoredReciprocalPrimeAtom (A m : Nat) : Real :=
  if A < m then fourFiveReciprocalPrimeAtom m else 0

/-- Continuum log-log mass of the integer cell `(m-1,m]`, restricted to the
strict tail above `A`. -/
def fourFiveAnchoredLogLogCellAtom (A m : Nat) : Real :=
  if A < m then
    fourFiveLogLogPrimitive m - fourFiveLogLogPrimitive (m - 1)
  else 0

/-- Signed reciprocal-prime cell measure: actual prime atom minus its
continuum log-log cell mass. -/
def fourFiveReciprocalPrimeSignedCell (A m : Nat) : Real :=
  fourFiveAnchoredReciprocalPrimeAtom A m -
    fourFiveAnchoredLogLogCellAtom A m

/-- The cumulative signed reciprocal-prime discrepancy on `(A,Y]`. -/
def fourFiveReciprocalPrimeDiscrepancy (A Y : Nat) : Real :=
  fullReciprocalSum Y - fullReciprocalSum A -
    (fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A)

/-- Right-endpoint plus total discrete variation, the norm produced by
finite Abel summation on `(A,Y]`. -/
def fourFiveRightDiscreteBVNorm (f : Nat -> Real) (A Y : Nat) : Real :=
  |f Y| +
    ∑ m ∈ Finset.Ioc A (Y - 1), |f (m + 1) - f m|

/-- The reciprocal-prime signed measure paired with an arbitrary sequence. -/
def fourFiveReciprocalPrimeBVDefect
    (f : Nat -> Real) (A Y : Nat) : Real :=
  ∑ m ∈ Finset.Ioc A Y,
    f m * fourFiveReciprocalPrimeSignedCell A m





/-- A safe named cutoff which retains the lower endpoint `2` needed for
positive logarithms. -/
noncomputable def fourFiveReciprocalBVSafeCutoff : Nat :=
  max fullReciprocalSumUniformCutoff 2



























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

/-- A one-coordinate finite product-measure pairing. -/
def fourFiveFiniteProductOne {ι : Type*}
    (S : Finset ι) (w : ι -> Real) (K : ι -> Real) : Real :=
  ∑ i ∈ S, w i * K i

/-- A two-coordinate finite product-measure pairing. -/
def fourFiveFiniteProductTwo {ι : Type*}
    (S : Finset ι) (w : ι -> Real) (K : ι -> ι -> Real) : Real :=
  ∑ i ∈ S, w i * (∑ j ∈ S, w j * K i j)

/-- A three-coordinate finite product-measure pairing. -/
def fourFiveFiniteProductThree {ι : Type*}
    (S : Finset ι) (w : ι -> Real)
    (K : ι -> ι -> ι -> Real) : Real :=
  ∑ i ∈ S, w i *
    (∑ j ∈ S, w j * (∑ k ∈ S, w k * K i j k))







/-! ## Two elementary norm ledgers -/







/-! ## Reciprocal-prime specialization -/

/-- The uniform one-dimensional discrepancy factor used below. -/
noncomputable def fourFiveReciprocalBVError (A : Nat) : Real :=
  5 * fullReciprocalSumUniformConstant /
    Real.log (A : Real) ^ 3



/-- Actual reciprocal-prime product pairing in one coordinate. -/
def fourFiveActualReciprocalProductOne
    (K : Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductOne (Finset.Ioc A Y)
    (fourFiveAnchoredReciprocalPrimeAtom A) K

/-- Continuum log-log cell product pairing in one coordinate. -/
def fourFiveContinuumLogLogProductOne
    (K : Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductOne (Finset.Ioc A Y)
    (fourFiveAnchoredLogLogCellAtom A) K

/-- Actual reciprocal-prime product pairing in two coordinates. -/
def fourFiveActualReciprocalProductTwo
    (K : Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductTwo (Finset.Ioc A Y)
    (fourFiveAnchoredReciprocalPrimeAtom A) K

/-- Continuum log-log cell product pairing in two coordinates. -/
def fourFiveContinuumLogLogProductTwo
    (K : Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductTwo (Finset.Ioc A Y)
    (fourFiveAnchoredLogLogCellAtom A) K

/-- Actual reciprocal-prime product pairing in three coordinates. -/
def fourFiveActualReciprocalProductThree
    (K : Nat -> Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductThree (Finset.Ioc A Y)
    (fourFiveAnchoredReciprocalPrimeAtom A) K

/-- Continuum log-log cell product pairing in three coordinates. -/
def fourFiveContinuumLogLogProductThree
    (K : Nat -> Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductThree (Finset.Ioc A Y)
    (fourFiveAnchoredLogLogCellAtom A) K







/-! ## Quantitative one-, two-, and three-coordinate transfer -/







end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveMovingFaceBV -/
section


/-!
# Moving-face mass and bounded-variation certificates

For fixed values of all but one logarithmic prime coordinate, the simplex
kernel is increasing until the moving face and is zero afterwards.  Its
height is at most one because the omitted last-prime coordinate has
logarithmic size at least one.  Thus its right-endpoint-plus-variation norm
is at most two: at most one unit while increasing and at most one unit for
the unique cutoff jump.

This file proves that finite statement first for an abstract monotone
sequence, then instantiates it for the literal logarithmic moving-face
kernel.  The one-, two-, and three-coordinate kernels are finally fed into
the product-measure telescope with `V = 2`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeSums

/-! ## A finite one-jump BV lemma -/

/-- A sequence which agrees with `g` on `(A,R]` and is zero elsewhere. -/
def fourFiveCutoffSequence
    (A R : Nat) (g : Nat -> Real) (n : Nat) : Real :=
  if A < n ∧ n <= R then g n else 0





/-! ## The literal logarithmic moving face -/

/-- Logarithmic prime coordinate `log n / log y`. -/
def fourFiveLogCoordinate (y n : Nat) : Real :=
  Real.log (n : Real) / Real.log (y : Real)

/-- The literal one-dimensional conditional simplex kernel.  The first
condition centers it on the anchored interval `(A,Y]`; the second is the
strict moving face. -/
def fourFiveMovingFaceKernel
    (A y : Nat) (u c : Real) (n : Nat) : Real :=
  if A < n ∧ fourFiveLogCoordinate y n < u - c - 1 then
    (u - c - fourFiveLogCoordinate y n)⁻¹
  else 0

/-- Greatest active integer at or below `Y`. -/
def fourFiveMovingFaceCutoff
    (A Y y : Nat) (u c : Real) : Nat :=
  Nat.findGreatest
    (fun n => A < n ∧ fourFiveLogCoordinate y n < u - c - 1) Y

/-- Freeze the reciprocal kernel at the cutoff.  This gives a genuinely
monotone bounded extension on the whole finite interval. -/
def fourFiveMovingFaceMonotoneExtension
    (A Y y : Nat) (u c : Real) (n : Nat) : Real :=
  let R := fourFiveMovingFaceCutoff A Y y u c
  (u - c - fourFiveLogCoordinate y (min n R))⁻¹









/-!
The preceding certificate has an irrelevant `R < A` branch: the stopped
sequence is identically zero there.  Splitting that case first gives the
clean unconditional BV statement actually used below.
-/



/-! ## Compact reciprocal-mass bounds -/

/-- The paper's common mass cap on logarithmic coordinates up to `4.8`. -/
def fourFiveCompactReciprocalMass : Real :=
  1 + Real.log ((24 : Real) / 5)

















/-! ## One, two, and three moving-simplex coordinates -/

def fourFiveMovingSimplexKernelOne
    (A y : Nat) (u : Real) (p : Nat) : Real :=
  fourFiveMovingFaceKernel A y u 0 p

def fourFiveMovingSimplexKernelTwo
    (A y : Nat) (u : Real) (p q : Nat) : Real :=
  if A < p ∧ A < q ∧
      fourFiveLogCoordinate y p + fourFiveLogCoordinate y q < u - 1 then
    (u - fourFiveLogCoordinate y p - fourFiveLogCoordinate y q)⁻¹
  else 0

def fourFiveMovingSimplexKernelThree
    (A y : Nat) (u : Real) (p q r : Nat) : Real :=
  if A < p ∧ A < q ∧ A < r ∧
      fourFiveLogCoordinate y p + fourFiveLogCoordinate y q +
        fourFiveLogCoordinate y r < u - 1 then
    (u - fourFiveLogCoordinate y p - fourFiveLogCoordinate y q -
      fourFiveLogCoordinate y r)⁻¹
  else 0





















/-! ## Literal product-telescope instantiations -/







end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveFixedSimplexKernel -/
section


/-!
# Fixed-simplex kernels for the four/five chamber

For `m = j - 1`, the paper moves the continuum ordered-prime kernel to the
fixed simplex

`Delta_m = {z_i >= 0, sum z_i <= 1}`

by writing `T = u - j` and `s_i = 1 + T z_i`.  The resulting integrand is

`T^m / (prod_i (1 + T z_i) * (1 + T * (1 - sum_i z_i)))`.

This file defines that expression literally for every finite dimension,
proves its parameter derivative, justifies differentiation under the
compact-simplex integral, and packages the four kernels needed in the
ordered mixture.  On `4.1 <= u <= 4.7`, all relevant parameters satisfy
`0 < T < 3`, so every denominator is bounded away from zero.  Compactness
then supplies one common bound for the mixture and its continuous first
derivative.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## The fixed simplex and its rational integrand -/

/-- The closed `m`-simplex in its usual `m` free coordinates. -/
def fourFiveClosedSimplex (m : Nat) : Set (Fin m -> Real) :=
  {z | (∀ i, 0 <= z i) ∧ (∑ i, z i) <= 1}







/-- Product of the `m` ordinary transformed prime coordinates. -/
def fourFiveSimplexFactorProduct
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  ∏ i, (1 + T * z i)

/-- Derivative of `fourFiveSimplexFactorProduct` in the parameter `T`. -/
def fourFiveSimplexFactorProductDerivative
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  ∑ i ∈ Finset.univ,
    (∏ k ∈ Finset.univ.erase i, (1 + T * z k)) * z i

/-- The final, slack-coordinate factor. -/
def fourFiveSimplexRemainderFactor
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  1 + T * (1 - ∑ i, z i)

/-- Full denominator in the transformed fixed-simplex kernel. -/
def fourFiveSimplexDenominator
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  fourFiveSimplexFactorProduct m T z *
    fourFiveSimplexRemainderFactor m T z

/-- Parameter derivative of the full denominator. -/
def fourFiveSimplexDenominatorDerivative
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  fourFiveSimplexFactorProductDerivative m T z *
      fourFiveSimplexRemainderFactor m T z +
    fourFiveSimplexFactorProduct m T z * (1 - ∑ i, z i)

/-- The paper's transformed fixed-simplex integrand, including its Jacobian
factor `T^m`. -/
def fourFiveFixedSimplexIntegrand
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  T ^ m / fourFiveSimplexDenominator m T z

/-- Explicit first derivative of the transformed integrand in `T`. -/
def fourFiveFixedSimplexIntegrandDerivative
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  (((m : Real) * T ^ (m - 1)) *
        fourFiveSimplexDenominator m T z -
      T ^ m * fourFiveSimplexDenominatorDerivative m T z) /
    fourFiveSimplexDenominator m T z ^ 2



















/-! ## Differentiation under the compact-simplex integral -/

/-- The fixed-simplex continuum kernel in `m` free coordinates. -/
def fourFiveFixedSimplexKernel (m : Nat) (T : Real) : Real :=
  ∫ z in fourFiveClosedSimplex m,
    fourFiveFixedSimplexIntegrand m T z

/-- Integral of the explicit parameter derivative. -/
def fourFiveFixedSimplexKernelDerivative (m : Nat) (T : Real) : Real :=
  ∫ z in fourFiveClosedSimplex m,
    fourFiveFixedSimplexIntegrandDerivative m T z











/-! ## The four ordered continuum kernels -/

/-- `j = 1`: no preceding reciprocal-prime coordinate. -/
def fourFiveContinuumKernelOne (u : Real) : Real := u⁻¹

/-- `j = 2`: one-dimensional fixed simplex. -/
def fourFiveContinuumKernelTwo (u : Real) : Real :=
  fourFiveFixedSimplexKernel 1 (u - 2)

/-- `j = 3`: two-dimensional fixed simplex. -/
def fourFiveContinuumKernelThree (u : Real) : Real :=
  fourFiveFixedSimplexKernel 2 (u - 3)

/-- `j = 4`: three-dimensional fixed simplex. -/
def fourFiveContinuumKernelFour (u : Real) : Real :=
  fourFiveFixedSimplexKernel 3 (u - 4)

def fourFiveContinuumKernelOneDerivative (u : Real) : Real :=
  -(u ^ 2)⁻¹

def fourFiveContinuumKernelTwoDerivative (u : Real) : Real :=
  fourFiveFixedSimplexKernelDerivative 1 (u - 2)

def fourFiveContinuumKernelThreeDerivative (u : Real) : Real :=
  fourFiveFixedSimplexKernelDerivative 2 (u - 3)

def fourFiveContinuumKernelFourDerivative (u : Real) : Real :=
  fourFiveFixedSimplexKernelDerivative 3 (u - 4)















/-- Factorially weighted continuum kernel corresponding to the ordered
mixture `N_1 + N_2/2! + N_3/3! + N_4/4!`. -/
def fourFiveContinuumMixtureKernel (u : Real) : Real :=
  fourFiveContinuumKernelOne u +
    fourFiveContinuumKernelTwo u / 2 +
    fourFiveContinuumKernelThree u / 6 +
    fourFiveContinuumKernelFour u / 24

/-- Continuous first derivative of the mixture kernel. -/
def fourFiveContinuumMixtureKernelDerivative (u : Real) : Real :=
  fourFiveContinuumKernelOneDerivative u +
    fourFiveContinuumKernelTwoDerivative u / 2 +
    fourFiveContinuumKernelThreeDerivative u / 6 +
    fourFiveContinuumKernelFourDerivative u / 24









end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveCellLebesgueIdentification -/
section


/-!
# Log-log cells as literal Lebesgue cells

The continuum atom used by the reciprocal-prime BV transfer is not a
formal surrogate: on every integer cell `(m-1,m]` it is exactly the
Lebesgue integral of `dx / (x log x)`.  This file proves that identity and
rewrites the one-, two-, and three-coordinate cell products as products of
literal Lebesgue cell integrals.

The endpoint convention is immaterial for these absolutely continuous
cell measures.  No limiting argument is used in this identification.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-- Density of logarithmic-coordinate Lebesgue measure in the physical
prime variable. -/
def fourFiveLogLogLebesgueDensity (x : Real) : Real :=
  1 / (x * Real.log x)







/-- Literal Lebesgue mass of one integer cell. -/
def fourFiveLogLogLebesgueCellAtom (m : Nat) : Real :=
  ∫ x in ((m - 1 : Nat) : Real)..(m : Real),
    fourFiveLogLogLebesgueDensity x







/-- Product of one literal Lebesgue cell measure. -/
def fourFiveLebesgueCellProductOne
    (K : Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductOne (Finset.Ioc A Y)
    fourFiveLogLogLebesgueCellAtom K

/-- Product of two literal Lebesgue cell measures. -/
def fourFiveLebesgueCellProductTwo
    (K : Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductTwo (Finset.Ioc A Y)
    fourFiveLogLogLebesgueCellAtom K

/-- Product of three literal Lebesgue cell measures. -/
def fourFiveLebesgueCellProductThree
    (K : Nat -> Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductThree (Finset.Ioc A Y)
    fourFiveLogLogLebesgueCellAtom K







end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveOrderedMixtureAssembly -/
section


/-!
# Final factorial assembly for the ordered four/five mixture

This file is the algebraic terminus of the ordered-prime calculation.  It
defines the four fixed-simplex continuum layer mains, records the exact
`1, 1/2!, 1/3!, 1/4!` error ledger, and turns four layerwise estimates into
the repository's `FourFiveOrderedPrimeMixtureEstimate` proposition.

The second assembly theorem plugs in the exact last-prime endpoint estimates
from `BankPaperFourFiveOrderedLastPrimeExpansion`.  Its only remaining input
is the displayed four-layer bridge from the last-prime logarithmic integrals
to the fixed-simplex continuum layers.  The bridge budget exposes separately
the already-proved moving-face telescope losses

`0, 2 E, 4 E M, 6 E M^2`

and user-supplied cell-quadrature losses.  Thus the still-missing analytic
step is explicit in the theorem statement rather than hidden in a new axiom.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

/-! ## The four fixed-simplex layer main terms -/

def fourFiveContinuumLayerOneMain (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) *
    ∫ t in (A : Real)..(B : Real),
      fourFiveContinuumKernelOne
        (Real.log t / Real.log (y : Real))

def fourFiveContinuumLayerTwoMain (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) *
    ∫ t in (A : Real)..(B : Real),
      fourFiveContinuumKernelTwo
        (Real.log t / Real.log (y : Real))

def fourFiveContinuumLayerThreeMain (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) *
    ∫ t in (A : Real)..(B : Real),
      fourFiveContinuumKernelThree
        (Real.log t / Real.log (y : Real))

def fourFiveContinuumLayerFourMain (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) *
    ∫ t in (A : Real)..(B : Real),
      fourFiveContinuumKernelFour
        (Real.log t / Real.log (y : Real))

/-- The exact factorial mixture of the four continuum layer mains. -/
def fourFiveContinuumOrderedMixtureMain (y A B : Nat) : Real :=
  fourFiveContinuumLayerOneMain y A B +
    fourFiveContinuumLayerTwoMain y A B / 2 +
    fourFiveContinuumLayerThreeMain y A B / 6 +
    fourFiveContinuumLayerFourMain y A B / 24

/-- The same main term written as one integral of the already constructed
mixture kernel.  Equality with `fourFiveContinuumOrderedMixtureMain` follows
from ordinary linearity once the four displayed integrands are known to be
interval-integrable. -/
def fourFiveContinuumMixtureIntegralMain (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) *
    ∫ t in (A : Real)..(B : Real),
      fourFiveContinuumMixtureKernel
        (Real.log t / Real.log (y : Real))





/-- Exact factorial weighting of four nonnegative error ledgers. -/
def fourFiveFactorialErrorLedger
    (e1 e2 e3 e4 : Real) : Real :=
  e1 + e2 / 2 + e3 / 6 + e4 / 24



/-! ## Pure factorial error assembly -/



/-! ## The exact remaining bridge contract -/

/-- Product-telescope loss in a layer with `m = 0,1,2,3` preceding prime
coordinates.  These are exactly the constants proved by the moving-face BV
instantiations: `V = 2` times the `m`-term product telescope. -/
def fourFiveMovingFaceProductError
    (m : Nat) (E M : Real) : Real :=
  match m with
  | 0 => 0
  | 1 => 2 * E
  | 2 => 4 * E * M
  | 3 => 6 * E * M ^ 2
  | _ => 0









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

/-- A prefix product embedded in `Real`. -/
def fourFiveRealPrefixProduct
    {m : Nat} (q : Fin m -> Nat) : Real :=
  ((∏ i, q i : Nat) : Real)



/-- Exact real lower endpoint of the exposed last prime. -/
def fourFiveLastPrimeRealLower
    {m : Nat} (q : Fin m -> Nat) (y A : Nat) : Real :=
  max (y : Real) ((A : Real) / fourFiveRealPrefixProduct q)

/-- Exact real upper endpoint of the exposed last prime. -/
def fourFiveLastPrimeRealUpper
    {m : Nat} (q : Fin m -> Nat) (B : Nat) : Real :=
  (B : Real) / fourFiveRealPrefixProduct q





/-- Real-endpoint logarithmic integral for one last-prime fibre. -/
def fourFiveLastPrimeRealIntegral
    {m : Nat} (q : Fin m -> Nat) (y A B : Nat) : Real :=
  if fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B then
    ∫ v in fourFiveLastPrimeRealLower q y A..
      fourFiveLastPrimeRealUpper q B, 1 / Real.log v
  else 0

/-- Fifth-log PNT loss at the exact real moving endpoints. -/
def fourFiveLastPrimeRealEndpointError
    {m : Nat} (C : Real) (q : Fin m -> Nat)
    (y A B : Nat) : Real :=
  if fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B then
    3 * C * fourFiveLastPrimeRealUpper q B /
      Real.log (fourFiveLastPrimeRealLower q y A) ^ 5
  else 0

/-- The real-endpoint main after the exact physical substitution `t=qv`. -/
def fourFiveLastPrimeRealPhysicalIntegral
    {m : Nat} (q : Fin m -> Nat) (y A B : Nat) : Real :=
  if fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B then
    (fourFiveRealPrefixProduct q)⁻¹ *
      ∫ t in
          fourFiveRealPrefixProduct q *
              fourFiveLastPrimeRealLower q y A..
          fourFiveRealPrefixProduct q *
              fourFiveLastPrimeRealUpper q B,
        1 / Real.log (t / fourFiveRealPrefixProduct q)
  else 0











/-- Sum of the exactly transformed real-endpoint physical integrals. -/
def fourFiveOrderedLastPrimeRealIntegralLayer
    (m y A B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    fourFiveLastPrimeRealIntegral q y A B

/-- Sum of the exactly transformed real-endpoint physical integrals. -/
def fourFiveOrderedLastPrimeRealPhysicalLayer
    (m y A B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    fourFiveLastPrimeRealPhysicalIntegral q y A B





/-- Layer sum of the exact real-endpoint fifth-log losses. -/
def fourFiveOrderedLastPrimeRealEndpointErrorLayer
    (C : Real) (m y A B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    fourFiveLastPrimeRealEndpointError C q y A B

/-! ## Quantitative fifth-log ledger -/

/-- Literal reciprocal mass of the prime coordinate band `(y,B]`. -/
def fourFivePrimeCoordinateReciprocalMass (y B : Nat) : Real :=
  ∑ p ∈ fourFivePrimeCoordinateBand y B, (p : Real)⁻¹

/-- Literal reciprocal mass of all ordered `m`-coordinate prefixes. -/
def fourFiveOrderedPrimePrefixReciprocalMass
    (m y B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    (fourFiveRealPrefixProduct q)⁻¹















end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveLastPrimeContinuumDecomposition -/
section


/-!
# Exact decomposition of the last-prime/continuum bridge

The final ordered-mixture assembly deliberately exposes one analytic bridge.
This file splits that bridge into literal intermediate quantities, without
adding a hypothesis or an assumed estimate.

For a layer with `m = 0,1,2,3` preceding prime coordinates we insert

1. the physical `t`-integral with the actual reciprocal-prime product;
2. the corresponding product of continuum log-log cells, identified exactly
   with products of literal Lebesgue cell integrals;
3. the untransformed logarithmic moving-simplex integral;
4. the already constructed fixed-simplex layer `K_1,...,K_4`.

The three genuinely new interfaces are therefore the physical endpoint
change, cell aggregation (including right-endpoint/strict-face effects), and
the moving-to-fixed-simplex change of variables.  The reciprocal-prime
product replacement remains a separate interface supplied by the existing
product-measure telescope.

Every error below is the absolute value of a displayed difference.  The
`productBudgetOverrun` is the positive part left after charging the existing
moving-face budget.  Consequently the final bridge is a theorem for arbitrary
`E,M`; later quantitative work only has to show that the explicit three new
errors and the overrun have the desired size.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## Physical and cellwise intermediate layers -/

/-- The logarithmic coordinate of a real physical variable. -/
def fourFiveRealLogCoordinate (y : Nat) (t : Real) : Real :=
  Real.log t / Real.log (y : Real)













/-- The common physical `t`-integral after exposing the last prime, with the
remaining `m` coordinates still carrying the actual reciprocal-prime atoms.
Only the four layers used by the ordered mixture are retained. -/
def fourFivePhysicalActualMovingLayer
    (m y A B : Nat) : Real :=
  match m with
  | 0 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          (fourFiveRealLogCoordinate y t)⁻¹
  | 1 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveActualReciprocalProductOne
            (fourFiveMovingSimplexKernelOne y y
              (fourFiveRealLogCoordinate y t)) y B
  | 2 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveActualReciprocalProductTwo
            (fourFiveMovingSimplexKernelTwo y y
              (fourFiveRealLogCoordinate y t)) y B
  | 3 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveActualReciprocalProductThree
            (fourFiveMovingSimplexKernelThree y y
              (fourFiveRealLogCoordinate y t)) y B
  | _ => 0

/-- The same physical layer after replacing every actual reciprocal-prime
atom by its continuum log-log cell mass. -/
def fourFivePhysicalContinuumCellLayer
    (m y A B : Nat) : Real :=
  match m with
  | 0 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          (fourFiveRealLogCoordinate y t)⁻¹
  | 1 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveContinuumLogLogProductOne
            (fourFiveMovingSimplexKernelOne y y
              (fourFiveRealLogCoordinate y t)) y B
  | 2 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveContinuumLogLogProductTwo
            (fourFiveMovingSimplexKernelTwo y y
              (fourFiveRealLogCoordinate y t)) y B
  | 3 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveContinuumLogLogProductThree
            (fourFiveMovingSimplexKernelThree y y
              (fourFiveRealLogCoordinate y t)) y B
  | _ => 0

/-- The continuum-cell layer written with the literal cell integrals
`integral_(n-1)^n dx/(x log x)`. -/
def fourFivePhysicalLebesgueCellLayer
    (m y A B : Nat) : Real :=
  match m with
  | 0 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          (fourFiveRealLogCoordinate y t)⁻¹
  | 1 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLebesgueCellProductOne
            (fourFiveMovingSimplexKernelOne y y
              (fourFiveRealLogCoordinate y t)) y B
  | 2 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLebesgueCellProductTwo
            (fourFiveMovingSimplexKernelTwo y y
              (fourFiveRealLogCoordinate y t)) y B
  | 3 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLebesgueCellProductThree
            (fourFiveMovingSimplexKernelThree y y
              (fourFiveRealLogCoordinate y t)) y B
  | _ => 0

/-! ## The literal logarithmic moving simplex -/

/-- The untransformed logarithmic simplex for `m` preceding coordinates.
The last logarithmic coordinate is the slack `u - sum s`. -/
def fourFiveLogarithmicMovingSimplex
    (m : Nat) (u : Real) : Set (Fin m -> Real) :=
  {s | (∀ i, 1 <= s i) ∧ (∑ i, s i) <= u - 1}

/-- Density on the logarithmic moving simplex.  It is the image of
`prod dx_i/(x_i log x_i)` together with the exposed last-prime factor. -/
def fourFiveLogarithmicMovingSimplexIntegrand
    (m : Nat) (u : Real) (s : Fin m -> Real) : Real :=
  (∏ i, (s i)⁻¹) * (u - ∑ i, s i)⁻¹

/-- Literal untransformed moving-simplex kernel. -/
def fourFiveLogarithmicMovingSimplexKernel
    (m : Nat) (u : Real) : Real :=
  ∫ s in fourFiveLogarithmicMovingSimplex m u,
    fourFiveLogarithmicMovingSimplexIntegrand m u s

/-- The physical outer integral of the literal moving-simplex kernel. -/
def fourFivePhysicalMovingSimplexLayer
    (m y A B : Nat) : Real :=
  match m with
  | 0 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          (fourFiveRealLogCoordinate y t)⁻¹
  | 1 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLogarithmicMovingSimplexKernel 1
            (fourFiveRealLogCoordinate y t)
  | 2 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLogarithmicMovingSimplexKernel 2
            (fourFiveRealLogCoordinate y t)
  | 3 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLogarithmicMovingSimplexKernel 3
            (fourFiveRealLogCoordinate y t)
  | _ => 0

/-- The already constructed fixed-simplex target, indexed by the number of
preceding coordinates rather than by the total layer number. -/
def fourFiveFixedContinuumLayer
    (m y A B : Nat) : Real :=
  match m with
  | 0 => fourFiveContinuumLayerOneMain y A B
  | 1 => fourFiveContinuumLayerTwoMain y A B
  | 2 => fourFiveContinuumLayerThreeMain y A B
  | 3 => fourFiveContinuumLayerFourMain y A B
  | _ => 0

/-! ## Exact cell-to-Lebesgue equalities under the outer integral -/









/-! ## Pointwise reuse of the moving-face product telescope -/







/-! ## Three new exact error interfaces and the existing product interface -/







/-- Existing interface: actual reciprocal-prime products versus continuum
log-log cell products. -/
def fourFivePhysicalProductReplacementError
    (m y A B : Nat) : Real :=
  abs (fourFivePhysicalActualMovingLayer m y A B -
    fourFivePhysicalContinuumCellLayer m y A B)

/-- Piece 2: right-endpoint Lebesgue cells, including their strict moving
faces, versus the literal moving simplex. -/
def fourFiveLebesgueCellAggregationError
    (m y A B : Nat) : Real :=
  abs (fourFivePhysicalLebesgueCellLayer m y A B -
    fourFivePhysicalMovingSimplexLayer m y A B)

/-- Piece 3: the literal moving simplex versus the fixed-simplex kernel
`K_(m+1)`. -/
def fourFiveMovingToFixedSimplexError
    (m y A B : Nat) : Real :=
  abs (fourFivePhysicalMovingSimplexLayer m y A B -
    fourFiveFixedContinuumLayer m y A B)





/-! The zero-prefix layer has no product, cell-aggregation, or simplex
change-of-variables loss.  Only its literal last-prime endpoint change can
remain in the exact bridge ledger. -/















/-! ## Pure four-stage triangle ledger -/









/-! ## Discharging the assembly bridge without a new contract -/





end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveMovingFixedSimplexIdentification -/
section


/-!
# Exact moving-simplex to fixed-simplex identification

For `T = u - (m+1) > 0`, the affine map

`s_i = 1 + T z_i`

maps the closed unit `m`-simplex bijectively onto the logarithmic moving
simplex.  Its Jacobian is `T^m`, and the transformed density is exactly
`fourFiveFixedSimplexIntegrand`.  This discharges the third residual in the
continuum bridge by equality, not by an assumed estimate.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-- Coordinatewise affine map from the fixed simplex to the logarithmic
moving simplex. -/
def fourFiveSimplexAffineMap
    (m : Nat) (T : Real) (z : Fin m -> Real) : Fin m -> Real :=
  (1 : Fin m -> Real) + T • z

/-- Its constant Fréchet derivative. -/
def fourFiveSimplexAffineDerivative
    (m : Nat) (T : Real) :
    (Fin m -> Real) →L[Real] (Fin m -> Real) :=
  T • ContinuousLinearMap.id Real (Fin m -> Real)















/-! ## The four physical layer identities -/















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

/-- The reciprocal part of a conditional moving-face kernel, before the
anchor and strict-face cutoffs are imposed. -/
def fourFiveRealMovingFaceReciprocal
    (y : Nat) (u c x : Real) : Real :=
  (u - c - fourFiveRealLogCoordinate y x)⁻¹

/-- The conditional moving-face kernel on the real physical coordinate.
At a natural right endpoint it is the kernel already used by the discrete
BV argument. -/
def fourFiveRealMovingFaceKernel
    (A y : Nat) (u c x : Real) : Real :=
  if (A : Real) < x ∧
      fourFiveRealLogCoordinate y x < u - c - 1 then
    fourFiveRealMovingFaceReciprocal y u c x
  else 0

@[simp] theorem fourFiveRealLogCoordinate_natCast
    (y n : Nat) :
    fourFiveRealLogCoordinate y (n : Real) =
      fourFiveLogCoordinate y n := by
  rfl

















/-! ## The unique cell crossed by the strict face -/

/-- The strict face crosses cell `(n-1,n]` when its lower endpoint is on
the active side and its right endpoint is on the inactive side. -/
def fourFiveMovingFaceStrictCell
    (y n : Nat) (u c : Real) : Prop :=
  fourFiveLogCoordinate y (n - 1) < u - c - 1 ∧
    u - c - 1 <= fourFiveLogCoordinate y n

/-- The only natural index at which a strict-face cell can occur.  If the
integer cutoff lies below the anchor this is the first cell; otherwise it
is the cell immediately following the greatest active integer. -/
def fourFiveMovingFaceStrictCellIndex
    (A Y y : Nat) (u c : Real) : Nat :=
  max (A + 1) (fourFiveMovingFaceCutoff A Y y u c + 1)





/-! ## A two-unit finite oscillation envelope -/

/-- Cellwise oscillation envelope.  The first summand is the telescoping
increase on active right endpoints.  The second reserves one unit for the
unique strict-face cell. -/
def fourFiveMovingFaceCellOscillationEnvelope
    (A Y y : Nat) (u c : Real) (n : Nat) : Real :=
  let R := fourFiveMovingFaceCutoff A Y y u c
  let g := fun k : Nat =>
    fourFiveRealMovingFaceReciprocal y u c (k : Real)
  (if A < n ∧ n <= R then g n - g (n - 1) else 0) +
    if n = fourFiveMovingFaceStrictCellIndex A Y y u c then 1 else 0















/-! ## Pointwise right-endpoint control -/



/-! ## The mesh is derived from the literal paper cells -/

/-- Explicit upper bound for every log-log cell beginning at or above `A`. -/
def fourFiveLogLogCellMeshBound (A : Nat) : Real :=
  1 / ((A : Real) * Real.log (A : Real))

















/-! ## The finite one-dimensional quadrature defect -/

/-- The literal signed defect on one paper cell. -/
def fourFiveMovingFaceLebesgueCellDefect
    (A _Y y : Nat) (u c : Real) (n : Nat) : Real :=
  ∫ x in (((n - 1 : Nat) : Real))..(n : Real),
    fourFiveLogLogLebesgueDensity x *
      (fourFiveMovingFaceKernel A y u c n -
        fourFiveRealMovingFaceKernel A y u c x)





/-- Sum of all literal signed cell defects for a conditional face. -/
def fourFiveMovingFaceLebesgueCellDefectSum
    (A Y y : Nat) (u c : Real) : Real :=
  ∑ n ∈ Finset.Ioc A Y,
    fourFiveMovingFaceLebesgueCellDefect A Y y u c n











/-- The finite right-endpoint log-log-cell sum. -/
def fourFiveMovingFaceRightEndpointCellSum
    (A Y y : Nat) (u c : Real) : Real :=
  ∑ n ∈ Finset.Ioc A Y,
    fourFiveLogLogLebesgueCellAtom n *
      fourFiveMovingFaceKernel A y u c n

/-- The same finite union of cells with the moving-face kernel allowed to
vary inside each literal cell. -/
def fourFiveMovingFaceRealCellIntegralSum
    (A Y y : Nat) (u c : Real) : Real :=
  ∑ n ∈ Finset.Ioc A Y,
    ∫ x in (((n - 1 : Nat) : Real))..(n : Real),
      fourFiveLogLogLebesgueDensity x *
        fourFiveRealMovingFaceKernel A y u c x







end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveMovingSimplexCellTelescope -/
section


/-!
# Product telescope for moving-simplex log-log cells

The one-dimensional cell defect has two exact pieces: an interior
telescoping defect and the defect of the unique crossed strict-face cell.
This file carries each piece separately through the two- and
three-coordinate product telescope.

For an arbitrary conditional defect `D(c)` bounded by `R`, the two
replacement positions cost `2 M R` and the three replacement positions
cost `3 M^2 R`, where `M` bounds the total log-log cell mass.  Applying this
once with the interior defect (`R = delta_A`) and once with the strict-face
defect (`R = delta_A`) gives

* one coordinate: `delta_A + delta_A = 2 delta_A`;
* two coordinates: `2 delta_A M + 2 delta_A M = 4 delta_A M`;
* three coordinates: `3 delta_A M^2 + 3 delta_A M^2 = 6 delta_A M^2`.

Every expression is a finite sum of the paper's literal cells.  In
particular, no convergence or abstract mesh hypothesis is used.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## The existing compact mass budget, in literal-cell form -/





/-! ## Generic finite cell-product ledgers -/

/-- Two positions at which a one-dimensional conditional cell defect can
occur.  The first untouched coordinate is sampled at its right endpoint;
the second is already integrated through its literal cell. -/
def fourFiveLogLogCellTelescopeTwo
    (D : Real -> Real) (A Y y : Nat) : Real :=
  (∑ q ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom q *
        D (fourFiveLogCoordinate y q)) +
    ∑ p ∈ Finset.Ioc A Y,
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          D (fourFiveRealLogCoordinate y x)



/-- The same three-position ledger ordered from the last sampled coordinate.
Keeping that finite coordinate outer avoids an unnecessary Fubini swap in
the exact three-coordinate hybrid identity. -/
def fourFiveLogLogCellTelescopeThreeRightOrdered
    (D : Real -> Real) (A Y y : Nat) : Real :=
  (∑ r ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom r *
        fourFiveLogLogCellTelescopeTwo
          (fun c => D (c + fourFiveLogCoordinate y r)) A Y y) +
    ∑ p ∈ Finset.Ioc A Y,
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∑ q ∈ Finset.Ioc A Y,
            ∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                D (fourFiveRealLogCoordinate y x +
                  fourFiveRealLogCoordinate y z))







/-! ## Interior and strict-face specializations -/





























/-! ## Corollaries with the paper's common compact mass cap -/





end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveMovingSimplexCellIdentification -/
section


/-!
# Exact finite-cell identification for the moving simplex

This file identifies the two-coordinate cell telescope with the literal
difference between the right-corner sampled product and the iterated real
cell integral.  The proof inserts one hybrid product.  All rearrangements
are finite-sum identities or Fubini on one compact cell rectangle; the
joint kernel is measurable and bounded there.

The same real kernel is also prepared in three coordinates.  It is the
literal physical-variable form of the logarithmic moving-simplex density.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## Real moving-simplex kernels -/

def fourFiveRealMovingSimplexKernelOne
    (A y : Nat) (u x : Real) : Real :=
  fourFiveRealMovingFaceKernel A y u 0 x

def fourFiveRealMovingSimplexKernelTwo
    (A y : Nat) (u x z : Real) : Real :=
  if (A : Real) < x ∧ (A : Real) < z ∧
      fourFiveRealLogCoordinate y x +
        fourFiveRealLogCoordinate y z < u - 1 then
    (u - fourFiveRealLogCoordinate y x -
      fourFiveRealLogCoordinate y z)⁻¹
  else 0

def fourFiveRealMovingSimplexKernelThree
    (A y : Nat) (u x z w : Real) : Real :=
  if (A : Real) < x ∧ (A : Real) < z ∧ (A : Real) < w ∧
      fourFiveRealLogCoordinate y x +
        fourFiveRealLogCoordinate y z +
          fourFiveRealLogCoordinate y w < u - 1 then
    (u - fourFiveRealLogCoordinate y x -
      fourFiveRealLogCoordinate y z -
        fourFiveRealLogCoordinate y w)⁻¹
  else 0



























/-! ## Integrability on one literal cell rectangle -/

 def fourFiveRealMovingSimplexDensityTwo
    (A y : Nat) (u : Real) (p : Real × Real) : Real :=
  fourFiveLogLogLebesgueDensity p.1 *
    fourFiveLogLogLebesgueDensity p.2 *
      fourFiveRealMovingSimplexKernelTwo A y u p.1 p.2





/-! ## Sample, hybrid, and fully integrated two-coordinate products -/

def fourFiveMovingSimplexRightEndpointProductTwo
    (A Y y : Nat) (u : Real) : Real :=
  fourFiveLebesgueCellProductTwo
    (fourFiveMovingSimplexKernelTwo A y u) A Y

def fourFiveMovingSimplexHybridCellProductTwo
    (A Y y : Nat) (u : Real) : Real :=
  ∑ p ∈ Finset.Ioc A Y,
    ∑ q ∈ Finset.Ioc A Y,
      fourFiveLogLogLebesgueCellAtom q *
        (∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            fourFiveRealMovingSimplexKernelTwo A y u x (q : Real))

def fourFiveMovingSimplexIteratedRealCellProductTwo
    (A Y y : Nat) (u : Real) : Real :=
  ∑ p ∈ Finset.Ioc A Y,
    ∑ q ∈ Finset.Ioc A Y,
      ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
        fourFiveLogLogLebesgueDensity x *
          (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
            fourFiveLogLogLebesgueDensity z *
              fourFiveRealMovingSimplexKernelTwo A y u x z)









/-! ## Three coordinates, using the exact two-coordinate block -/

def fourFiveMovingSimplexRightEndpointProductThree
    (A Y y : Nat) (u : Real) : Real :=
  fourFiveLebesgueCellProductThree
    (fourFiveMovingSimplexKernelThree A y u) A Y

/-- Hybrid in which the first two coordinates are integrated and the last
coordinate is still sampled at its cell endpoint. -/
def fourFiveMovingSimplexTwoIntegratedHybridThree
    (A Y y : Nat) (u : Real) : Real :=
  ∑ r ∈ Finset.Ioc A Y,
    fourFiveLogLogLebesgueCellAtom r *
      fourFiveMovingSimplexIteratedRealCellProductTwo A Y y
        (u - fourFiveLogCoordinate y r)

def fourFiveMovingSimplexIteratedRealCellProductThree
    (A Y y : Nat) (u : Real) : Real :=
  ∑ p ∈ Finset.Ioc A Y,
    ∑ q ∈ Finset.Ioc A Y,
      ∑ r ∈ Finset.Ioc A Y,
        ∫ x in (((p - 1 : Nat) : Real))..(p : Real),
          fourFiveLogLogLebesgueDensity x *
            (∫ z in (((q - 1 : Nat) : Real))..(q : Real),
              fourFiveLogLogLebesgueDensity z *
                (∫ w in (((r - 1 : Nat) : Real))..(r : Real),
                  fourFiveLogLogLebesgueDensity w *
                    fourFiveRealMovingSimplexKernelThree A y u x z w))









 def fourFiveRealMovingSimplexDensityThree
    (A y : Nat) (u : Real) (p : (Real × Real) × Real) : Real :=
  fourFiveLogLogLebesgueDensity p.1.1 *
    fourFiveLogLogLebesgueDensity p.1.2 *
      fourFiveLogLogLebesgueDensity p.2 *
        fourFiveRealMovingSimplexKernelThree A y u p.1.1 p.1.2 p.2



































/-! ## Exact union of the active physical cells -/





def fourFiveMovingSimplexActivePhysicalIntegralTwo
    (A Y y : Nat) (u : Real) : Real :=
  ∫ x in (A : Real)..(Y : Real),
    fourFiveLogLogLebesgueDensity x *
      (∫ z in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity z *
          fourFiveRealMovingSimplexKernelTwo A y u x z)

def fourFiveMovingSimplexActivePhysicalIntegralThree
    (A Y y : Nat) (u : Real) : Real :=
  ∫ x in (A : Real)..(Y : Real),
    fourFiveLogLogLebesgueDensity x *
      (∫ z in (A : Real)..(Y : Real),
        fourFiveLogLogLebesgueDensity z *
          (∫ w in (A : Real)..(Y : Real),
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree A y u x z w))



















/-! ## Joint integrability on the finite active box -/







end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveActiveLogCoordinate -/
section


/-!
# Active physical cells and logarithmic coordinates

This file isolates the exact change of variables used after the finite
right-endpoint cell telescope.  For every positive number of preceding
coordinates, the coordinatewise map

`s_i ↦ exp (log y * s_i)`

sends the strict logarithmic moving simplex onto the physical active
region.  Its Jacobian cancels the factors `dx_i / (x_i log x_i)` exactly.
The strict and closed logarithmic simplexes differ only on the frontier of
a convex set, hence have the same Lebesgue integral.  No limiting mesh or
convergence statement is used.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## Strict and physical moving simplexes -/

def fourFiveStrictLogarithmicMovingSimplex
    (m : Nat) (u : Real) : Set (Fin m -> Real) :=
  {s | (∀ i, 1 < s i) ∧ (∑ i, s i) < u - 1}

def fourFivePhysicalActiveMovingSimplex
    (m : Nat) (y : Nat) (u : Real) : Set (Fin m -> Real) :=
  {x | (∀ i, (y : Real) < x i) ∧
    (∑ i, fourFiveRealLogCoordinate y (x i)) < u - 1}

def fourFivePhysicalActiveMovingSimplexIntegrand
    (m : Nat) (y : Nat) (u : Real) (x : Fin m -> Real) : Real :=
  (∏ i, fourFiveLogLogLebesgueDensity (x i)) *
    (u - ∑ i, fourFiveRealLogCoordinate y (x i))⁻¹

def fourFivePhysicalActiveMovingSimplexKernel
    (m : Nat) (y : Nat) (u : Real) : Real :=
  ∫ x in fourFivePhysicalActiveMovingSimplex m y u,
    fourFivePhysicalActiveMovingSimplexIntegrand m y u x



def fourFivePhysicalActiveMovingSimplexOne
    (y : Nat) (u : Real) : Set Real :=
  {x | (y : Real) < x ∧ fourFiveRealLogCoordinate y x < u - 1}

def fourFivePhysicalActiveMovingSimplexTwo
    (y : Nat) (u : Real) : Set (Real × Real) :=
  {p | (y : Real) < p.1 ∧ (y : Real) < p.2 ∧
    fourFiveRealLogCoordinate y p.1 +
      fourFiveRealLogCoordinate y p.2 < u - 1}

def fourFivePhysicalActiveMovingSimplexThree
    (y : Nat) (u : Real) : Set ((Real × Real) × Real) :=
  {p | (y : Real) < p.1.1 ∧ (y : Real) < p.1.2 ∧
    (y : Real) < p.2 ∧
    fourFiveRealLogCoordinate y p.1.1 +
      fourFiveRealLogCoordinate y p.1.2 +
        fourFiveRealLogCoordinate y p.2 < u - 1}

def fourFivePhysicalActiveIntegrandOne
    (y : Nat) (u x : Real) : Real :=
  fourFiveLogLogLebesgueDensity x *
    (u - fourFiveRealLogCoordinate y x)⁻¹

def fourFivePhysicalActiveIntegrandTwo
    (y : Nat) (u : Real) (p : Real × Real) : Real :=
  fourFiveLogLogLebesgueDensity p.1 *
    fourFiveLogLogLebesgueDensity p.2 *
      (u - fourFiveRealLogCoordinate y p.1 -
        fourFiveRealLogCoordinate y p.2)⁻¹

def fourFivePhysicalActiveIntegrandThree
    (y : Nat) (u : Real) (p : (Real × Real) × Real) : Real :=
  fourFiveLogLogLebesgueDensity p.1.1 *
    fourFiveLogLogLebesgueDensity p.1.2 *
      fourFiveLogLogLebesgueDensity p.2 *
        (u - fourFiveRealLogCoordinate y p.1.1 -
          fourFiveRealLogCoordinate y p.1.2 -
            fourFiveRealLogCoordinate y p.2)⁻¹







/-- The concrete coordinate equivalence used to express the three-variable
Pi integral in the paper's nested `((x,z),w)` order. -/
def fourFiveFinThreeArrow :
    (Fin 3 -> Real) ≃ᵐ ((Real × Real) × Real) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Real) 0).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl Real)
      (MeasurableEquiv.finTwoArrow (α := Real))).trans
        MeasurableEquiv.prodAssoc.symm)

@[simp] theorem fourFiveFinThreeArrow_apply
    (s : Fin 3 -> Real) :
    fourFiveFinThreeArrow s = ((s 0, s 1), s 2) := by
  change ((s 0, (Fin.tail s) 0), (Fin.tail s) 1) =
    ((s 0, s 1), s 2)
  rfl







@[simp] theorem fourFiveFinThreeArrow_symm_apply_zero
    (p : (Real × Real) × Real) :
    (fourFiveFinThreeArrow.symm p) 0 = p.1.1 := by
  have h := congrArg (fun q : (Real × Real) × Real => q.1.1)
    (fourFiveFinThreeArrow.apply_symm_apply p)
  simpa only [fourFiveFinThreeArrow_apply] using h

@[simp] theorem fourFiveFinThreeArrow_symm_apply_one
    (p : (Real × Real) × Real) :
    (fourFiveFinThreeArrow.symm p) 1 = p.1.2 := by
  have h := congrArg (fun q : (Real × Real) × Real => q.1.2)
    (fourFiveFinThreeArrow.apply_symm_apply p)
  simpa only [fourFiveFinThreeArrow_apply] using h

@[simp] theorem fourFiveFinThreeArrow_symm_apply_two
    (p : (Real × Real) × Real) :
    (fourFiveFinThreeArrow.symm p) 2 = p.2 := by
  have h := congrArg (fun q : (Real × Real) × Real => q.2)
    (fourFiveFinThreeArrow.apply_symm_apply p)
  simpa only [fourFiveFinThreeArrow_apply] using h



























def fourFiveCoordinateSumCLM (m : Nat) :
    (Fin m -> Real) →L[Real] Real :=
  ∑ i, (ContinuousLinearMap.proj i :
    (Fin m -> Real) →L[Real] Real)

@[simp] theorem fourFiveCoordinateSumCLM_apply
    (m : Nat) (s : Fin m -> Real) :
    fourFiveCoordinateSumCLM m s = ∑ i, s i := by
  simp [fourFiveCoordinateSumCLM]









/-! ## The coordinatewise exponential map and its Jacobian -/

def fourFiveLogCoordinateExpMap
    (m : Nat) (y : Nat) (s : Fin m -> Real) : Fin m -> Real :=
  fun i => Real.exp (Real.log (y : Real) * s i)

def fourFiveLogCoordinateExpDerivative
    (m : Nat) (y : Nat) (s : Fin m -> Real) :
    (Fin m -> Real) →L[Real] (Fin m -> Real) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
      (Real.log (y : Real) *
        Real.exp (Real.log (y : Real) * s i))).comp
      (ContinuousLinearMap.proj i)







@[simp] theorem fourFiveRealLogCoordinate_expMap
    {m y : Nat} (hy : 2 <= y) (s : Fin m -> Real) (i : Fin m) :
    fourFiveRealLogCoordinate y
        (fourFiveLogCoordinateExpMap m y s i) = s i := by
  have hlog : Real.log (y : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < y by omega)))
  unfold fourFiveRealLogCoordinate fourFiveLogCoordinateExpMap
  rw [Real.log_exp]
  field_simp [hlog]









/-! ## The literal finite cells equal the logarithmic kernel -/













end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveLebesgueCellAggregationBound -/
section


/-!
# Explicit bound for the Lebesgue-cell aggregation residual

The fixed physical box `(y,B]` is used as a measurable proxy under the
outer `t` integral.  The exact active-cell/log-coordinate results identify
that proxy with the logarithmic moving simplex whenever `t <= B`.  This
file then integrates the pointwise cell bounds, preserving the constants
`2`, `4`, and `6` in dimensions one, two, and three.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## Joint measurability in the outer parameter -/













/-! ## Measurable fixed-box proxies -/

def fourFiveActivePhysicalProxyOne
    (y B : Nat) (t : Real) : Real :=
  ∫ x in (y : Real)..(B : Real),
    fourFiveLogLogLebesgueDensity x *
      fourFiveRealMovingSimplexKernelOne y y
        (fourFiveRealLogCoordinate y t) x

def fourFiveActivePhysicalProxyTwo
    (y B : Nat) (t : Real) : Real :=
  ∫ x in (y : Real)..(B : Real),
    ∫ z in (y : Real)..(B : Real),
      fourFiveLogLogLebesgueDensity x *
        fourFiveLogLogLebesgueDensity z *
          fourFiveRealMovingSimplexKernelTwo y y
            (fourFiveRealLogCoordinate y t) x z

def fourFiveActivePhysicalProxyThree
    (y B : Nat) (t : Real) : Real :=
  ∫ x in (y : Real)..(B : Real),
    ∫ z in (y : Real)..(B : Real),
      ∫ w in (y : Real)..(B : Real),
        fourFiveLogLogLebesgueDensity x *
          fourFiveLogLogLebesgueDensity z *
            fourFiveLogLogLebesgueDensity w *
              fourFiveRealMovingSimplexKernelThree y y
                (fourFiveRealLogCoordinate y t) x z w







/-! ## Sampled endpoint functions and uniform finite bounds -/

def fourFiveLebesgueCellEndpointOne
    (y B : Nat) (t : Real) : Real :=
  fourFiveLebesgueCellProductOne
    (fourFiveMovingSimplexKernelOne y y
      (fourFiveRealLogCoordinate y t)) y B

def fourFiveLebesgueCellEndpointTwo
    (y B : Nat) (t : Real) : Real :=
  fourFiveLebesgueCellProductTwo
    (fourFiveMovingSimplexKernelTwo y y
      (fourFiveRealLogCoordinate y t)) y B

def fourFiveLebesgueCellEndpointThree
    (y B : Nat) (t : Real) : Real :=
  fourFiveLebesgueCellProductThree
    (fourFiveMovingSimplexKernelThree y y
      (fourFiveRealLogCoordinate y t)) y B



















/-! ## Proxy identities and pointwise quadrature bounds -/



















/-! ## Outer interval integrability -/























/-! ## Explicit outer residual bounds -/



def fourFiveLebesgueCellAggregationBudget
    (m y A B : Nat) (M : Real) : Real :=
  (1 / Real.log (y : Real)) * ((B : Real) - (A : Real)) *
    match m with
    | 0 => 0
    | 1 => 2 * fourFiveLogLogCellMeshBound y
    | 2 => 4 * fourFiveLogLogCellMeshBound y * M
    | 3 => 6 * fourFiveLogLogCellMeshBound y * M ^ 2
    | _ => 0









/-! ## Substitution into the layer and ordered-mixture ledgers -/















end Erdos390.WholePaper.BankPaperRealization

end

/- Source module: Erdos390.WholePaper.BankPaperFourFiveRealCommonDomainIdentification -/
section


/-!
# Exact common physical domain for the real last-prime endpoint

For a fixed prime prefix `q`, put `Q = prod_i q_i`.  The exact real
last-prime substitution has physical interval

`(max (Q*y) A, B]`.

This file rewrites that interval as the common outer interval `(A,B]`, with
the literal support cutoff `Q*y < t`.  The logarithmic identity

`log (t / Q) = log y * (log_y t - sum_i log_y q_i)`

then identifies the prefix summand with the moving-simplex kernel.  Finally,
finite prefix sums are commuted with the outer integral and, in dimensions
one, two, and three, the `Fin m` prefix sum is expanded into the nested
finite products already used by the product-measure telescope.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## A fixed-domain cutoff for one prefix -/

/-- The exposed last-prime kernel, extended by zero from its moving physical
interval to the common outer interval. -/
def fourFiveRealPrefixCutoffKernel
    (Q : Real) (y : Nat) (t : Real) : Real :=
  if Q * (y : Real) < t then
    1 / Real.log (t / Q)
  else 0













/-! ## Logarithmic cancellation inside one prefix summand -/

/-- The common-domain moving-simplex summand attached to one prime prefix. -/
def fourFivePrimePrefixMovingTerm
    {m : Nat} (q : Fin m -> Nat) (y : Nat) (t : Real) : Real :=
  (∏ i, ((q i : Nat) : Real)⁻¹) *
    if (∑ i, fourFiveLogCoordinate y (q i)) <
        fourFiveRealLogCoordinate y t - 1 then
      (fourFiveRealLogCoordinate y t -
        ∑ i, fourFiveLogCoordinate y (q i))⁻¹
    else 0

















/-! ## Finite prefix sums in dimensions one, two, and three -/

















/-! ## Commuting the finite prefix sum with the outer integral -/



















/-! ## Integrated product replacement and vanishing overrun -/

/-- The one-dimensional BV discrepancy after the common outer integration
has been applied. -/
def fourFivePhysicalOuterScaledBVError
    (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) * ((B : Real) - (A : Real)) *
    fourFiveReciprocalBVError y

























/-! ## Fully bounded real-endpoint bridge and factorial assembly -/









/-- The fully explicit real-endpoint error ledger.  The physical-domain and
moving/fixed errors are absent because they are exact equalities, while the
product overrun has been proved zero. -/
def fourFiveRealEndpointFullyBoundedAssemblyError
    (C : Real) (y A B : Nat) (M : Real) : Real :=
  fourFiveFactorialErrorLedger
    (fourFiveOrderedLastPrimeRealEndpointErrorLayer C 0 y A B +
      fourFiveMovingFaceProductError 0
        (fourFivePhysicalOuterScaledBVError y A B) M +
      fourFiveLebesgueCellAggregationBudget 0 y A B M)
    (fourFiveOrderedLastPrimeRealEndpointErrorLayer C 1 y A B +
      fourFiveMovingFaceProductError 1
        (fourFivePhysicalOuterScaledBVError y A B) M +
      fourFiveLebesgueCellAggregationBudget 1 y A B M)
    (fourFiveOrderedLastPrimeRealEndpointErrorLayer C 2 y A B +
      fourFiveMovingFaceProductError 2
        (fourFivePhysicalOuterScaledBVError y A B) M +
      fourFiveLebesgueCellAggregationBudget 2 y A B M)
    (fourFiveOrderedLastPrimeRealEndpointErrorLayer C 3 y A B +
      fourFiveMovingFaceProductError 3
        (fourFivePhysicalOuterScaledBVError y A B) M +
      fourFiveLebesgueCellAggregationBudget 3 y A B M)







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

/-- The factorial mass polynomial occurring in the four endpoint errors. -/
def fourFiveEndpointFactorialMassPolynomial (M : Real) : Real :=
  1 + M / 2 + M ^ 2 / 6 + M ^ 3 / 24

/-- The factorial mass polynomial occurring in both the BV and cell errors.

Indeed, after division by `2!`, `3!`, and `4!`, the coefficients
`2,4,6` become `1,2/3,1/4`. -/
def fourFiveTransferFactorialMassPolynomial (M : Real) : Real :=
  1 + 2 * M / 3 + M ^ 2 / 4





/-- One constant paying the endpoint, reciprocal-prime BV, and Lebesgue-cell
parts of the fully bounded assembly after they are put over `log(y)^3`. -/
def fourFiveSignedCoreAssemblyLogCubeConstant
    (C M : Real) : Real :=
  3 * C * fourFiveEndpointFactorialMassPolynomial M +
    (5 * fullReciprocalSumUniformConstant + 1) *
      fourFiveTransferFactorialMassPolynomial M







/-! ## Freezing the common continuum kernel -/







/-! ### Quotient endpoints and ideal physical lengths -/





/-! ## Exact `K0+1` balance and signed three-interval algebra -/







/-! ## Positive cutoff-band algebra -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalClippedIntervalGeometry -/
section


/-!
# Endpoint geometry for the three clipped signed exceptional intervals

This file isolates the elementary endpoint work needed before applying the
four/five rough-interval estimate to the three physical intervals in the
signed exceptional core.

There are two separate layers.

* A common endpoint certificate controls the literal real exceptional floor,
  the fifth-power rough chamber, and the padded logarithmic coordinate range.
* For a fixed positive smooth core, each clipped physical interval is either
  empty or satisfies exactly the endpoint hypotheses consumed by the
  four/five counting and kernel-freezing adapters.

The common certificate is proved eventually from
`0 <= deltaStar < 1/18`.  In particular, the proof retains both rounding
operations: the exceptional lower endpoint is a natural floor, while the
smooth-core prefix is bounded by twice the natural ceiling
`tangentPaperExceptionalCutoff`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.PaperScaleMarkedCell

noncomputable section

namespace BankPaperRealization

/-! ## Named endpoints and the exact adapter geometry -/

def roughCanonicalExceptionalPhysicalLowerEndpoint
    (n : Nat) (deltaStar : Real) (b lo : Nat) : Nat :=
  max (lo / b)
    (roughCanonicalRealExceptionalRoughCutoff n deltaStar)

def roughCanonicalExceptionalPhysicalUpperEndpoint
    (b hi : Nat) : Nat :=
  hi / b



/-- The exact endpoint package needed by the per-interval four/five
counting theorem.  The upper scale includes the harmless `+1` used by the
paper-rate adapter. -/
structure RoughCanonicalExceptionalPhysicalIntervalGeometry
    (n : Nat) (deltaStar : Real) (b A B : Nat) : Prop where
  core_pos : 1 <= b
  core_le_cutoff :
    b <= 2 * tangentPaperExceptionalCutoff deltaStar n
  lower_pos : 1 <= A
  lower_le_upper : A <= B
  upper_le_paperScale : B <= 3 * n / b + 1
  rough_cutoff_le_lower : yNat n <= A
  omega_chamber : B < (yNat n + 1) ^ 5
  padded_log_range :
    ∀ t ∈ Set.Icc (A : Real) (B : Real),
      Real.log t / Real.log (yNat n : Real) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)

/-- The data common to all three physical intervals before division by a
smooth core. -/
structure RoughCanonicalExceptionalCommonEndpointGeometry
    (n : Nat) (deltaStar : Real) : Prop where
  exceptional_floor_pos :
    1 <= roughCanonicalRealExceptionalRoughCutoff n deltaStar
  rough_cutoff_le_exceptional_floor :
    yNat n <= roughCanonicalRealExceptionalRoughCutoff n deltaStar
  omega_cap : 3 * n < (yNat n + 1) ^ 5
  padded_log_range :
    ∀ t ∈ Set.Icc
        (roughCanonicalRealExceptionalRoughCutoff n deltaStar : Real)
        ((3 * n : Nat) : Real),
      Real.log t / Real.log (yNat n : Real) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)



/-! ## Empty-interval handling -/







/-! ## A common certificate gives every nonempty clipped interval -/







/-! ## The literal exceptional floor dominates `n^(1-deltaStar)` -/







/-! ## Padded logarithmic coordinates -/

/-- One explicit logarithmic threshold pays the upper endpoint rounding
from `3n` and the floor loss in `yNat`. -/
def roughCanonicalExceptionalPaddedLogThreshold : Real :=
  (45 / 2 : Real) *
    (Real.log 3 + (47 / 10 : Real) * Real.log 2)



/-! ## Fifth-power chamber and the eventual common certificate -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalFourFiveKernelVariation -/
section


/-!
# Discrete variation of the frozen four/five kernel

The periodic exceptional-core argument needs the prime-power variation of

`b ↦ K(log((2n)/b) / log(yNat n)) / b`.

This file proves that estimate from the already formalized uniform `C¹`
bound for `fourFiveContinuumMixtureKernel`.  The coordinate-range premise is
kept explicit: it is the elementary chamber geometry asserting that all
sampled logarithmic coordinates lie in the padded interval `[4.1,4.7]`.

No rough-number count or exceptional-core asymptotic is used here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## The literal frozen kernel -/

/-- The logarithmic coordinate at a frozen smooth core. -/
def roughCanonicalFourFiveFrozenCoordinate (n b : Nat) : Real :=
  Real.log ((2 * (n : Real)) / (b : Real)) /
    Real.log (yNat n : Real)

/-- The literal four/five continuum kernel divided by its smooth core.
The zero value is arbitrary and is never used in a positive core block. -/
def roughCanonicalFourFiveFrozenKernelWeight (n b : Nat) : Real :=
  if b = 0 then 0 else
    fourFiveContinuumMixtureKernel
      (roughCanonicalFourFiveFrozenCoordinate n b) / (b : Real)

/-! ## Compact `C¹` control -/



/-! ## Coordinate increments -/





/-! ## Finite variation algebra -/



/-! ## The literal kernel variation -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveGeometryPrecursorConnector -/
section


/-!
# Geometry precursors for the signed exceptional four/five chamber

This file supplies the elementary eventual inputs which precede the six
interval estimates in the signed exceptional four/five chamber.

* The natural exceptional cutoff is eventually at most half of `yNat`.
* Every frozen coordinate with smooth core in the deep prefix belongs to
  the padded chamber `[4.1, 4.7]`.
* The five routine scalar fields of the chamber input are packaged together.

The coordinate result is obtained directly from the existing common endpoint
geometry.  No rough-counting estimate or kernel estimate is introduced here.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.PaperPrimePowerTailRate

noncomputable section

namespace BankPaperRealization

/-! ## Separation of the natural exceptional cutoff from `yNat` -/



/-! ## Uniform padded coordinates on the deep prefix -/





/-! ## Routine chamber fields and the combined precursor -/

/-- The five scalar fields of the four/five chamber input which do not
depend on any of the six interval estimates. -/
structure RoughCanonicalSignedExceptionalFourFiveScalarBoundsAt
    (W n : Nat) (deltaStar : Real) : Prop where
  n_two : 2 <= n
  head_le_yNat : W <= yNat n
  core_cutoff_le_yNat :
    2 * tangentPaperExceptionalCutoff deltaStar n <= yNat n
  log_scale_one : 1 <= L n
  log_yNat_one : 1 <= Real.log (yNat n : Real)



/-- The scalar fields together with the stronger all-deep-core coordinate
statement form the geometry precursor to the six interval estimates. -/
structure RoughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt
    (W n : Nat) (deltaStar : Real) : Prop where
  scalar_bounds :
    RoughCanonicalSignedExceptionalFourFiveScalarBoundsAt W n deltaStar
  deep_coordinates :
    ∀ b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2),
      roughCanonicalFourFiveFrozenCoordinate n b ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveChamberConnector -/
section


/-!
# Four/five chamber connector for the signed exceptional core

This file joins the four pieces which are already formalized separately.

* The ordered four/five estimate is converted to the paper rate on every
  certified exceptional physical interval.
* The continuum kernel is frozen at the literal coordinate
  `log((2n)/b) / log(yNat n)`.
* Natural quotient lengths are compared with the three ideal balanced
  lengths.
* Three frozen deep estimates and three positive cutoff estimates are
  assembled into the signed exceptional-core chamber.

The remaining input is deliberately exposed by
`RoughCanonicalSignedExceptionalFourFiveChamberInputAt`.  It consists of
the three interval estimates after the elementary displacement and clipping
budgets, together with the padded coordinate range for the prime-power
samples of the frozen kernel.  No unproved analytic assertion is hidden in
the connector.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The geometry-facing ordered-to-rough rate -/

/-- The natural upper scale attached to a physical interval at smooth core
`b`.  It is the scale supplied by
`RoughCanonicalExceptionalPhysicalIntervalGeometry`. -/
def roughCanonicalExceptionalPhysicalRateScale (n b : Nat) : Real :=
  (3 * n / b + 1 : Nat)

/-- The fixed coefficient in the ordered-to-rough paper-rate conversion. -/
def roughCanonicalFourFiveIntervalPaperRateConstant (C : Real) : Real :=
  125 * (1 +
    fourFiveSignedCoreAssemblyLogCubeConstant C
      fourFiveCompactReciprocalMass)









/-! ## One-interval freezing and quotient normalization -/







/-! ## Three-interval certificates -/

/-- The three already-frozen, ideal-length estimates needed on a deep
smooth core. -/
structure RoughCanonicalSignedExceptionalDeepIntervalEstimate
    (K0 n b : Nat) (c deltaStar : Real)
    (Cplus Chigh Cbroad : Real) : Prop where
  upper :
    abs (((roughCanonicalExceptionalUpperPhysicalRoughInterval
          n (upperTailLength c n) deltaStar b).card : Real) -
        (fourFiveContinuumMixtureKernel
            (roughCanonicalFourFiveFrozenCoordinate n b) /
          Real.log (yNat n : Real)) *
            ((upperTailLength c n : Real) / (b : Real))) <=
      Cplus *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1)
  high :
    abs (((roughCanonicalExceptionalHighPhysicalRoughInterval
          n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real) -
        (fourFiveContinuumMixtureKernel
            (roughCanonicalFourFiveFrozenCoordinate n b) /
          Real.log (yNat n : Real)) *
            ((((K0 + 1) * upperTailLength c n : Nat) : Real) /
              (b : Real))) <=
      Chigh *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1)
  broad :
    abs (((roughCanonicalExceptionalBroadPhysicalRoughInterval
          n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real) -
        (fourFiveContinuumMixtureKernel
            (roughCanonicalFourFiveFrozenCoordinate n b) /
          Real.log (yNat n : Real)) *
            (((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
              (b : Real))) <=
      Cbroad *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1)

/-- The three positive estimates needed on the one cutoff band. -/
structure RoughCanonicalSignedExceptionalCutoffIntervalEstimate
    (K0 n b : Nat) (c deltaStar : Real)
    (Cplus Chigh Cbroad : Real) : Prop where
  upper :
    ((roughCanonicalExceptionalUpperPhysicalRoughInterval
        n (upperTailLength c n) deltaStar b).card : Real) <=
      Cplus *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1)
  high :
    ((roughCanonicalExceptionalHighPhysicalRoughInterval
        n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real) <=
      Chigh *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1)
  broad :
    ((roughCanonicalExceptionalBroadPhysicalRoughInterval
        n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real) <=
      Cbroad *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1)

/-! ## Replacing the physical upper scale by `n/b` -/





/-! ## Signed deep and cutoff bounds -/

/-- The literal error left after removing the frozen periodic main term
from one signed smooth core. -/
def roughCanonicalFourFiveSignedExceptionalCoreError
    (W K0 n b : Nat) (c deltaStar beta : Real) : Real :=
  roughCanonicalSignedExceptionalCoreMass
      n (upperTailLength c n) (K0 + 1) deltaStar
      (roughHeadCompatibleRawWeight
        W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha
          W n (upperTailLength c n) (K0 + 1) beta (L n))
        beta (L n)) b -
    ((upperTailLength c n : Real) /
      Real.log (yNat n : Real)) *
      roughHeadPeriodicCoreCoefficient W b *
        roughCanonicalFourFiveFrozenKernelWeight n b

def roughCanonicalFourFiveDeepCoreConstant
    (W K0 : Nat) (c beta Cplus Chigh Cbroad : Real) : Real :=
  4 * (Cplus +
    roughBalancedAlphaConstant W K0 c beta * Chigh +
    abs beta * Cbroad)

def roughCanonicalFourFiveCutoffCoreConstant
    (W K0 : Nat) (c beta Cplus Chigh Cbroad : Real) : Real :=
  4 * (Cplus +
    roughBalancedAlphaConstant W K0 c beta * Chigh +
    abs beta * Cbroad)









/-! ## Exact remaining chamber input -/

/-- The exact information not supplied by the present four/five library at
one value of `n`.

The deep and cutoff fields are the six interval consequences of the
displacement/clipping analysis.  The final field is the padded-coordinate
geometry needed by the already proved frozen-kernel variation theorem.
-/
structure RoughCanonicalSignedExceptionalFourFiveChamberInputAt
    (W K0 n : Nat) (c deltaStar : Real)
    (deepPlus deepHigh deepBroad
      cutoffPlus cutoffHigh cutoffBroad : Real) : Prop where
  n_two : 2 <= n
  head_le_yNat : W <= yNat n
  core_cutoff_le_yNat :
    2 * tangentPaperExceptionalCutoff deltaStar n <= yNat n
  log_scale_one : 1 <= L n
  log_yNat_one : 1 <= Real.log (yNat n : Real)
  deep_intervals :
    ∀ b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n,
      RoughCanonicalSignedExceptionalDeepIntervalEstimate
        K0 n b c deltaStar deepPlus deepHigh deepBroad
  cutoff_intervals :
    ∀ b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n,
      RoughCanonicalSignedExceptionalCutoffIntervalEstimate
        K0 n b c deltaStar cutoffPlus cutoffHigh cutoffBroad
  variation_coordinates :
    ∀ p : Nat, p.Prime -> W < p ->
      ∀ k ∈ positiveExponents
          (tangentPaperExceptionalCutoff deltaStar n / 2),
        ∀ m ∈ Finset.Icc 1
            ((tangentPaperExceptionalCutoff deltaStar n / 2) / p ^ k),
          roughCanonicalFourFiveFrozenCoordinate n (p ^ k * m) ∈
            Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)

/-- Eventual form of the exact remaining six interval estimates and the
prime-power coordinate geometry. -/
def RoughCanonicalSignedExceptionalFourFiveRemainingInputs
    (W K0 : Nat) (c deltaStar : Real)
    (deepPlus deepHigh deepBroad
      cutoffPlus cutoffHigh cutoffBroad : Real) : Prop :=
  ∀ᶠ n : Nat in atTop,
    RoughCanonicalSignedExceptionalFourFiveChamberInputAt
      W K0 n c deltaStar
      deepPlus deepHigh deepBroad cutoffPlus cutoffHigh cutoffBroad

/-! ## Chamber and final residual assembly -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepDisplacementConnector -/
section


/-!
# Frozen-coordinate displacement on the deep exceptional core

This file isolates the displacement input used when the continuum mixture
kernel is frozen at

`log((2n)/b) / log(yNat n)`.

Natural quotient rounding contributes one unit at each lower endpoint.
On the deep prefix, the existing bound
`tangentPaperExceptionalCutoff <= n / L^2` absorbs that unit.  The upper and
high intervals then have displacement `O(1/L^2)`, while the broad interval
has displacement `O(1/L)`.

Only endpoint arithmetic and previously proved scale bounds occur here.
No interval count and no clipping-length estimate is asserted.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A normalized logarithmic displacement lemma -/



/-! ## Fixed rate constants -/

def roughCanonicalFourFiveDeepUpperDisplacementConstant
    (c : Real) : Real :=
  15 * (c + 1)

def roughCanonicalFourFiveDeepHighDisplacementConstant
    (K0 : Nat) (c : Real) : Real :=
  15 * (((K0 + 1 : Nat) : Real) * c + 1)

def roughCanonicalFourFiveDeepBroadDisplacementConstant : Real :=
  15







/-! ## Elementary deep-prefix scale reductions -/







/-! ## Finite displacement bounds in adapter form -/







/-! ## Simultaneous adapter-facing packaging -/

structure RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
    (K0 n b : Nat) (c deltaStar : Real) : Prop where
  upper_D_nonneg :
    0 <= roughCanonicalFourFiveDeepUpperDisplacementConstant c / L n ^ 2
  upper_displacement :
    ∀ t ∈ Set.Icc
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b (2 * n) : Real)
        (roughCanonicalExceptionalPhysicalUpperEndpoint
          b (2 * n + upperTailLength c n) : Real),
      abs (Real.log t / Real.log (yNat n : Real) -
          roughCanonicalFourFiveFrozenCoordinate n b) <=
        roughCanonicalFourFiveDeepUpperDisplacementConstant c / L n ^ 2
  high_D_nonneg :
    0 <=
      roughCanonicalFourFiveDeepHighDisplacementConstant K0 c / L n ^ 2
  high_displacement :
    ∀ t ∈ Set.Icc
        (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
          (2 * n - (K0 + 1) * upperTailLength c n) : Real)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) : Real),
      abs (Real.log t / Real.log (yNat n : Real) -
          roughCanonicalFourFiveFrozenCoordinate n b) <=
        roughCanonicalFourFiveDeepHighDisplacementConstant K0 c / L n ^ 2
  broad_D_nonneg :
    0 <= roughCanonicalFourFiveDeepBroadDisplacementConstant / L n
  broad_displacement :
    ∀ t ∈ Set.Icc
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b n : Real)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b
          (2 * n - (K0 + 1) * upperTailLength c n) : Real),
      abs (Real.log t / Real.log (yNat n : Real) -
          roughCanonicalFourFiveFrozenCoordinate n b) <=
        roughCanonicalFourFiveDeepBroadDisplacementConstant / L n









/-! ## Eventual simultaneous form -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepEndpointErrorConnector -/
section


/-!
# Endpoint-length errors on the deep exceptional core

The three physical intervals use natural quotient endpoints.  Their lower
endpoints are additionally clipped by the literal real exceptional floor.
This file separates the two effects at a deep smooth core.

* The upper and high lower endpoints are eventually not moved by clipping.
  Their literal lengths therefore differ from the ideal quotient lengths by
  at most one.
* The broad lower endpoint remains clipped.  Its clipping excess is bounded
  directly, and its complete endpoint-length error is
  `O(Z / L + 1)`, where
  `Z = roughCanonicalExceptionalPhysicalRateScale n b`.

The broad statement deliberately retains the `max` in the literal endpoint.
No eventual broad no-clipping assertion is made.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A generic clipping triangle -/



/-! ## Deep upper/high no-clipping -/









/-! ## The clipped broad endpoint -/





/-! ## Adapter-facing package -/

/-- The three endpoint-length inputs on one deep smooth core.  Only the two
short intervals record no-clipping; the broad field retains its clipped
lower endpoint. -/
structure RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
    (K0 n b : Nat) (c deltaStar : Real) : Prop where
  upper_noClipping :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
      (2 * n) / b
  high_noClipping :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
      (2 * n - (K0 + 1) * upperTailLength c n) / b
  upper_length_error :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n + upperTailLength c n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b (2 * n) : Nat) : Real) -
        (upperTailLength c n : Real) / (b : Real)) <= 1
  high_length_error :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
            (2 * n - (K0 + 1) * upperTailLength c n) : Nat) : Real) -
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real)) <= 1
  broad_length_error :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n - (K0 + 1) * upperTailLength c n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b n : Nat) : Real) -
        ((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real)) <=
      2 *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1)









/-! ## Eventual deep-core form -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepIntervalEstimateConnector -/
section


/-!
# Deep exceptional four/five interval estimates

This connector assembles the three inputs already isolated for a deep
smooth core:

* the uniform arithmetic `Z / L^3` estimate;
* freezing at the literal coordinate, using the uniform compact `C¹`
  kernel bound and the deep displacement package;
* the literal endpoint-length errors.

The upper and high intervals use their eventual no-clipping conclusions.
The broad interval continues to use its clipped lower endpoint.  If that
clipping passes the broad upper endpoint, the literal interval is empty and
the same endpoint budget controls the removed frozen main term.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Algebraic rate absorption -/





/-! ## Generic one-interval assemblers -/

def roughCanonicalFourFiveDeepShortEstimateConstant
    (P C D a : Real) : Real :=
  P + 5 * C * D * (2 * a + 1) + 5 * C

def roughCanonicalFourFiveDeepBroadEstimateConstant
    (P C D : Real) : Real :=
  P + 25 * C * D + 10 * C

















/-! ## The three fixed deep constants -/

def roughCanonicalFourFiveDeepUpperEstimateConstant
    (P C c : Real) : Real :=
  roughCanonicalFourFiveDeepShortEstimateConstant P C
    (roughCanonicalFourFiveDeepUpperDisplacementConstant c) c

def roughCanonicalFourFiveDeepHighEstimateConstant
    (K0 : Nat) (P C c : Real) : Real :=
  roughCanonicalFourFiveDeepShortEstimateConstant P C
    (roughCanonicalFourFiveDeepHighDisplacementConstant K0 c)
    (((K0 + 1 : Nat) : Real) * c)

def roughCanonicalFourFiveDeepBroadFinalEstimateConstant
    (P C : Real) : Real :=
  roughCanonicalFourFiveDeepBroadEstimateConstant P C
    roughCanonicalFourFiveDeepBroadDisplacementConstant







/-! ## Finite three-interval assembly -/



/-! ## Eventual three-interval package -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveCutoffIntervalPrecursorConnector -/
section


/-!
# Positive cutoff-interval precursor for the signed four/five chamber

The cutoff band does not need a frozen main term.  On every nonempty
geometry-certified interval we freeze at the fixed padded endpoint `4.1`,
choose ideal length zero, and charge the literal interval span as endpoint
error.  The choices

`u0 = 41/10`, `D = 3/5`, `idealLength = 0`

therefore turn the existing freezing adapter into a positive cardinality
bound.  Empty intervals contribute zero.

This file also proves the generic clipped-span estimate and scales the upper
and high spans to `Z/L^2`, and the broad span to `Z/L`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Generic clipped spans -/





/-! ## Freezing at the fixed padded endpoint -/



/-! ## Span scaling -/









/-! ## Three cutoff constants -/

def roughCanonicalFourFiveCutoffUpperEstimateConstant
    (P Ckernel c : Real) : Real :=
  P + (8 / 5 : Real) * Ckernel * (10 * c + 5)

def roughCanonicalFourFiveCutoffHighEstimateConstant
    (K0 : Nat) (P Ckernel c : Real) : Real :=
  P + (8 / 5 : Real) * Ckernel *
    (10 * (((K0 + 1 : Nat) : Real) * c) + 5)

def roughCanonicalFourFiveCutoffBroadEstimateConstant
    (P Ckernel : Real) : Real :=
  P + 8 * Ckernel







/-! ## Finite geometry-or-empty cutoff assembly -/



/-! ## Eventual cutoff estimates -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSelectorDeficitPaperRateClosureConnector -/
section


/-!
# Honest paper-rate closure for the canonical selector deficit

The literal Post-Hfit structured pre-selector is already known to have the
unconditional expansion

`complete signed residual - source/raw defect - placement moment`.

There are two mathematically different changes hidden in the source/raw
defect:

* the actual global source versus the correction installed on guarded
  postcharge pools;
* the guarded postcharge correction versus the older raw-pool correction.

The second change is the guarded/raw defect isolated in
`BankPaperCanonicalGuardedRawCorrectionMomentDefectConnector`.  This file
splits the source/raw defect into those two literal finite differences and
keeps both of them visible.  In particular, no guarded-to-raw equality is
assumed.

The quantitative interface has two layers.  A pointwise theorem combines
the four signed-residual component bounds with paper-rate bounds for the two
implementation defects and the structured-placement moment.  An eventual
theorem closes the exceptional, raw-row-correction, and guard terms from
the existing rate theorems; only the raw signed residual remains as an
analytic input at that layer.  Thus downstream source-specific work can see
exactly which medium-prime estimates remain.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The two independent implementation defects -/







/-! ## Exact seven-term selector decomposition -/





/-! ## Named remaining paper-rate inputs -/

/-- Paper-rate input for the raw upper-minus-lower signed valuation
residual at the balanced physical depth. -/
def RoughCanonicalBalancedRawSignedValuationResidualBound
    (W n K0 : Nat) (c beta : Real) (p : Nat) (bound : Real) : Prop :=
  abs (roughCanonicalRawSignedValuationResidual n
    (upperTailLength c n) (K0 + 1)
    (roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
      (roughHeadBalancedAlpha W n (upperTailLength c n)
        (K0 + 1) beta (L n))
      beta (L n)) p) <= bound



/-! ## Pointwise paper-rate closure -/









/-! ## Eventual closure of the generic four-term residual -/

/-- The balanced four-term residual without any source-specific structured
data.  This is the B-free specialization to which the existing exceptional,
raw-row-correction, and aggregate-guard rate theorems apply directly. -/
def roughCanonicalBalancedCompleteSignedResidual
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (W K0 : Nat)
    {left right : Nat -> Nat} {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar beta : Real) (p : Nat) : Real :=
  roughCanonicalCompleteSignedResidual
    (roughCanonicalRawSignedValuationResidual n
      (upperTailLength c n) (K0 + 1)
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)) p)
    (roughCanonicalSignedExceptionalResidual n
      (upperTailLength c n) (K0 + 1) deltaStar
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)) p)
    (roughCanonicalAggregateRawRowCorrection W n
      (upperTailLength c n) (K0 + 1) deltaStar
      (roughHeadBalancedAlpha W n (upperTailLength c n)
        (K0 + 1) beta (L n))
      beta (L n) p)
    (R.roughCanonicalAggregateGuardResidual certificate deltaStar
      (K0 + 1)
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)) p)





end BankPaperRealization

end

end Erdos390.WholePaper

end


