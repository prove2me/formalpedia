-- Prove2me | Definitions.Def_erdos390_analytic_foundations_002
-- name    : erdos390_analytic_foundations_002
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T14:45:01.242912+00:00
-- url     : https://prove2.me/theorems/3e116753-d4d4-435e-ab1a-d2f1652c72ca
-- title:
--   Weighted prime bands and guarded bridge data
-- statement:
--   This bundle defines finite weighted prime-band geometry and the literal guarded bridge sample used for moment fitting. It includes structured samples indexed by head tag and physical sign, baseline allocations, bridge coordinates and statistics, covariance blocks, nuisance regression and Schur-complement maps, barycentric targets, and the effective parameter norm.
--
--   For positive prime weights $w_p$, coordinates $t_p$, and a nonempty fibre $P_j$ in each band $j$, its mass and center are
--   $$m_j=\sum_{p\in P_j}w_p,\qquad c_j=\frac{\sum_{p\in P_j}w_pt_p}{m_j},\qquad \langle x,z\rangle_m=\sum_jm_jx_jz_j.$$
--   The band gauge is the subspace defined by $\langle c,q\rangle_m=0$. Bridge coordinates separate main band/slow variables from physical/head nuisance variables; the effective size combines the prime-coefficient supremum norm, nuisance norm and absolute slow coordinate.
--
--   The data structures make physical intervals, guard deletion, head-pattern separation and target margins explicit. They are interfaces for subsequent existence and uniform-estimate theorems, rather than an assertion that every choice of bridge data admits a fitted path.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperBridgeFit.lean; grouped definitions extracted from multiple source modules at this commit, including Erdos390.Lemma84, Erdos390.Full.ArithmeticBandGeometry, Erdos390.Full.CoarseMixture, with the remaining originating modules identified by source-module comments in the definition body.

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_001


/- Source module: Erdos390.Lemma84 -/
section


/-!
# The finite-dimensional core of Lemma 8.4

This file formalizes only the algebraic part of the moving-low-cell
arithmetic quotient argument.  The Poisson--Dickman gap, prime
quadrature, and marked covariance estimates occur below as fields of an
explicit input structure.  Thus this file contains no postulate claiming
those analytic results.
-/

namespace Erdos390.Lemma84

open scoped BigOperators

noncomputable section

section WeightedBands

variable {Prime Band : Type*}
variable [Fintype Prime] [Fintype Band]
variable [DecidableEq Prime] [DecidableEq Band]

/-- Finite prime weights, their logarithmic coordinates, and a partition
into bands. -/
structure WeightedBandData (Prime Band : Type*) [Fintype Prime]
    [Fintype Band] [DecidableEq Prime] [DecidableEq Band] where
  weight : Prime → ℝ
  weight_pos : ∀ p, 0 < weight p
  coord : Prime → ℝ
  band : Prime → Band
  fiber_nonempty : ∀ j, ∃ p, band p = j

namespace WeightedBandData

variable (d : WeightedBandData Prime Band)

def fiber (j : Band) : Finset Prime :=
  Finset.univ.filter fun p => d.band p = j

def mass (j : Band) : ℝ :=
  ∑ p ∈ d.fiber j, d.weight p

def center (j : Band) : ℝ :=
  (∑ p ∈ d.fiber j, d.weight p * d.coord p) / d.mass j

def bandInner (x y : Band → ℝ) : ℝ :=
  ∑ j, d.mass j * x j * y j

def bandNormSq (x : Band → ℝ) : ℝ :=
  d.bandInner x x

def inGauge (q : Band → ℝ) : Prop :=
  d.bandInner d.center q = 0

def lift (b : Band → ℝ) (p : Prime) : ℝ :=
  b (d.band p)

def primeInner (x y : Prime → ℝ) : ℝ :=
  ∑ p, d.weight p * x p * y p

def primeNormSq (x : Prime → ℝ) : ℝ :=
  d.primeInner x x

def cellDeviation (p : Prime) : ℝ :=
  d.center (d.band p) - d.coord p

def cellVariance : ℝ :=
  d.primeNormSq d.cellDeviation

def centerEnergy : ℝ :=
  d.bandNormSq d.center

def gaugeCoefficient (b : Band → ℝ) : ℝ :=
  d.bandInner d.center b / d.centerEnergy

def gaugePart (b : Band → ℝ) (j : Band) : ℝ :=
  b j - d.gaugeCoefficient b * d.center j

def coordEnergy : ℝ :=
  d.primeNormSq d.coord

def residual (b : Band → ℝ) (mu : ℝ) (p : Prime) : ℝ :=
  d.lift b p - mu * d.coord p

def physicalSq (b : Band → ℝ) (mu : ℝ) : ℝ :=
  d.primeNormSq (d.residual b mu)

def physicalMinimizer (b : Band → ℝ) : ℝ :=
  d.primeInner d.coord (d.lift b) / d.coordEnergy

def primeQuadratic (E : Prime → Prime → ℝ) (c : Prime → ℝ) : ℝ :=
  ∑ p, ∑ r, E p r * c p * c r





















theorem mem_fiber_iff {p : Prime} {j : Band} :
    p ∈ d.fiber j ↔ d.band p = j := by
  simp [fiber]

theorem mass_pos (j : Band) : 0 < d.mass j := by
  apply Finset.sum_pos
  · intro p hp
    exact d.weight_pos p
  · obtain ⟨p, hp⟩ := d.fiber_nonempty j
    exact ⟨p, by simp [fiber, hp]⟩







































/-!
## Conditional bridge

The next structure is the exact boundary between the finite argument and
the presently external analytic work.  Its fields are a leading
Poisson--Dickman/quadrature form, an actual marked covariance form, the
nuisance loss, and quantitative comparisons between them.  No field is
the desired quotient conclusion.
-/

structure BridgeInputs where
  leadingForm : (Prime → ℝ) → ℝ
  actualVariance : (Prime → ℝ) → ℝ
  nuisanceLoss : (Prime → ℝ) → ℝ
  schurForm : (Band → ℝ) → ℝ
  gapConstant : ℝ
  covarianceError : ℝ
  nuisanceError : ℝ
  gapConstant_nonneg : 0 ≤ gapConstant
  covarianceError_nonneg : 0 ≤ covarianceError
  nuisanceError_nonneg : 0 ≤ nuisanceError
  leading_gap : ∀ c,
    d.primeInner d.coord c = 0 →
      gapConstant * d.primeNormSq c ≤ leadingForm c
  covariance_comparison : ∀ c,
    |actualVariance c - leadingForm c| ≤
      covarianceError * d.primeNormSq c
  nuisance_bound : ∀ c,
    nuisanceLoss c ≤ nuisanceError * d.primeNormSq c
  exact_null_schur : ∀ b mu,
    schurForm b =
      actualVariance (d.residual b mu) -
        nuisanceLoss (d.residual b mu)





/-- The sup norm on a nonempty finite band space. -/
def bandSupNorm [Nonempty Band] (x : Band → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => |x j|

/-- The projected inverse is intentionally a separate contract.  In the
paper it is supplied by the continuum `L∞` inverse, arithmetic transfer,
and the stable projected-Schur perturbation lemma; it is not inferred
from the quadratic quotient gap. -/
structure ProjectedInverseContract [Nonempty Band] where
  operator : (Band → ℝ) → (Band → ℝ)
  inverse : (Band → ℝ) → (Band → ℝ)
  boundConstant : ℝ
  boundConstant_nonneg : 0 ≤ boundConstant
  operator_maps_gauge : ∀ q, d.inGauge q → d.inGauge (operator q)
  inverse_maps_gauge : ∀ q, d.inGauge q → d.inGauge (inverse q)
  left_inverse_on_gauge : ∀ q, d.inGauge q → inverse (operator q) = q
  right_inverse_on_gauge : ∀ q, d.inGauge q → operator (inverse q) = q
  inverse_bound : ∀ q, d.inGauge q →
    bandSupNorm (inverse q) ≤ boundConstant * bandSupNorm q



end WeightedBandData

end WeightedBands

end

end Erdos390.Lemma84

end

/- Source module: Erdos390.Full.ArithmeticBandGeometry -/
section


/-!
# Exact arithmetic band geometry

This instantiates the finite weighted-band algebra with the paper's actual
prime set, harmonic weights `1/p`, and logarithmic coordinates `t_p`.  In
particular the centering identity is arithmetic, not a continuum identity;
this is the correction required by the audit of Section 8.4.
-/

namespace Erdos390.Full

noncomputable section

open ArithmeticModel

namespace ArithmeticBandGeometry

abbrev BandPrime (n W : ℕ) := {p : ℕ // p ∈ primeBand n W}

/-- A permitted finite partition of the actual prime band. -/
structure Partition (n W : ℕ) (Band : Type*) [Fintype Band] where
  band : BandPrime n W → Band
  fiber_nonempty : ∀ j, ∃ p, band p = j

namespace Partition

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]

instance : Fintype (BandPrime n W) :=
  Fintype.ofFinset (primeBand n W) (fun _ ↦ Iff.rfl)

instance : DecidableEq (BandPrime n W) := inferInstance

def data (P : Partition n W Band) :
    Erdos390.Lemma84.WeightedBandData (BandPrime n W) Band where
  weight := fun p ↦ 1 / (p.1 : ℝ)
  weight_pos := by
    intro p
    exact one_div_pos.mpr (by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos)
  coord := fun p ↦ tPrime n p.1
  band := P.band
  fiber_nonempty := P.fiber_nonempty

abbrev mass (P : Partition n W Band) (j : Band) : ℝ :=
  P.data.mass j

abbrev center (P : Partition n W Band) (j : Band) : ℝ :=
  P.data.center j

abbrev variance (P : Partition n W Band) : ℝ :=
  P.data.cellVariance

abbrev centerEnergy (P : Partition n W Band) : ℝ :=
  P.data.centerEnergy





def minimizingMu (P : Partition n W Band) (lambda : ℝ) : ℝ :=
  lambda * P.centerEnergy / (P.centerEnergy + P.variance)











end Partition

end ArithmeticBandGeometry

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.CoarseMixture -/
section


/-!
# Canonical coarse mixtures

Given an actual fine finite law and a map to finitely many reserved cells,
the coarse weights and conditional-mean pattern vectors are defined by finite
sums.  This removes the need to assume the law-of-total-variance connection
used in the nuisance covariance argument.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace CanonicalCoarseMixture

variable {Fine Cell Nuisance : Type*} [Fintype Fine] [Fintype Cell]
  [DecidableEq Cell]
  [NormedAddCommGroup Nuisance] [InnerProductSpace ℝ Nuisance]

def fiberWeight (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) : ℝ :=
  ∑ f ∈ (Finset.univ : Finset Fine) with cell f = c, fine.weight f

def fiberMoment (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) : Nuisance :=
  ∑ f ∈ (Finset.univ : Finset Fine) with cell f = c,
    fine.weight f • fine.pattern f

def conditionalPattern (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) : Nuisance :=
  (fiberWeight fine cell c)⁻¹ • fiberMoment fine cell c

omit [Fintype Cell] in
theorem fiberWeight_nonneg (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) :
    0 ≤ fiberWeight fine cell c := by
  exact Finset.sum_nonneg fun f hf ↦ fine.weight_nonneg f

theorem fiberWeight_sum (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) :
    ∑ c, fiberWeight fine cell c = 1 := by
  change (∑ c, ∑ f ∈ (Finset.univ : Finset Fine) with cell f = c,
    fine.weight f) = 1
  rw [Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset Fine))
    (t := (Finset.univ : Finset Cell))
    (g := cell) (fun f _ ↦ Finset.mem_univ (cell f)) fine.weight]
  exact fine.weight_sum

def coarse (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) : PatternMixture Cell Nuisance where
  weight := fiberWeight fine cell
  weight_nonneg := fiberWeight_nonneg fine cell
  weight_sum := fiberWeight_sum fine cell
  pattern := conditionalPattern fine cell

@[simp] theorem coarse_weight (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) :
    (coarse fine cell).weight c = fiberWeight fine cell c := rfl

@[simp] theorem coarse_pattern (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) :
    (coarse fine cell).pattern c = conditionalPattern fine cell c := rfl

omit [Fintype Cell] in
theorem inner_fiberMoment (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) (x : Nuisance) :
    inner ℝ x (fiberMoment fine cell c) =
      ∑ f ∈ (Finset.univ : Finset Fine) with cell f = c,
        fine.weight f * inner ℝ x (fine.pattern f) := by
  simp only [fiberMoment, inner_sum, inner_smul_right]

/-- The coarse conditional-mean certificate follows from the definitions,
provided every coarse cell has positive mass. -/
def certificate (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (hpos : ∀ c, 0 < fiberWeight fine cell c) :
    PatternMixture.CoarseMeanCertificate fine (coarse fine cell) where
  cell := cell
  cell_mass := fun _ ↦ rfl
  cell_firstMoment := by
    intro c x
    rw [← inner_fiberMoment fine cell c x]
    simp only [coarse_weight, coarse_pattern, conditionalPattern,
      inner_smul_right]
    field_simp [ne_of_gt (hpos c)]

end CanonicalCoarseMixture

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.StableInverse -/
section


/-!
# Stable inversion under an operator perturbation

This is the quantitative finite-dimensional perturbation lemma needed after
the continuum inverse has been transferred to the arithmetic gauge space.
It does not assume invertibility of the perturbed operator.  Instead it
derives it from a proved inverse for the reference operator and an operator
error smaller than the reciprocal inverse bound.
-/

namespace Erdos390.Full

noncomputable section

namespace StableInverse

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ X] in
theorem reference_control
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) (x : X) :
    (1 - C * delta) * ‖x‖ ≤ C * ‖(A + E) x‖ := by
  have hA : ‖x‖ ≤ C * ‖A x‖ := by
    calc
      ‖x‖ = ‖Ainv (A x)‖ := by rw [hleft x]
      _ ≤ C * ‖A x‖ := hinv (A x)
  have hsplit : ‖A x‖ ≤ ‖(A + E) x‖ + ‖E x‖ := by
    have hid : A x = (A + E) x - E x := by
      simp
    rw [hid]
    exact norm_sub_le _ _
  have hscaled : C * ‖A x‖ ≤
      C * (‖(A + E) x‖ + ‖E x‖) :=
    mul_le_mul_of_nonneg_left hsplit hC
  have herrscaled : C * (‖(A + E) x‖ + ‖E x‖) ≤
      C * (‖(A + E) x‖ + delta * ‖x‖) := by
    apply mul_le_mul_of_nonneg_left _ hC
    simpa [add_comm] using add_le_add_left (herror x) ‖(A + E) x‖
  nlinarith

omit [FiniteDimensional ℝ X] in
theorem perturbed_injective
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) :
    Function.Injective (A + E) := by
  intro x y hxy
  have hzero : (A + E) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hcontrol := reference_control A Ainv E C delta hC
    hleft hinv herror (x - y)
  rw [hzero, norm_zero, mul_zero] at hcontrol
  have hcoef : 0 < 1 - C * delta := sub_pos.mpr hsmall
  have hnorm : ‖x - y‖ = 0 := by
    apply le_antisymm
    · nlinarith [norm_nonneg (x - y)]
    · exact norm_nonneg _
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The continuous linear equivalence represented by the perturbed operator.
Its existence is a conclusion, not a hypothesis. -/
def perturbedEquiv
    (A Ainv E : X →L[ℝ] X) (C delta : ℝ)
    (hC : 0 ≤ C)
    (hsmall : C * delta < 1)
    (hleft : ∀ x, Ainv (A x) = x)
    (hinv : ∀ y, ‖Ainv y‖ ≤ C * ‖y‖)
    (herror : ∀ x, ‖E x‖ ≤ delta * ‖x‖) : X ≃L[ℝ] X :=
  (LinearEquiv.ofInjectiveEndo ((A + E : X →L[ℝ] X) : X →ₗ[ℝ] X)
    (perturbed_injective A Ainv E C delta hC hsmall
      hleft hinv herror)).toContinuousLinearEquiv







end StableInverse

end

end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperBridgeFit -/
section


/-!
# The finite arithmetic data in the bridge fit

This file instantiates the nonlinear finite-family layer with the actual
objects appearing in Lemmas 8.5--8.6 and Proposition 8.7: guarded smooth
structured cells, arithmetic prime bands, valuation statistics, the physical
logarithm, centered head indicators, and the compensated slow score.

The sample is the tagged disjoint union of the paper's cells.  Tagging is the
formal counterpart of the disjointification performed before normalization;
the underlying integer remains available as `Sample.value`.

All statements in this file are finite identities.  Asymptotic marked-smooth
estimates are not silently inserted as hypotheses equivalent to the desired
fit.  Where a later analytic estimate is still needed, the exact finite
quantity it must bound is exposed explicitly.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full

noncomputable section

open ArithmeticModel StructuredCells HeadPattern

namespace PaperBridgeFit

/-- The two separated physical pools in the baseline construction. -/
inductive PhysicalSign
  | minus
  | plus
  deriving DecidableEq, Fintype, Inhabited

/-- A head-pattern/physical-pool cell. -/
abbrev Cell (Head : Type*) := Head × PhysicalSign

/-- Exact finite data defining the paper's guarded active sample `S_n`.
The smoothness cutoff is the actual `floor (n^(2/9))`. -/
structure StructuredSampleData (Head : Type*) [Fintype Head] where
  n : ℕ
  W : ℕ
  pattern : Head → HeadPattern.Pattern
  lo : PhysicalSign → ℕ
  hi : PhysicalSign → ℕ
  lo_le_hi : ∀ sigma, lo sigma ≤ hi sigma
  physical_separated : hi .minus < lo .plus
  guards : Finset ℕ
  cell_nonempty : ∀ c : Cell Head,
    ((structuredCell (pattern c.1) (lo c.2) (hi c.2) (yNat n)) \
      guards).Nonempty

namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]

/-- The actual guard-deleted structured cell `C_{e,sigma,n}`. -/
def cellFinset (D : StructuredSampleData Head) (c : Cell Head) : Finset ℕ :=
  structuredCell (D.pattern c.1) (D.lo c.2) (D.hi c.2)
      (yNat D.n) \ D.guards

/-- Members of one actual structured cell. -/
abbrev SampleAt (D : StructuredSampleData Head) (c : Cell Head) :=
  {m : ℕ // m ∈ D.cellFinset c}

instance sampleAtFintype (D : StructuredSampleData Head) (c : Cell Head) :
    Fintype (D.SampleAt c) :=
  Fintype.ofFinset (D.cellFinset c) (fun _ => Iff.rfl)

instance sampleAtDecidableEq (D : StructuredSampleData Head) (c : Cell Head) :
    DecidableEq (D.SampleAt c) := inferInstance

/-- The tagged disjoint union `S_n = disjoint union C_{e,sigma,n}`. -/
abbrev Sample (D : StructuredSampleData Head) :=
  Sigma D.SampleAt

instance sampleFintype (D : StructuredSampleData Head) : Fintype D.Sample :=
  inferInstance

noncomputable instance sampleDecidableEq (D : StructuredSampleData Head) :
    DecidableEq D.Sample := Classical.decEq D.Sample

/-- The cell tag of a sample. -/
def cellOf (D : StructuredSampleData Head) (m : D.Sample) : Cell Head :=
  m.1

/-- The underlying positive integer. -/
def value (D : StructuredSampleData Head) (m : D.Sample) : ℕ :=
  m.2.1

theorem value_mem_cell (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ∈ D.cellFinset (D.cellOf m) :=
  m.2.2

theorem value_pos (D : StructuredSampleData Head) (m : D.Sample) :
    0 < D.value m := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact StructuredCells.pos_of_mem_smoothInterval
    (mem_structuredCell.mp hm).1

theorem lo_lt_value (D : StructuredSampleData Head) (m : D.Sample) :
    D.lo (D.cellOf m).2 < D.value m := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).1

theorem value_le_hi (D : StructuredSampleData Head) (m : D.Sample) :
    D.value m ≤ D.hi (D.cellOf m).2 := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1

theorem value_matches_head (D : StructuredSampleData Head) (m : D.Sample) :
    (D.pattern (D.cellOf m).1).Matches (D.value m) := by
  have hm : D.value m ∈ structuredCell
      (D.pattern (D.cellOf m).1) (D.lo (D.cellOf m).2)
      (D.hi (D.cellOf m).2) (yNat D.n) :=
    (Finset.mem_sdiff.mp (D.value_mem_cell m)).1
  exact (mem_structuredCell.mp hm).2





theorem sampleAt_card_pos (D : StructuredSampleData Head) (c : Cell Head) :
    0 < Fintype.card (D.SampleAt c) := by
  rw [Fintype.card_pos_iff]
  obtain ⟨m, hm⟩ := D.cell_nonempty c
  exact ⟨⟨m, hm⟩⟩

end StructuredSampleData

/-- Explicit baseline masses, uniform within each structured cell as in
equation (8.7) of the paper. -/
structure BaselineAllocation
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) where
  cellMass : Cell Head → ℝ
  cellMass_pos : ∀ c, 0 < cellMass c

namespace BaselineAllocation

variable {Head : Type*} [Fintype Head]
  {D : StructuredSampleData Head}

/-- The paper's active mass `q_n`. -/
def totalMass (A : BaselineAllocation D) : ℝ :=
  ∑ c, A.cellMass c

theorem totalMass_pos [Nonempty Head] (A : BaselineAllocation D) :
    0 < A.totalMass := by
  exact Finset.sum_pos (fun c _ => A.cellMass_pos c)
    (Finset.univ_nonempty)

/-- The exact coordinate realization
`z_m^0 = q_{e,sigma,n} / #C_{e,sigma,n}`. -/
def baseWeight (A : BaselineAllocation D) (m : D.Sample) : ℝ :=
  A.cellMass (D.cellOf m) /
    Fintype.card (D.SampleAt (D.cellOf m))

theorem baseWeight_pos (A : BaselineAllocation D) (m : D.Sample) :
    0 < A.baseWeight m := by
  exact div_pos (A.cellMass_pos (D.cellOf m)) (by
    exact_mod_cast D.sampleAt_card_pos (D.cellOf m))

theorem baseWeight_nonneg (A : BaselineAllocation D) (m : D.Sample) :
    0 ≤ A.baseWeight m :=
  le_of_lt (A.baseWeight_pos m)

/-- Summing the explicit uniform weights recovers exactly `q_n`. -/
theorem baseWeight_sum (A : BaselineAllocation D) :
    ∑ m, A.baseWeight m = A.totalMass := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [baseWeight, StructuredSampleData.cellOf]
  have hcard : (Fintype.card (D.SampleAt c) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (D.sampleAt_card_pos c))
  change (∑ _ : D.SampleAt c,
    A.cellMass c / (Fintype.card (D.SampleAt c) : ℝ)) = A.cellMass c
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

/-- Normalized mass of one reserved cell. -/
def normalizedCellMass (A : BaselineAllocation D) (c : Cell Head) : ℝ :=
  A.cellMass c / A.totalMass

theorem normalizedCellMass_pos [Nonempty Head]
    (A : BaselineAllocation D) (c : Cell Head) :
    0 < A.normalizedCellMass c :=
  div_pos (A.cellMass_pos c) A.totalMass_pos

theorem normalizedCellMass_sum [Nonempty Head] (A : BaselineAllocation D) :
    ∑ c, A.normalizedCellMass c = 1 := by
  simp only [normalizedCellMass]
  rw [← Finset.sum_div, totalMass]
  exact div_self (ne_of_gt A.totalMass_pos)

end BaselineAllocation

/-- Coordinates used in the simultaneous nonlinear fit.  The gauge indices
are the positive-band basis vectors `q^(j)`, the nuisance coordinates are the
physical logarithm and centered head indicators, and `slow` is the
compensated score. -/
inductive MomentCoord (Gauge HeadCoord : Type*)
  | gauge (j : Gauge)
  | physical
  | head (h : HeadCoord)
  | slow
  deriving DecidableEq, Fintype

/-- The finite nuisance block `(R,H^circ)` used before taking the Schur
complement. -/
inductive NuisanceCoord (HeadCoord : Type*)
  | physical
  | head (h : HeadCoord)
  deriving DecidableEq, Fintype

/-- The quotient-band plus compensated-score block, complementary to the
finite nuisance block. -/
inductive MainCoord (Gauge : Type*)
  | gauge (j : Gauge)
  | slow
  deriving DecidableEq, Fintype

/-- All concrete finite data entering the simultaneous fit. -/
structure BridgeData
    (Head Band : Type*) [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] where
  sampleData : StructuredSampleData Head
  baseline : BaselineAllocation sampleData
  partition : ArithmeticBandGeometry.Partition
    sampleData.n sampleData.W Band
  lowBand : Band
  referenceHead : Head
  w : ℝ
  w_pos : 0 < w
  n_gt_one : 1 < sampleData.n

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Positive-band coordinates, with the low row removed. -/
abbrev GaugeIndex := {j : Band // j ≠ B.lowBand}

/-- Centered head coordinates, with one reference pattern removed. -/
abbrev HeadIndex := {h : Head // h ≠ B.referenceHead}

/-- The actual finite coordinate type of Proposition 8.7. -/
abbrev Coord := MomentCoord B.GaugeIndex B.HeadIndex

/-- The Euclidean realization after the slow coordinate is rescaled by `w`.
Its ordinary Euclidean norm is the paper's anisotropic scaled Euclidean
norm on `(u,a,lambda)`, with the slow parameter represented by `w*lambda`. -/
abbrev ParamSpace := EuclideanSpace ℝ B.Coord

abbrev NuisanceSpace := EuclideanSpace ℝ (NuisanceCoord B.HeadIndex)

abbrev MainSpace := EuclideanSpace ℝ (MainCoord B.GaugeIndex)

/-- The paper's `L`; here it is tied to the actual integer `n`. -/
def L : ℝ := Real.log (B.sampleData.n : ℝ)

theorem L_pos : 0 < B.L := by
  rw [L, Real.log_pos_iff (by positivity)]
  exact_mod_cast B.n_gt_one



/-- The paper's active mass `q_n`. -/
def q : ℝ := B.baseline.totalMass

theorem q_pos [Nonempty Head] : 0 < B.q :=
  B.baseline.totalMass_pos

/-- Actual harmonic band mass `H_j`. -/
def harmonicMass (j : Band) : ℝ :=
  B.partition.mass j

theorem harmonicMass_pos (j : Band) : 0 < B.harmonicMass j :=
  B.partition.data.mass_pos j

/-- Actual arithmetic center `alpha_j`. -/
def bandCenter (j : Band) : ℝ :=
  B.partition.center j

theorem bandPrime_tPrime_pos
    (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
    0 < ArithmeticModel.tPrime B.sampleData.n p.1 := by
  have hn : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
  have hpPrime := ArithmeticModel.prime_of_mem_primeBand p.2
  have hpOne : (1 : ℝ) < (p.1 : ℝ) := by
    exact_mod_cast hpPrime.one_lt
  have hpLeNat : (p.1 : ℝ) ≤
      (ArithmeticModel.yNat B.sampleData.n : ℝ) := by
    exact_mod_cast ArithmeticModel.le_yNat_of_mem_primeBand p.2
  have hfloor : (ArithmeticModel.yNat B.sampleData.n : ℝ) ≤
      ArithmeticModel.y B.sampleData.n := by
    exact Nat.floor_le (le_of_lt (Scale.y_pos hn))
  have hyOne : (1 : ℝ) < ArithmeticModel.y B.sampleData.n :=
    hpOne.trans_le (hpLeNat.trans hfloor)
  exact div_pos (Real.log_pos hpOne) (Real.log_pos hyOne)

theorem bandCenter_pos (j : Band) : 0 < B.bandCenter j := by
  change 0 <
    (∑ p ∈ B.partition.data.fiber j,
      (1 / (p.1 : ℝ)) *
        ArithmeticModel.tPrime B.sampleData.n p.1) /
      B.partition.data.mass j
  apply div_pos
  · apply Finset.sum_pos
    · intro p hp
      exact mul_pos (by
        exact one_div_pos.mpr (by
          exact_mod_cast
            (ArithmeticModel.prime_of_mem_primeBand p.2).pos))
        (B.bandPrime_tPrime_pos p)
    · obtain ⟨p, hp⟩ := B.partition.fiber_nonempty j
      exact ⟨p, by
        simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp⟩
  · exact B.partition.data.mass_pos j

/-- The actual valuation statistic `Omega_j(m)`. -/
def bandScore (j : Band) (m : B.sampleData.Sample) : ℝ :=
  ∑ p ∈ B.partition.data.fiber j,
    ArithmeticModel.valuation p.1 (B.sampleData.value m)

/-- The coefficient of the low row in the concrete gauge basis
`q^(j)=e_j-(H_j alpha_j)/(H_0 alpha_0)e_0`. -/
def lowRatio (j : B.GaugeIndex) : ℝ :=
  B.harmonicMass j.1 * B.bandCenter j.1 /
    (B.harmonicMass B.lowBand * B.bandCenter B.lowBand)

/-- The quotient-band score corresponding to the paper's concrete basis. -/
def gaugeScore (j : B.GaugeIndex) (m : B.sampleData.Sample) : ℝ :=
  B.bandScore j.1 m - B.lowRatio j * B.bandScore B.lowBand m

/-- The physical logarithm `R(m)=log(m/n)`. -/
def physicalScore (m : B.sampleData.Sample) : ℝ :=
  Real.log ((B.sampleData.value m : ℝ) / (B.sampleData.n : ℝ))







/-- Indicator of a tagged head-pattern cell. -/
def headIndicator (h : Head) (m : B.sampleData.Sample) : ℝ :=
  if (B.sampleData.cellOf m).1 = h then 1 else 0

/-- Exact baseline probability of a head pattern, summed over its two
physical pools. -/
def headBaselineMass [Nonempty Head] (h : Head) : ℝ :=
  ∑ sigma : PhysicalSign,
    B.baseline.normalizedCellMass (h, sigma)

/-- The centered head indicator `H_h^circ`. -/
def centeredHeadScore [Nonempty Head]
    (h : B.HeadIndex) (m : B.sampleData.Sample) : ℝ :=
  B.headIndicator h.1 m - B.headBaselineMass h.1

/-- The exact arithmetic cell deviation `g_p=alpha_{j(p)}-t_p`. -/
def primeDeviation (p : ArithmeticBandGeometry.BandPrime
    B.sampleData.n B.sampleData.W) : ℝ :=
  B.bandCenter (B.partition.band p) -
    ArithmeticModel.tPrime B.sampleData.n p.1

/-- The raw compensated score `S_g=sum_p g_p v_p(m)`. -/
def slowScore (m : B.sampleData.Sample) : ℝ :=
  ∑ p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W,
    B.primeDeviation p *
      ArithmeticModel.valuation p.1 (B.sampleData.value m)

/-- The medium-prime logarithmic score removed by compensation. -/
def primeLogScore (m : B.sampleData.Sample) : ℝ :=
  ∑ p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W,
    ArithmeticModel.tPrime B.sampleData.n p.1 *
      ArithmeticModel.valuation p.1 (B.sampleData.value m)

/-- The logarithm contributed by the prescribed finite head pattern. -/
def headLogScore (h : Head) : ℝ :=
  ∑ p ∈ (B.sampleData.pattern h).primes,
    ((B.sampleData.pattern h).exponent p : ℝ) * Real.log (p : ℝ)











/-- Raw paper statistic before anisotropic coordinate scaling. -/
def rawStatistic [Nonempty Head]
    (m : B.sampleData.Sample) : B.Coord → ℝ
  | .gauge j => B.gaugeScore j m
  | .physical => B.physicalScore m
  | .head h => B.centeredHeadScore h m
  | .slow => B.slowScore m

/-- Coordinate scaling: only the slow statistic is divided by `w`, so its
dual parameter is `w*lambda`. -/
def coordScale (c : B.Coord) : ℝ :=
  match c with
  | .slow => B.w
  | _ => 1



/-- The actual statistic vector used by `VectorExponentialFamily`. -/
def statistic [Nonempty Head]
    (m : B.sampleData.Sample) : B.ParamSpace :=
  (EuclideanSpace.equiv B.Coord ℝ).symm
    (fun c => B.rawStatistic m c / B.coordScale c)

@[simp]
theorem statistic_apply [Nonempty Head]
    (m : B.sampleData.Sample) (c : B.Coord) :
    (B.statistic m : B.Coord → ℝ) c =
      B.rawStatistic m c / B.coordScale c := by
  rfl

/-! ### Exact main/nuisance coordinate splitting -/

/-- Coordinate inclusion of quotient-band and slow variables. -/
def mainEmbed (u : B.MainSpace) : B.ParamSpace :=
  (EuclideanSpace.equiv B.Coord ℝ).symm (fun c => match c with
    | .gauge j => u (MainCoord.gauge j)
    | .slow => u MainCoord.slow
    | .physical => 0
    | .head _ => 0)

/-- Coordinate inclusion of physical/head nuisance variables. -/
def nuisanceEmbed (z : B.NuisanceSpace) : B.ParamSpace :=
  (EuclideanSpace.equiv B.Coord ℝ).symm (fun c => match c with
    | .physical => z NuisanceCoord.physical
    | .head h => z (NuisanceCoord.head h)
    | .gauge _ => 0
    | .slow => 0)

@[simp] theorem mainEmbed_gauge (u : B.MainSpace) (j : B.GaugeIndex) :
    B.mainEmbed u (MomentCoord.gauge j) = u (MainCoord.gauge j) := rfl

@[simp] theorem mainEmbed_slow (u : B.MainSpace) :
    B.mainEmbed u MomentCoord.slow = u MainCoord.slow := rfl

@[simp] theorem mainEmbed_physical (u : B.MainSpace) :
    B.mainEmbed u MomentCoord.physical = 0 := rfl

@[simp] theorem mainEmbed_head (u : B.MainSpace) (h : B.HeadIndex) :
    B.mainEmbed u (MomentCoord.head h) = 0 := rfl

@[simp] theorem nuisanceEmbed_gauge (z : B.NuisanceSpace)
    (j : B.GaugeIndex) : B.nuisanceEmbed z (MomentCoord.gauge j) = 0 := rfl

@[simp] theorem nuisanceEmbed_slow (z : B.NuisanceSpace) :
    B.nuisanceEmbed z MomentCoord.slow = 0 := rfl

@[simp] theorem nuisanceEmbed_physical (z : B.NuisanceSpace) :
    B.nuisanceEmbed z MomentCoord.physical = z NuisanceCoord.physical := rfl

@[simp] theorem nuisanceEmbed_head (z : B.NuisanceSpace)
    (h : B.HeadIndex) :
    B.nuisanceEmbed z (MomentCoord.head h) = z (NuisanceCoord.head h) := rfl

def mainEmbedding : B.MainSpace →ₗ[ℝ] B.ParamSpace where
  toFun := B.mainEmbed
  map_add' := by
    intro u v
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [mainEmbed]
  map_smul' := by
    intro a u
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [mainEmbed]

def nuisanceEmbedding : B.NuisanceSpace →ₗ[ℝ] B.ParamSpace where
  toFun := B.nuisanceEmbed
  map_add' := by
    intro u v
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [nuisanceEmbed]
  map_smul' := by
    intro a u
    apply (EuclideanSpace.equiv B.Coord ℝ).injective
    funext c
    cases c <;> simp [nuisanceEmbed]

def mainEmbeddingCLM : B.MainSpace →L[ℝ] B.ParamSpace :=
  B.mainEmbedding.toContinuousLinearMap

def nuisanceEmbeddingCLM : B.NuisanceSpace →L[ℝ] B.ParamSpace :=
  B.nuisanceEmbedding.toContinuousLinearMap

/-- Recombination of the two complementary coordinate blocks. -/
def combine (u : B.MainSpace) (z : B.NuisanceSpace) : B.ParamSpace :=
  B.mainEmbed u + B.nuisanceEmbed z

@[simp] theorem combine_gauge (u : B.MainSpace) (z : B.NuisanceSpace)
    (j : B.GaugeIndex) :
    B.combine u z (MomentCoord.gauge j) = u (MainCoord.gauge j) := by
  simp [combine]

@[simp] theorem combine_slow (u : B.MainSpace) (z : B.NuisanceSpace) :
    B.combine u z MomentCoord.slow = u MainCoord.slow := by
  simp [combine]

@[simp] theorem combine_physical (u : B.MainSpace) (z : B.NuisanceSpace) :
    B.combine u z MomentCoord.physical = z NuisanceCoord.physical := by
  simp [combine]

@[simp] theorem combine_head (u : B.MainSpace) (z : B.NuisanceSpace)
    (h : B.HeadIndex) :
    B.combine u z (MomentCoord.head h) = z (NuisanceCoord.head h) := by
  simp [combine]

/-- The coordinate type is exactly the disjoint union of the main and
nuisance coordinate types.  Making this equivalence explicit avoids relying
on fragile simplification of sums over a derived `Fintype` instance. -/
def coordSplitEquiv :
    B.Coord ≃ (MainCoord B.GaugeIndex ⊕ NuisanceCoord B.HeadIndex) where
  toFun
    | .gauge j => Sum.inl (.gauge j)
    | .slow => Sum.inl .slow
    | .physical => Sum.inr .physical
    | .head h => Sum.inr (.head h)
  invFun
    | Sum.inl (.gauge j) => .gauge j
    | Sum.inl .slow => .slow
    | Sum.inr .physical => .physical
    | Sum.inr (.head h) => .head h
  left_inv c := by cases c <;> rfl
  right_inv c := by
    rcases c with c | c <;> cases c <;> rfl

theorem sum_coord_split (f : B.Coord → ℝ) :
    (∑ c : B.Coord, f c) =
      (∑ c : MainCoord B.GaugeIndex,
        f (match c with
          | .gauge j => .gauge j
          | .slow => .slow)) +
      ∑ c : NuisanceCoord B.HeadIndex,
        f (match c with
          | .physical => .physical
          | .head h => .head h) := by
  calc
    (∑ c : B.Coord, f c) =
        ∑ s : (MainCoord B.GaugeIndex ⊕ NuisanceCoord B.HeadIndex),
          f (B.coordSplitEquiv.symm s) := by
      exact Fintype.sum_equiv B.coordSplitEquiv f
        (fun s => f (B.coordSplitEquiv.symm s)) (fun c => by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro c hc
        cases c <;> simp [coordSplitEquiv]
      · apply Finset.sum_congr rfl
        intro c hc
        cases c <;> simp [coordSplitEquiv]













theorem inner_nuisanceEmbed_combine (z v : B.NuisanceSpace)
    (u : B.MainSpace) :
    inner ℝ (B.nuisanceEmbed z) (B.combine u v) = inner ℝ z v := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ c : B.Coord, B.combine u v c * B.nuisanceEmbed z c) =
    ∑ c : NuisanceCoord B.HeadIndex, v c * z c
  rw [B.sum_coord_split]
  have hmain : (∑ c : MainCoord B.GaugeIndex,
      B.combine u v (match c with
        | .gauge j => .gauge j
        | .slow => .slow) *
      B.nuisanceEmbed z (match c with
        | .gauge j => .gauge j
        | .slow => .slow)) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    cases c <;> simp
  have hnuisance : (∑ c : NuisanceCoord B.HeadIndex,
      B.combine u v (match c with
        | .physical => .physical
        | .head h => .head h) *
      B.nuisanceEmbed z (match c with
        | .physical => .physical
        | .head h => .head h)) = ∑ c, v c * z c := by
    apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp
  rw [hmain, hnuisance, zero_add]

/-- The quotient/slow portion of the actual statistic vector. -/
def mainStatistic [Nonempty Head]
    (m : B.sampleData.Sample) : B.MainSpace :=
  (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).symm
    (fun c => match c with
      | .gauge j => B.statistic m (MomentCoord.gauge j)
      | .slow => B.statistic m MomentCoord.slow)

@[simp] theorem mainStatistic_gauge [Nonempty Head]
    (m : B.sampleData.Sample) (j : B.GaugeIndex) :
    B.mainStatistic m (MainCoord.gauge j) =
      B.statistic m (MomentCoord.gauge j) := rfl

@[simp] theorem mainStatistic_slow [Nonempty Head]
    (m : B.sampleData.Sample) :
    B.mainStatistic m MainCoord.slow = B.statistic m MomentCoord.slow := rfl

/-- The concrete self-dual exponential family.  In the scaled coordinates
`theta_slow=w*lambda`, its exponent is exactly
`L^(-1)(sum u_j Q_j + a^T Z + lambda S_g)`. -/
def vectorFamily [Nonempty Head] :
    VectorExponentialFamily B.sampleData.Sample B.ParamSpace where
  baseWeight := B.baseline.baseWeight
  baseWeight_nonneg := B.baseline.baseWeight_nonneg
  baseMass_pos := by
    rw [B.baseline.baseWeight_sum]
    exact B.q_pos
  scale := B.L
  scale_pos := B.L_pos
  statistic := B.statistic

theorem vectorFamily_baseMass [Nonempty Head] :
    B.vectorFamily.baseMass = B.q := by
  simp only [VectorExponentialFamily.baseMass,
    VectorExponentialFamily.scalarFamily,
    FiniteExponentialFamily.baseMass, vectorFamily, q]
  exact B.baseline.baseWeight_sum

/-- The normalized covariance operator.  The factor `L/q` removes the
active-mass Jacobian normalization, so its quadratic form is exactly the
probability covariance of the actual statistic vector. -/
def covarianceOperator [Nonempty Head]
    (xi : B.ParamSpace) : B.ParamSpace →L[ℝ] B.ParamSpace :=
  (B.L / B.q) • B.vectorFamily.jacobian xi







theorem inner_covarianceOperator_self [Nonempty Head]
    (xi x : B.ParamSpace) :
    inner ℝ x (B.covarianceOperator xi x) =
      (B.vectorFamily.tiltedMixture xi).covarianceForm x := by
  rw [covarianceOperator, ContinuousLinearMap.smul_apply, inner_smul_right,
    B.vectorFamily.inner_jacobian_self]
  have hL : B.L ≠ 0 := ne_of_gt B.L_pos
  have hq : B.q ≠ 0 := ne_of_gt B.q_pos
  rw [B.vectorFamily_baseMass]
  change (B.L / B.q) *
      (B.q / B.L *
        (B.vectorFamily.tiltedMixture xi).covarianceForm x) =
    (B.vectorFamily.tiltedMixture xi).covarianceForm x
  field_simp



/-- Actual finite nuisance covariance `Γ_{xi,n}`. -/
def nuisanceCovarianceOperator [Nonempty Head]
    (xi : B.ParamSpace) : B.NuisanceSpace →L[ℝ] B.NuisanceSpace :=
  B.nuisanceEmbeddingCLM.adjoint.comp
    ((B.covarianceOperator xi).comp B.nuisanceEmbeddingCLM)

/-- The actual main-to-nuisance cross-covariance block. -/
def crossCovarianceOperator [Nonempty Head]
    (xi : B.ParamSpace) : B.MainSpace →L[ℝ] B.NuisanceSpace :=
  B.nuisanceEmbeddingCLM.adjoint.comp
    ((B.covarianceOperator xi).comp B.mainEmbeddingCLM)

/-- Residual main score after subtracting a nuisance regression. -/
def schurResidual (R : B.MainSpace → B.NuisanceSpace)
    (u : B.MainSpace) : B.ParamSpace :=
  B.combine u (-R u)

theorem schurResidual_eq_sub (R : B.MainSpace → B.NuisanceSpace)
    (u : B.MainSpace) :
    B.schurResidual R u = B.mainEmbed u - B.nuisanceEmbed (R u) := by
  unfold schurResidual combine
  have hneg : B.nuisanceEmbed (-R u) = -B.nuisanceEmbed (R u) :=
    B.nuisanceEmbedding.map_neg (R u)
  rw [hneg]
  rfl

/-- Exact two-sided block orthogonality of a nuisance regression.  This is
an algebraic equation for the displayed actual covariance operator, not a
spectral-gap hypothesis. -/
def IsNuisanceRegression [Nonempty Head] (xi : B.ParamSpace)
    (R : B.MainSpace → B.NuisanceSpace) : Prop :=
  ∀ u z,
    inner ℝ (B.schurResidual R u)
        (B.covarianceOperator xi (B.nuisanceEmbed z)) = 0 ∧
      inner ℝ (B.nuisanceEmbed z)
        (B.covarianceOperator xi (B.schurResidual R u)) = 0

theorem nuisanceCovarianceOperator_injective [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    Function.Injective (B.nuisanceCovarianceOperator xi) := by
  intro z₁ z₂ heq
  have hzero : B.nuisanceCovarianceOperator xi (z₁ - z₂) = 0 := by
    rw [map_sub, heq, sub_self]
  have hcoer := hgap (z₁ - z₂)
  rw [hzero, inner_zero_right] at hcoer
  have hnorm : ‖z₁ - z₂‖ = 0 := by
    by_contra hn
    have hnpos : 0 < ‖z₁ - z₂‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have : 0 < gamma * ‖z₁ - z₂‖ ^ 2 :=
      mul_pos hgamma (sq_pos_of_pos hnpos)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The actual nuisance block as an equivalence, constructed from a proved
finite coercivity bound. -/
def nuisanceCovarianceEquiv [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.NuisanceSpace ≃L[ℝ] B.NuisanceSpace :=
  (LinearEquiv.ofInjectiveEndo
    ((B.nuisanceCovarianceOperator xi :
      B.NuisanceSpace →L[ℝ] B.NuisanceSpace) :
        B.NuisanceSpace →ₗ[ℝ] B.NuisanceSpace)
    (B.nuisanceCovarianceOperator_injective xi hgamma hgap)).toContinuousLinearEquiv



/-- The actual finite nuisance regression `Γ_{xi,n}^{-1} B_{xi,n}`. -/
def exactNuisanceRegression [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) : B.NuisanceSpace :=
  (B.nuisanceCovarianceEquiv xi hgamma hgap).symm
    (B.crossCovarianceOperator xi u)

def exactNuisanceRegressionCLM [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.MainSpace →L[ℝ] B.NuisanceSpace :=
  (B.nuisanceCovarianceEquiv xi hgamma hgap).symm.toContinuousLinearMap.comp
    (B.crossCovarianceOperator xi)

@[simp] theorem exactNuisanceRegressionCLM_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.exactNuisanceRegressionCLM xi hgamma hgap u =
      B.exactNuisanceRegression xi hgamma hgap u := rfl

/-- Linear residual inclusion `u ↦ (u,-Γ⁻¹Bu)`. -/
def exactSchurEmbeddingCLM [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.MainSpace →L[ℝ] B.ParamSpace :=
  B.mainEmbeddingCLM - B.nuisanceEmbeddingCLM.comp
    (B.exactNuisanceRegressionCLM xi hgamma hgap)

@[simp] theorem exactSchurEmbeddingCLM_apply [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.exactSchurEmbeddingCLM xi hgamma hgap u =
      B.schurResidual (B.exactNuisanceRegression xi hgamma hgap) u := by
  rw [B.schurResidual_eq_sub]
  rfl

/-- Actual main/slow Schur-complement operator after exact finite nuisance
regression. -/
def exactSchurCovarianceOperator [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    B.MainSpace →L[ℝ] B.MainSpace :=
  B.mainEmbeddingCLM.adjoint.comp
    ((B.covarianceOperator xi).comp
      (B.exactSchurEmbeddingCLM xi hgamma hgap))























/-! ## Exact target and moment correspondence -/

/-- The unscaled endpoint requested by a band residual vector `Delta`.
The slow component is `alpha^T Delta`; the physical and head components
are zero. -/
def unscaledTarget (Delta : Band → ℝ) : B.Coord → ℝ
  | .gauge j => Delta j.1 - B.lowRatio j * Delta B.lowBand
  | .physical => 0
  | .head _ => 0
  | .slow => ∑ j, B.bandCenter j * Delta j

/-- Endpoint in the anisotropically scaled Euclidean coordinates. -/
def targetVector (Delta : Band → ℝ) : B.ParamSpace :=
  (EuclideanSpace.equiv B.Coord ℝ).symm
    (fun c => B.unscaledTarget Delta c / B.coordScale c)

@[simp]
theorem targetVector_apply (Delta : Band → ℝ) (c : B.Coord) :
    (B.targetVector Delta : B.Coord → ℝ) c =
      B.unscaledTarget Delta c / B.coordScale c := by
  rfl

/-- The normalized target `tau=(L/q) target` displayed in Proposition 8.7. -/
def normalizedTarget [Nonempty Head] (Delta : Band → ℝ) : B.ParamSpace :=
  (B.L / B.q) • B.targetVector Delta

@[simp]
theorem normalizedTarget_apply [Nonempty Head]
    (Delta : Band → ℝ) (c : B.Coord) :
    (B.normalizedTarget Delta : B.Coord → ℝ) c =
      (B.L / B.q) *
        (B.unscaledTarget Delta c / B.coordScale c) := by
  rfl

/-- Raw active moment of a paper statistic. -/
def paperMoment [Nonempty Head]
    (F : B.sampleData.Sample → ℝ) (xi : B.ParamSpace) : ℝ :=
  B.vectorFamily.scalarFamily.moment F xi





















/-- Any statistic depending only on the tagged head pattern. -/
def headFunctionScore (phi : Head → ℝ)
    (m : B.sampleData.Sample) : ℝ :=
  phi (B.sampleData.cellOf m).1





/-- Exact finite logarithmic compatibility required by the paper: on the
guarded smooth sample, the medium-prime logarithmic score is an affine
combination of the ordinary physical logarithm and the tagged head pattern.
The later arithmetic factorization theorem must produce this identity. -/
def HasPrimeLogCompatibility : Prop :=
  ∃ a : ℝ, ∃ phi : Head → ℝ, ∀ m : B.sampleData.Sample,
    B.primeLogScore m =
      a * B.physicalScore m + B.headFunctionScore phi m













/-- The one-dimensional band vector invisible to the concrete gauge
coordinates. -/
def bandKernelVector (j : Band) : ℝ :=
  if h : j = B.lowBand then 1 else B.lowRatio ⟨j, h⟩

def bandRecoveryCoefficient : ℝ :=
  ∑ j : Band, B.bandCenter j * B.bandKernelVector j







def bandMomentError [Nonempty Head]
    (Delta : Band → ℝ) (xi0 xi1 : B.ParamSpace) (j : Band) : ℝ :=
  B.paperMoment (B.bandScore j) xi1 -
    B.paperMoment (B.bandScore j) xi0 - Delta j















/-! ## Actual baseline mixture and coarse cells -/

/-- At parameter zero the normalized tilted law is exactly the explicit
baseline law `z_m^0/q_n`. -/
theorem probabilityMass_zero [Nonempty Head]
    (m : B.sampleData.Sample) :
    B.vectorFamily.probabilityMass 0 m =
      B.baseline.baseWeight m / B.q := by
  simp only [VectorExponentialFamily.probabilityMass,
    VectorExponentialFamily.scalarFamily,
    FiniteExponentialFamily.probabilityMass,
    FiniteExponentialFamily.unnormalizedWeight,
    FiniteExponentialFamily.partition, vectorFamily,
    map_zero, zero_div, Real.exp_zero, mul_one]
  rw [B.baseline.baseWeight_sum]
  rfl

/-- The canonical coarse mixture obtained from the actual fine baseline and
the literal cell tag. -/
def coarseBaseline [Nonempty Head] : PatternMixture (Cell Head) B.ParamSpace :=
  CanonicalCoarseMixture.coarse
    (B.vectorFamily.tiltedMixture 0) B.sampleData.cellOf

theorem coarseBaseline_weight [Nonempty Head] (c : Cell Head) :
    B.coarseBaseline.weight c = B.baseline.normalizedCellMass c := by
  change CanonicalCoarseMixture.fiberWeight
      (B.vectorFamily.tiltedMixture 0) B.sampleData.cellOf c =
    B.baseline.normalizedCellMass c
  simp only [CanonicalCoarseMixture.fiberWeight,
    VectorExponentialFamily.tiltedMixture]
  have hp (m : B.sampleData.Sample) :
      B.vectorFamily.probabilityMass 0 m =
        B.baseline.baseWeight m / B.q :=
    B.probabilityMass_zero m
  simp_rw [hp]
  rw [Finset.sum_filter]
  rw [Fintype.sum_sigma]
  simp only [StructuredSampleData.cellOf]
  rw [Finset.sum_eq_single c]
  · simp only [BaselineAllocation.baseWeight,
      BaselineAllocation.normalizedCellMass,
      StructuredSampleData.cellOf, if_true, q]
    rw [← Finset.sum_div]
    have hcard : (Fintype.card (B.sampleData.SampleAt c) : ℝ) ≠ 0 := by
      exact_mod_cast
        (Nat.ne_of_gt (B.sampleData.sampleAt_card_pos c))
    change (∑ _ : B.sampleData.SampleAt c,
      B.baseline.cellMass c / (Fintype.card (B.sampleData.SampleAt c) : ℝ)) /
        B.baseline.totalMass = B.baseline.cellMass c / B.baseline.totalMass
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcard]
  · intro c' _ hne
    simp [hne]
  · intro hc
    exact (hc (Finset.mem_univ c)).elim











/-- The actual nuisance statistic `Z=(R,H_1^circ,...,H_e^circ)`. -/
def nuisanceStatistic [Nonempty Head]
    (m : B.sampleData.Sample) : B.NuisanceSpace :=
  (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm
    (fun c => match c with
      | .physical => B.physicalScore m
      | .head h => B.centeredHeadScore h m)

@[simp]
theorem nuisanceStatistic_physical [Nonempty Head]
    (m : B.sampleData.Sample) :
    B.nuisanceStatistic m (NuisanceCoord.physical) = B.physicalScore m := by
  rfl

@[simp]
theorem nuisanceStatistic_head [Nonempty Head]
    (m : B.sampleData.Sample) (h : B.HeadIndex) :
    B.nuisanceStatistic m (NuisanceCoord.head h) =
      B.centeredHeadScore h m := by
  rfl

/-- The full statistic is exactly the orthogonal coordinate recombination
of the main and nuisance blocks. -/
theorem statistic_eq_combine [Nonempty Head]
    (m : B.sampleData.Sample) :
    B.statistic m = B.combine (B.mainStatistic m) (B.nuisanceStatistic m) := by
  apply (EuclideanSpace.equiv B.Coord ℝ).injective
  funext c
  cases c with
  | gauge j => simp
  | slow => simp
  | physical => simp [statistic_apply, rawStatistic, coordScale]
  | head h => simp [statistic_apply, rawStatistic, coordScale]

/-- Fine baseline law on the actual nuisance patterns. -/
def nuisanceFineBaseline [Nonempty Head] :
    PatternMixture B.sampleData.Sample B.NuisanceSpace where
  weight := B.vectorFamily.probabilityMass 0
  weight_nonneg := B.vectorFamily.scalarFamily.probabilityMass_nonneg 0
  weight_sum := B.vectorFamily.scalarFamily.probabilityMass_sum 0
  pattern := B.nuisanceStatistic

/-- Nuisance marginal at an arbitrary point of the actual tilt path. -/
def nuisanceFineAt [Nonempty Head] (xi : B.ParamSpace) :
    PatternMixture B.sampleData.Sample B.NuisanceSpace where
  weight := B.vectorFamily.probabilityMass xi
  weight_nonneg := B.vectorFamily.scalarFamily.probabilityMass_nonneg xi
  weight_sum := B.vectorFamily.scalarFamily.probabilityMass_sum xi
  pattern := B.nuisanceStatistic

@[simp] theorem nuisanceFineAt_zero [Nonempty Head] :
    B.nuisanceFineAt 0 = B.nuisanceFineBaseline := rfl

/-- The abstract block `Γ_{xi,n}` is exactly the covariance of the literal
physical/head statistic under the actual tilted finite law. -/
theorem nuisanceCovarianceOperator_quadratic [Nonempty Head]
    (xi : B.ParamSpace) (z : B.NuisanceSpace) :
    inner ℝ z (B.nuisanceCovarianceOperator xi z) =
      (B.nuisanceFineAt xi).covarianceForm z := by
  have hinter : inner ℝ z (B.nuisanceCovarianceOperator xi z) =
      inner ℝ (B.nuisanceEmbed z)
        (B.covarianceOperator xi (B.nuisanceEmbed z)) := by
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply] using
      (ContinuousLinearMap.adjoint_inner_right B.nuisanceEmbeddingCLM z
        (B.covarianceOperator xi (B.nuisanceEmbeddingCLM z)))
  rw [hinter, B.inner_covarianceOperator_self]
  unfold PatternMixture.covarianceForm PatternMixture.probability
    FiniteProbability.covariance FiniteProbability.expect
  simp only [VectorExponentialFamily.tiltedMixture, nuisanceFineAt]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    rw [show B.vectorFamily.statistic m = B.statistic m by rfl,
      B.statistic_eq_combine m,
      B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m)
        (B.mainStatistic m)]
  · apply congrArg₂ (· * ·)
    · apply Finset.sum_congr rfl
      intro m hm
      rw [show B.vectorFamily.statistic m = B.statistic m by rfl,
        B.statistic_eq_combine m,
        B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m)
          (B.mainStatistic m)]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [show B.vectorFamily.statistic m = B.statistic m by rfl,
        B.statistic_eq_combine m,
        B.inner_nuisanceEmbed_combine z (B.nuisanceStatistic m)
          (B.mainStatistic m)]





/-- Canonical nuisance cell mixture. -/
def nuisanceCoarseBaseline [Nonempty Head] :
    PatternMixture (Cell Head) B.NuisanceSpace :=
  CanonicalCoarseMixture.coarse B.nuisanceFineBaseline B.sampleData.cellOf

theorem nuisanceCoarseBaseline_weight [Nonempty Head] (c : Cell Head) :
    B.nuisanceCoarseBaseline.weight c =
      B.baseline.normalizedCellMass c := by
  change CanonicalCoarseMixture.fiberWeight
      B.nuisanceFineBaseline B.sampleData.cellOf c =
    B.baseline.normalizedCellMass c
  change CanonicalCoarseMixture.fiberWeight
      (B.vectorFamily.tiltedMixture 0) B.sampleData.cellOf c =
    B.baseline.normalizedCellMass c
  exact B.coarseBaseline_weight c

theorem nuisanceCoarseBaseline_weight_pos [Nonempty Head]
    (c : Cell Head) : 0 < B.nuisanceCoarseBaseline.weight c := by
  rw [B.nuisanceCoarseBaseline_weight c]
  exact B.baseline.normalizedCellMass_pos c

/-- Every centered-head coordinate is literally constant on a tagged
head/physical cell, so its conditional mean is the same constant. -/
theorem nuisanceCoarseBaseline_pattern_head [Nonempty Head]
    (c : Cell Head) (h : B.HeadIndex) :
    B.nuisanceCoarseBaseline.pattern c (NuisanceCoord.head h) =
      (if c.1 = h.1 then 1 else 0) - B.headBaselineMass h.1 := by
  change ((CanonicalCoarseMixture.fiberWeight
      B.nuisanceFineBaseline B.sampleData.cellOf c)⁻¹ •
    CanonicalCoarseMixture.fiberMoment
      B.nuisanceFineBaseline B.sampleData.cellOf c)
        (NuisanceCoord.head h) = _
  simp only [Pi.smul_apply, smul_eq_mul,
    CanonicalCoarseMixture.fiberMoment, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, nuisanceFineBaseline,
    nuisanceStatistic_head]
  let K : ℝ := (if c.1 = h.1 then 1 else 0) -
    B.headBaselineMass h.1
  have hconstant : ∀ m : B.sampleData.Sample,
      m ∈ (Finset.univ : Finset B.sampleData.Sample) →
      B.sampleData.cellOf m = c → B.centeredHeadScore h m = K := by
    intro m hm hmc
    simp only [centeredHeadScore, headIndicator, K, hmc]
  have hsum :
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.centeredHeadScore h m) =
        CanonicalCoarseMixture.fiberWeight
          B.nuisanceFineBaseline B.sampleData.cellOf c * K := by
    rw [CanonicalCoarseMixture.fiberWeight, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hconstant m (Finset.mem_univ m) (Finset.mem_filter.mp hm).2]
  change (CanonicalCoarseMixture.fiberWeight
      B.nuisanceFineBaseline B.sampleData.cellOf c)⁻¹ *
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
        B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.centeredHeadScore h m) = _
  rw [hsum]
  have hweight : CanonicalCoarseMixture.fiberWeight
      B.nuisanceFineBaseline B.sampleData.cellOf c ≠ 0 := by
    exact ne_of_gt (by
      simpa only [← CanonicalCoarseMixture.coarse_weight] using
        B.nuisanceCoarseBaseline_weight_pos c)
  dsimp only [K]
  field_simp

/-- The physical coordinate of an actual coarse conditional mean. -/
def cellPhysicalMean [Nonempty Head] (c : Cell Head) : ℝ :=
  B.nuisanceCoarseBaseline.pattern c NuisanceCoord.physical

/-- Changing only the physical sign of a cell changes its nuisance pattern
only along the physical coordinate. -/
theorem nuisancePattern_sameHead_sub [Nonempty Head] (h : Head) :
    B.nuisanceCoarseBaseline.pattern (h, .plus) -
        B.nuisanceCoarseBaseline.pattern (h, .minus) =
      (B.cellPhysicalMean (h, .plus) -
        B.cellPhysicalMean (h, .minus)) •
          EuclideanSpace.single NuisanceCoord.physical (1 : ℝ) := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  change (B.nuisanceCoarseBaseline.pattern (h, .plus) -
      B.nuisanceCoarseBaseline.pattern (h, .minus)) c =
    ((B.cellPhysicalMean (h, .plus) -
      B.cellPhysicalMean (h, .minus)) •
        EuclideanSpace.single NuisanceCoord.physical (1 : ℝ)) c
  cases c with
  | physical => simp [cellPhysicalMean]
  | head k =>
      rw [WithLp.ofLp_sub, Pi.sub_apply,
        WithLp.ofLp_smul, Pi.smul_apply,
        B.nuisanceCoarseBaseline_pattern_head,
        B.nuisanceCoarseBaseline_pattern_head]
      simp [EuclideanSpace.single_apply]

/-- Changing the head tag at a fixed physical sign changes the head block
by exactly one coordinate, plus a possibly nonzero physical displacement. -/
theorem nuisancePattern_head_sub [Nonempty Head]
    (h : B.HeadIndex) (sigma : PhysicalSign) :
    B.nuisanceCoarseBaseline.pattern (h.1, sigma) -
        B.nuisanceCoarseBaseline.pattern (B.referenceHead, sigma) =
      (B.cellPhysicalMean (h.1, sigma) -
        B.cellPhysicalMean (B.referenceHead, sigma)) •
          EuclideanSpace.single NuisanceCoord.physical (1 : ℝ) +
        EuclideanSpace.single (NuisanceCoord.head h) (1 : ℝ) := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  change (B.nuisanceCoarseBaseline.pattern (h.1, sigma) -
      B.nuisanceCoarseBaseline.pattern (B.referenceHead, sigma)) c =
    (((B.cellPhysicalMean (h.1, sigma) -
        B.cellPhysicalMean (B.referenceHead, sigma)) •
          EuclideanSpace.single NuisanceCoord.physical (1 : ℝ) +
      EuclideanSpace.single (NuisanceCoord.head h) (1 : ℝ)) :
        B.NuisanceSpace) c
  cases c with
  | physical => simp [cellPhysicalMean]
  | head k =>
      rw [WithLp.ofLp_sub, Pi.sub_apply,
        WithLp.ofLp_add, Pi.add_apply,
        WithLp.ofLp_smul, Pi.smul_apply,
        B.nuisanceCoarseBaseline_pattern_head,
        B.nuisanceCoarseBaseline_pattern_head]
      simp only [smul_eq_mul,
        EuclideanSpace.single_apply]
      by_cases hhk : h = k
      · subst k
        have href : B.referenceHead ≠ h.1 := Ne.symm h.2
        simp [href]
      · have hval : h.1 ≠ k.1 := by
          intro heq
          exact hhk (Subtype.ext heq)
        have href : B.referenceHead ≠ k.1 := Ne.symm k.2
        have hkh : k ≠ h := Ne.symm hhk
        simp [hval, href, hkh]



/-- Exact nuisance conditional-mean certificate. -/
def nuisanceCoarseCertificate [Nonempty Head] :
    PatternMixture.CoarseMeanCertificate
      B.nuisanceFineBaseline B.nuisanceCoarseBaseline :=
  CanonicalCoarseMixture.certificate
    B.nuisanceFineBaseline B.sampleData.cellOf (by
      intro c
      simpa only [CanonicalCoarseMixture.fiberWeight,
        ← CanonicalCoarseMixture.coarse_weight] using
        B.nuisanceCoarseBaseline_weight_pos c)

/-- First-moment identity for the physical coordinate in one actual cell. -/
theorem cellPhysicalMean_mul_weight [Nonempty Head] (c : Cell Head) :
    B.nuisanceCoarseBaseline.weight c * B.cellPhysicalMean c =
      ∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m := by
  have h := B.nuisanceCoarseCertificate.cell_firstMoment c
    (EuclideanSpace.single NuisanceCoord.physical (1 : ℝ))
  change (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
      B.sampleData.cellOf m = c,
      B.nuisanceFineBaseline.weight m *
        inner ℝ (EuclideanSpace.single NuisanceCoord.physical (1 : ℝ))
          (B.nuisanceStatistic m)) =
    B.nuisanceCoarseBaseline.weight c *
      inner ℝ (EuclideanSpace.single NuisanceCoord.physical (1 : ℝ))
        (B.nuisanceCoarseBaseline.pattern c) at h
  simpa only [EuclideanSpace.inner_single_left, RCLike.conj_to_real,
    one_mul, B.nuisanceStatistic_physical, cellPhysicalMean] using h.symm





































/-! ## Explicit finite diameter -/

/-- A concrete (not optimized) finite diameter certificate. -/
def statisticDiameter [Nonempty Head] : ℝ :=
  ∑ i : B.sampleData.Sample, ∑ j : B.sampleData.Sample,
    ‖B.statistic i - B.statistic j‖







/-- The covariance operator as a finite positive sum of rank-one pair
differences.  This is an identity for the actual tilted law at every finite
`n`, with no compactness or asymptotic input. -/
def covariancePairOperator [Nonempty Head]
    (xi : B.ParamSpace) : B.ParamSpace →L[ℝ] B.ParamSpace :=
  (1 / 2 : ℝ) • ∑ i : B.sampleData.Sample,
    ∑ j : B.sampleData.Sample,
      (B.vectorFamily.probabilityMass xi i *
        B.vectorFamily.probabilityMass xi j) •
          InnerProductSpace.rankOne ℝ
            (B.statistic i - B.statistic j)
            (B.statistic i - B.statistic j)



/-- Canonical, finite and tilt-independent cross-block bound.  It is crude
but completely explicit: every covariance block is dominated by one half
of the squared diameter of the actual statistic vectors. -/
def canonicalCrossBound [Nonempty Head] : ℝ :=
  B.statisticDiameter ^ 2 / 2







/-! ## A finite `ell^1` tilt bound -/













































/-! ## Target envelopes imply the ODE radius margin -/

/-- The two target estimates supplied before Proposition 8.7: the strict
band-rate envelope and the sharper compensated scalar estimate. -/
def HasTargetEnvelopes [Nonempty Head]
    (C : ℝ) (Delta : Band → ℝ) : Prop :=
  (∀ j, |Delta j| ≤
      (B.q / B.L) * C * |B.harmonicMass j|) ∧
    |∑ j, B.bandCenter j * Delta j| ≤
      (B.q / B.L) * C * B.w













/-! ## Concrete Proposition 8.7 endpoint -/











end BridgeData

/-! ## Non-circular order of asymptotic choices -/



end PaperBridgeFit

end


end Erdos390.Full

end

/- Source module: Erdos390.Full.PaperGuardedStructuredSample -/
section


/-!
# Canonical guarded structured sample

This module attaches the concrete guard ledger to the literal physical
structured cells used by the bridge.  Both physical endpoints are definitionally
`floor(A*n)`, and nonemptiness after guard deletion is derived from the proved
Dickman cell-density theorem and the concrete `O(y log n)` image census.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open PaperScaleMarkedCell
open PaperBridgeFit

noncomputable section

/-- Fixed physical intervals for the two bridge pools. -/
structure PhysicalIntervals where
  lower : PhysicalSign → ℝ
  upper : PhysicalSign → ℝ
  lower_pos : ∀ sigma, 0 < lower sigma
  lower_lt_upper : ∀ sigma, lower sigma < upper sigma
  separated : upper .minus < lower .plus

variable {Head : Type*} [Fintype Head]

/-- The unguarded head/physical cell with the paper's natural endpoints. -/
def rawCell (P : Head → Pattern) (I : PhysicalIntervals)
    (n : ℕ) (c : Cell Head) : Finset ℕ :=
  structuredCell (P c.1)
    (physicalBound (I.lower c.2) n)
    (physicalBound (I.upper c.2) n)
    (yNat n)









/-- Canonical `StructuredSampleData` built from fixed physical constants and
the concrete ledger.  Its endpoints and guard set reduce definitionally to
the paper objects. -/
def canonicalSampleData
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) n <
      physicalBound (I.lower .plus) n)
    (hnonempty : ∀ c : Cell Head,
      (rawCell P I n c \ G.guards).Nonempty) :
    StructuredSampleData Head where
  n := n
  W := W
  pattern := P
  lo := fun sigma ↦ physicalBound (I.lower sigma) n
  hi := fun sigma ↦ physicalBound (I.upper sigma) n
  lo_le_hi := by
    intro sigma
    unfold physicalBound
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right (I.lower_lt_upper sigma).le (by positivity)
  physical_separated := hsep
  guards := G.guards
  cell_nonempty := by
    intro c
    simpa only [rawCell] using hnonempty c

@[simp] theorem canonicalSampleData_n
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).n = n := rfl

@[simp] theorem canonicalSampleData_W
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).W = W := rfl

@[simp] theorem canonicalSampleData_pattern
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).pattern = P := rfl

@[simp] theorem canonicalSampleData_lo
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) (sigma : PhysicalSign) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).lo sigma =
      physicalBound (I.lower sigma) n := rfl

@[simp] theorem canonicalSampleData_hi
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) (sigma : PhysicalSign) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).hi sigma =
      physicalBound (I.upper sigma) n := rfl

@[simp] theorem canonicalSampleData_guards
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).guards = G.guards := rfl

@[simp] theorem canonicalSampleData_cellFinset
    (P : Head → Pattern) (I : PhysicalIntervals)
    {n W Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank)
    (hsep) (hnonempty) (c : Cell Head) :
    (canonicalSampleData (W := W) P I G hsep hnonempty).cellFinset c =
      rawCell P I n c \ G.guards := rfl



end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperUniformNuisanceGap -/
section


/-!
# Uniform finite-n nuisance gap from the literal paper cells

The positivity theorem in `PaperBridgeFit` chooses a finite-dimensional
left inverse separately for each `n`.  That proves positivity at a fixed
`n`, but by itself does not produce the constant `gamma_W` used in the
paper.  Here we give the quantitative argument directly.  A common lower
bound for every normalized head/physical cell, a fixed separation between
the two physical means, and a fixed bound for those means imply a covariance
gap with a completely explicit constant.  No limiting mixture occurs.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The selected cell pairs used to reconstruct the physical coordinate
and each nonreference head coordinate. -/
def nuisanceSelectedPair : Option B.HeadIndex -> Cell Head × Cell Head
  | none =>
      ((B.referenceHead, PhysicalSign.plus),
        (B.referenceHead, PhysicalSign.minus))
  | some h =>
      ((h.1, PhysicalSign.minus),
        (B.referenceHead, PhysicalSign.minus))

theorem nuisanceSelectedPair_injective :
    Function.Injective B.nuisanceSelectedPair := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some h =>
          have hfirst := congrArg (fun z => z.1.2) hij
          simp [nuisanceSelectedPair] at hfirst
  | some h =>
      cases j with
      | none =>
          have hfirst := congrArg (fun z => z.1.2) hij
          simp [nuisanceSelectedPair] at hfirst
      | some k =>
          have hhead : h.1 = k.1 := by
            simpa [nuisanceSelectedPair] using
              congrArg (fun z => z.1.1) hij
          exact congrArg some (Subtype.ext hhead)

/-- Exact coordinate expansion of the nuisance Euclidean norm. -/
theorem nuisance_norm_sq_coordinates (x : B.NuisanceSpace) :
    ‖x‖ ^ 2 =
      x NuisanceCoord.physical ^ 2 +
        ∑ h : B.HeadIndex, x (NuisanceCoord.head h) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  let e : NuisanceCoord B.HeadIndex ≃ Option B.HeadIndex :=
    { toFun := fun c => match c with
        | .physical => none
        | .head h => some h
      invFun := fun c => match c with
        | none => .physical
        | some h => .head h
      left_inv := by intro c; cases c <;> rfl
      right_inv := by intro c; cases c <;> rfl }
  calc
    (∑ c : NuisanceCoord B.HeadIndex, x c ^ 2) =
        ∑ c : Option B.HeadIndex, x (e.symm c) ^ 2 := by
      exact Fintype.sum_equiv e (fun c => x c ^ 2)
        (fun c => x (e.symm c) ^ 2) (fun c => by simp)
    _ = x NuisanceCoord.physical ^ 2 +
        ∑ h : B.HeadIndex, x (NuisanceCoord.head h) ^ 2 := by
      rw [Fintype.sum_option]
      rfl

/-- Evaluation of the selected physical pair difference. -/
theorem inner_nuisanceSelectedPair_none [Nonempty Head]
    (x : B.NuisanceSpace) :
    inner ℝ x
        (B.nuisanceCoarseBaseline.pattern
            (B.nuisanceSelectedPair none).1 -
          B.nuisanceCoarseBaseline.pattern
            (B.nuisanceSelectedPair none).2) =
      (B.cellPhysicalMean (B.referenceHead, .plus) -
          B.cellPhysicalMean (B.referenceHead, .minus)) *
        x NuisanceCoord.physical := by
  rw [show (B.nuisanceSelectedPair none).1 =
      (B.referenceHead, PhysicalSign.plus) by rfl,
    show (B.nuisanceSelectedPair none).2 =
      (B.referenceHead, PhysicalSign.minus) by rfl,
    B.nuisancePattern_sameHead_sub B.referenceHead,
    inner_smul_right, EuclideanSpace.inner_single_right]
  simp only [RCLike.conj_to_real, one_mul]

/-- Evaluation of a selected head-pair difference. -/
theorem inner_nuisanceSelectedPair_some [Nonempty Head]
    (x : B.NuisanceSpace) (h : B.HeadIndex) :
    inner ℝ x
        (B.nuisanceCoarseBaseline.pattern
            (B.nuisanceSelectedPair (some h)).1 -
          B.nuisanceCoarseBaseline.pattern
            (B.nuisanceSelectedPair (some h)).2) =
      (B.cellPhysicalMean (h.1, .minus) -
          B.cellPhysicalMean (B.referenceHead, .minus)) *
        x NuisanceCoord.physical + x (NuisanceCoord.head h) := by
  rw [show (B.nuisanceSelectedPair (some h)).1 =
      (h.1, PhysicalSign.minus) by rfl,
    show (B.nuisanceSelectedPair (some h)).2 =
      (B.referenceHead, PhysicalSign.minus) by rfl,
    B.nuisancePattern_head_sub h .minus,
    inner_add_right, inner_smul_right,
    EuclideanSpace.inner_single_right,
    EuclideanSpace.inner_single_right]
  simp only [RCLike.conj_to_real, one_mul]

/-- Sum of the squared scalar differences on the explicitly selected cell
pairs. -/
def nuisanceSelectedSquare [Nonempty Head] (x : B.NuisanceSpace) : ℝ :=
  ∑ o : Option B.HeadIndex,
    (inner ℝ x
      (B.nuisanceCoarseBaseline.pattern (B.nuisanceSelectedPair o).1 -
        B.nuisanceCoarseBaseline.pattern (B.nuisanceSelectedPair o).2)) ^ 2

theorem nuisanceSelectedSquare_eq [Nonempty Head]
    (x : B.NuisanceSpace) :
    B.nuisanceSelectedSquare x =
      ((B.cellPhysicalMean (B.referenceHead, .plus) -
          B.cellPhysicalMean (B.referenceHead, .minus)) *
        x NuisanceCoord.physical) ^ 2 +
      ∑ h : B.HeadIndex,
        ((B.cellPhysicalMean (h.1, .minus) -
            B.cellPhysicalMean (B.referenceHead, .minus)) *
          x NuisanceCoord.physical + x (NuisanceCoord.head h)) ^ 2 := by
  rw [nuisanceSelectedSquare, Fintype.sum_option,
    B.inner_nuisanceSelectedPair_none]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro h _
  rw [B.inner_nuisanceSelectedPair_some]

/-- A conditional physical mean is at most any cellwise upper bound. -/
theorem cellPhysicalMean_le_of_cellwise [Nonempty Head]
    (c : Cell Head) (r : ℝ)
    (hpoint : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = c → B.physicalScore m ≤ r) :
    B.cellPhysicalMean c ≤ r := by
  let s := (Finset.univ : Finset B.sampleData.Sample).filter
    (fun m => B.sampleData.cellOf m = c)
  have hsum :
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m) ≤
      B.nuisanceCoarseBaseline.weight c * r := by
    calc
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m) ≤
          ∑ m ∈ s, B.nuisanceFineBaseline.weight m * r := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left
          (hpoint m (Finset.mem_filter.mp hm).2)
          (B.nuisanceFineBaseline.weight_nonneg m)
      _ = (∑ m ∈ s, B.nuisanceFineBaseline.weight m) * r := by
        rw [Finset.sum_mul]
      _ = B.nuisanceCoarseBaseline.weight c * r := by
        have hmass := B.nuisanceCoarseCertificate.cell_mass c
        simpa only [s] using congrArg (fun z => z * r) hmass
  rw [← B.cellPhysicalMean_mul_weight c] at hsum
  exact (mul_le_mul_iff_right₀
    (B.nuisanceCoarseBaseline_weight_pos c)).mp hsum

/-- A conditional physical mean is at least any cellwise lower bound. -/
theorem le_cellPhysicalMean_of_cellwise [Nonempty Head]
    (c : Cell Head) (r : ℝ)
    (hpoint : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = c → r ≤ B.physicalScore m) :
    r ≤ B.cellPhysicalMean c := by
  let s := (Finset.univ : Finset B.sampleData.Sample).filter
    (fun m => B.sampleData.cellOf m = c)
  have hsum :
      B.nuisanceCoarseBaseline.weight c * r ≤
        ∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
          B.nuisanceFineBaseline.weight m * B.physicalScore m := by
    calc
      B.nuisanceCoarseBaseline.weight c * r =
          (∑ m ∈ s, B.nuisanceFineBaseline.weight m) * r := by
        have hmass := B.nuisanceCoarseCertificate.cell_mass c
        simpa only [s] using (congrArg (fun z => z * r) hmass).symm
      _ = ∑ m ∈ s, B.nuisanceFineBaseline.weight m * r := by
        rw [Finset.sum_mul]
      _ ≤ ∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
          B.nuisanceFineBaseline.weight m * B.physicalScore m := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left
          (hpoint m (Finset.mem_filter.mp hm).2)
          (B.nuisanceFineBaseline.weight_nonneg m)
  rw [← B.cellPhysicalMean_mul_weight c] at hsum
  exact (mul_le_mul_iff_right₀
    (B.nuisanceCoarseBaseline_weight_pos c)).mp hsum

theorem abs_cellPhysicalMean_le_of_cellwise [Nonempty Head]
    (c : Cell Head) (R : ℝ)
    (hpoint : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = c → |B.physicalScore m| ≤ R) :
    |B.cellPhysicalMean c| ≤ R := by
  rw [abs_le]
  constructor
  · apply B.le_cellPhysicalMean_of_cellwise c (-R)
    intro m hm
    exact (abs_le.mp (hpoint m hm)).1
  · apply B.cellPhysicalMean_le_of_cellwise c R
    intro m hm
    exact (abs_le.mp (hpoint m hm)).2

/-- Fixed cellwise physical ranges give the quantitative separation needed
by the uniform covariance theorem. -/
theorem cellPhysicalMean_sub_ge_of_cellwise [Nonempty Head]
    (h : Head) (rminus rplus : ℝ)
    (hminus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (h, .minus) →
        B.physicalScore m ≤ rminus)
    (hplus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (h, .plus) →
        rplus ≤ B.physicalScore m) :
    rplus - rminus ≤
      B.cellPhysicalMean (h, .plus) -
        B.cellPhysicalMean (h, .minus) := by
  have hm := B.cellPhysicalMean_le_of_cellwise (h, .minus) rminus hminus
  have hp := B.le_cellPhysicalMean_of_cellwise (h, .plus) rplus hplus
  linarith

/-- The baseline coarse covariance dominates the selected reconstruction
sum.  This is an exact finite inequality and uses only a common lower bound
for the actual normalized cell masses. -/
theorem nuisanceCoarseBaseline_covariance_ge_selected
    [Nonempty Head] {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (x : B.NuisanceSpace) :
    (lambda ^ 2 / 2) * B.nuisanceSelectedSquare x ≤
      B.nuisanceCoarseBaseline.covarianceForm x := by
  let term : (Cell Head × Cell Head) → ℝ := fun ij =>
    B.nuisanceCoarseBaseline.weight ij.1 *
      B.nuisanceCoarseBaseline.weight ij.2 *
      (inner ℝ x
        (B.nuisanceCoarseBaseline.pattern ij.1 -
          B.nuisanceCoarseBaseline.pattern ij.2)) ^ 2
  have hcoarseWeight : ∀ c : Cell Head,
      lambda ≤ B.nuisanceCoarseBaseline.weight c := by
    intro c
    rw [B.nuisanceCoarseBaseline_weight c]
    exact hweight c
  have hterm_nonneg : ∀ ij, 0 ≤ term ij := by
    intro ij
    exact mul_nonneg
      (mul_nonneg
        (B.nuisanceCoarseBaseline.weight_nonneg ij.1)
        (B.nuisanceCoarseBaseline.weight_nonneg ij.2))
      (sq_nonneg _)
  have hselectedWeight :
      lambda ^ 2 * B.nuisanceSelectedSquare x ≤
        ∑ o : Option B.HeadIndex, term (B.nuisanceSelectedPair o) := by
    rw [nuisanceSelectedSquare, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro o _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hleft := hcoarseWeight (B.nuisanceSelectedPair o).1
    have hright := hcoarseWeight (B.nuisanceSelectedPair o).2
    have hwleft := B.nuisanceCoarseBaseline.weight_nonneg
      (B.nuisanceSelectedPair o).1
    have hwright := B.nuisanceCoarseBaseline.weight_nonneg
      (B.nuisanceSelectedPair o).2
    nlinarith
  have hselectedSubset :
      (∑ o : Option B.HeadIndex, term (B.nuisanceSelectedPair o)) ≤
        ∑ ij : Cell Head × Cell Head, term ij := by
    calc
      (∑ o : Option B.HeadIndex, term (B.nuisanceSelectedPair o)) =
          ∑ ij ∈ (Finset.univ : Finset (Option B.HeadIndex)).image
              B.nuisanceSelectedPair, term ij := by
            rw [Finset.sum_image]
            intro a _ b _ hab
            exact B.nuisanceSelectedPair_injective hab
      _ ≤ ∑ ij ∈ (Finset.univ : Finset (Cell Head × Cell Head)),
            term ij := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _)
            (fun ij _ _ => hterm_nonneg ij)
      _ = ∑ ij : Cell Head × Cell Head, term ij := by simp
  rw [B.nuisanceCoarseBaseline.covarianceForm_pairDifference x]
  calc
    (lambda ^ 2 / 2) * B.nuisanceSelectedSquare x =
        (1 / 2 : ℝ) *
          (lambda ^ 2 * B.nuisanceSelectedSquare x) := by ring
    _ ≤ (1 / 2 : ℝ) *
        (∑ o : Option B.HeadIndex,
          term (B.nuisanceSelectedPair o)) := by
      exact mul_le_mul_of_nonneg_left hselectedWeight (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        (∑ ij : Cell Head × Cell Head, term ij) := by
      exact mul_le_mul_of_nonneg_left hselectedSubset (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j,
        B.nuisanceCoarseBaseline.weight i *
          B.nuisanceCoarseBaseline.weight j *
          (inner ℝ x
            (B.nuisanceCoarseBaseline.pattern i -
              B.nuisanceCoarseBaseline.pattern j)) ^ 2 := by
      simp only [Fintype.sum_prod_type, term]

/-- A uniform geometric denominator.  Its only dimensional dependence is
the fixed number of nonreference head coordinates. -/
def nuisanceGeometryConstant (sep R : ℝ) : ℝ :=
  2 * sep ^ 2 + 1 +
    8 * R ^ 2 * (Fintype.card B.HeadIndex : ℝ)

theorem nuisanceGeometryConstant_pos (sep R : ℝ) :
    0 < B.nuisanceGeometryConstant sep R := by
  unfold nuisanceGeometryConstant
  positivity

/-- One head coordinate is controlled by its selected pair difference and
the physical coordinate, with constants depending only on the common bound
for the physical cell means. -/
theorem headCoordinate_sq_le [Nonempty Head]
    {R : ℝ}
    (hmean : ∀ c : Cell Head, |B.cellPhysicalMean c| ≤ R)
    (x : B.NuisanceSpace) (h : B.HeadIndex) :
    x (NuisanceCoord.head h) ^ 2 ≤
      2 * ((B.cellPhysicalMean (h.1, .minus) -
          B.cellPhysicalMean (B.referenceHead, .minus)) *
        x NuisanceCoord.physical + x (NuisanceCoord.head h)) ^ 2 +
      8 * R ^ 2 * x NuisanceCoord.physical ^ 2 := by
  let r := B.cellPhysicalMean (h.1, .minus) -
    B.cellPhysicalMean (B.referenceHead, .minus)
  let xr := x NuisanceCoord.physical
  let xh := x (NuisanceCoord.head h)
  let q := r * xr + xh
  have hrabs : |r| ≤ 2 * R := by
    calc
      |r| ≤ |B.cellPhysicalMean (h.1, .minus)| +
          |B.cellPhysicalMean (B.referenceHead, .minus)| := by
        simpa only [r] using
          (abs_sub (B.cellPhysicalMean (h.1, .minus))
            (B.cellPhysicalMean (B.referenceHead, .minus)))
      _ ≤ R + R := add_le_add
        (hmean (h.1, .minus))
        (hmean (B.referenceHead, .minus))
      _ = 2 * R := by ring
  have hrsq : r ^ 2 ≤ (2 * R) ^ 2 := by
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg r) hrabs 2)
  have hrx : (r * xr) ^ 2 ≤ 4 * R ^ 2 * xr ^ 2 := by
    calc
      (r * xr) ^ 2 = r ^ 2 * xr ^ 2 := by ring
      _ ≤ (2 * R) ^ 2 * xr ^ 2 :=
        mul_le_mul_of_nonneg_right hrsq (sq_nonneg xr)
      _ = 4 * R ^ 2 * xr ^ 2 := by ring
  have hbasic : xh ^ 2 ≤ 2 * q ^ 2 + 2 * (r * xr) ^ 2 := by
    dsimp only [q]
    nlinarith [sq_nonneg ((r * xr + xh) + r * xr)]
  dsimp only [r, xr, xh, q] at hbasic hrx ⊢
  linarith

theorem headCoordinates_sum_sq_le [Nonempty Head]
    {R : ℝ}
    (hmean : ∀ c : Cell Head, |B.cellPhysicalMean c| ≤ R)
    (x : B.NuisanceSpace) :
    (∑ h : B.HeadIndex, x (NuisanceCoord.head h) ^ 2) ≤
      2 * ∑ h : B.HeadIndex,
        ((B.cellPhysicalMean (h.1, .minus) -
            B.cellPhysicalMean (B.referenceHead, .minus)) *
          x NuisanceCoord.physical + x (NuisanceCoord.head h)) ^ 2 +
      8 * R ^ 2 * (Fintype.card B.HeadIndex : ℝ) *
        x NuisanceCoord.physical ^ 2 := by
  calc
    (∑ h : B.HeadIndex, x (NuisanceCoord.head h) ^ 2) ≤
        ∑ h : B.HeadIndex,
          (2 * ((B.cellPhysicalMean (h.1, .minus) -
              B.cellPhysicalMean (B.referenceHead, .minus)) *
            x NuisanceCoord.physical + x (NuisanceCoord.head h)) ^ 2 +
          8 * R ^ 2 * x NuisanceCoord.physical ^ 2) := by
      apply Finset.sum_le_sum
      intro h _
      exact B.headCoordinate_sq_le hmean x h
    _ = 2 * ∑ h : B.HeadIndex,
          ((B.cellPhysicalMean (h.1, .minus) -
              B.cellPhysicalMean (B.referenceHead, .minus)) *
            x NuisanceCoord.physical + x (NuisanceCoord.head h)) ^ 2 +
        8 * R ^ 2 * (Fintype.card B.HeadIndex : ℝ) *
          x NuisanceCoord.physical ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem physicalCoordinate_sq_le_selected [Nonempty Head]
    {sep : ℝ} (hsep : 0 < sep)
    (hphysical : sep ≤
      B.cellPhysicalMean (B.referenceHead, .plus) -
        B.cellPhysicalMean (B.referenceHead, .minus))
    (x : B.NuisanceSpace) :
    sep ^ 2 * x NuisanceCoord.physical ^ 2 ≤
      ((B.cellPhysicalMean (B.referenceHead, .plus) -
          B.cellPhysicalMean (B.referenceHead, .minus)) *
        x NuisanceCoord.physical) ^ 2 := by
  let d := B.cellPhysicalMean (B.referenceHead, .plus) -
    B.cellPhysicalMean (B.referenceHead, .minus)
  have hd0 : 0 ≤ d := le_trans (le_of_lt hsep) hphysical
  have hsq : sep ^ 2 ≤ d ^ 2 :=
    (sq_le_sq₀ (le_of_lt hsep) hd0).2 hphysical
  calc
    sep ^ 2 * x NuisanceCoord.physical ^ 2 ≤
        d ^ 2 * x NuisanceCoord.physical ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = (d * x NuisanceCoord.physical) ^ 2 := by ring

/-- Quantitative reconstruction inequality for the literal nuisance cell
patterns.  The constant is uniform over `n` once `sep` and `R` are fixed. -/
theorem nuisance_norm_sq_le_selected [Nonempty Head]
    {sep R : ℝ} (hsep : 0 < sep)
    (hphysical : sep ≤
      B.cellPhysicalMean (B.referenceHead, .plus) -
        B.cellPhysicalMean (B.referenceHead, .minus))
    (hmean : ∀ c : Cell Head, |B.cellPhysicalMean c| ≤ R)
    (x : B.NuisanceSpace) :
    sep ^ 2 * ‖x‖ ^ 2 ≤
      B.nuisanceGeometryConstant sep R *
        B.nuisanceSelectedSquare x := by
  let xr := x NuisanceCoord.physical
  let p := (B.cellPhysicalMean (B.referenceHead, .plus) -
      B.cellPhysicalMean (B.referenceHead, .minus)) * xr
  let qs : ℝ := ∑ h : B.HeadIndex,
    ((B.cellPhysicalMean (h.1, .minus) -
        B.cellPhysicalMean (B.referenceHead, .minus)) * xr +
      x (NuisanceCoord.head h)) ^ 2
  let A : ℝ := 1 +
    8 * R ^ 2 * (Fintype.card B.HeadIndex : ℝ)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hqs : 0 ≤ qs := by
    exact Finset.sum_nonneg fun h _ => sq_nonneg _
  have hp : 0 ≤ p ^ 2 := sq_nonneg p
  have hhead := B.headCoordinates_sum_sq_le hmean x
  have hnorm : ‖x‖ ^ 2 ≤ 2 * qs + A * xr ^ 2 := by
    rw [B.nuisance_norm_sq_coordinates]
    dsimp only [qs, A, xr] at hhead ⊢
    linarith
  have hphys : sep ^ 2 * xr ^ 2 ≤ p ^ 2 := by
    simpa only [xr, p] using
      B.physicalCoordinate_sq_le_selected hsep hphysical x
  have hfirst : sep ^ 2 * ‖x‖ ^ 2 ≤
      2 * sep ^ 2 * qs + A * p ^ 2 := by
    calc
      sep ^ 2 * ‖x‖ ^ 2 ≤
          sep ^ 2 * (2 * qs + A * xr ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm (sq_nonneg sep)
      _ = 2 * sep ^ 2 * qs + A * (sep ^ 2 * xr ^ 2) := by ring
      _ ≤ 2 * sep ^ 2 * qs + A * p ^ 2 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hphys hA) _
  have hsecond : 2 * sep ^ 2 * qs + A * p ^ 2 ≤
      (2 * sep ^ 2 + A) * (p ^ 2 + qs) := by
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sq_nonneg sep)) hp, mul_nonneg hA hqs]
  rw [B.nuisanceSelectedSquare_eq]
  change sep ^ 2 * ‖x‖ ^ 2 ≤
    B.nuisanceGeometryConstant sep R * (p ^ 2 + qs)
  have hconstant : B.nuisanceGeometryConstant sep R =
      2 * sep ^ 2 + A := by
    simp only [nuisanceGeometryConstant, A]
    ring
  rw [hconstant]
  exact hfirst.trans hsecond

/-- Explicit positive constant for the uniform baseline nuisance gap. -/
def uniformNuisanceGap (lambda sep R : ℝ) : ℝ :=
  lambda ^ 2 * sep ^ 2 /
    (2 * B.nuisanceGeometryConstant sep R)

theorem uniformNuisanceGap_pos
    {lambda sep R : ℝ} (hlambda : 0 < lambda) (hsep : 0 < sep) :
    0 < B.uniformNuisanceGap lambda sep R := by
  exact div_pos (mul_pos (sq_pos_of_pos hlambda) (sq_pos_of_pos hsep))
    (mul_pos (by norm_num) (B.nuisanceGeometryConstant_pos sep R))

/-- Uniform finite-`n` baseline covariance bound.  In contrast with
`nuisanceBaselineGap`, this gap depends only on the three displayed common
geometric constants, not on a separately chosen inverse at the current `n`. -/
theorem nuisanceFineBaseline_uniform_gap [Nonempty Head]
    {lambda sep R : ℝ} (hlambda : 0 < lambda)
    (hsep : 0 < sep)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (hphysical : sep ≤
      B.cellPhysicalMean (B.referenceHead, .plus) -
        B.cellPhysicalMean (B.referenceHead, .minus))
    (hmean : ∀ c : Cell Head, |B.cellPhysicalMean c| ≤ R)
    (x : B.NuisanceSpace) :
    B.uniformNuisanceGap lambda sep R * ‖x‖ ^ 2 ≤
      B.nuisanceFineBaseline.covarianceForm x := by
  have hgeom := B.nuisance_norm_sq_le_selected
    hsep hphysical hmean x
  have hcoarse := B.nuisanceCoarseBaseline_covariance_ge_selected
    (le_of_lt hlambda) hweight x
  have hC : 0 < B.nuisanceGeometryConstant sep R :=
    B.nuisanceGeometryConstant_pos sep R
  have hscale : 0 ≤ lambda ^ 2 /
      (2 * B.nuisanceGeometryConstant sep R) := by positivity
  calc
    B.uniformNuisanceGap lambda sep R * ‖x‖ ^ 2 =
        (lambda ^ 2 /
          (2 * B.nuisanceGeometryConstant sep R)) *
            (sep ^ 2 * ‖x‖ ^ 2) := by
      unfold uniformNuisanceGap
      field_simp [ne_of_gt hC]
    _ ≤ (lambda ^ 2 /
          (2 * B.nuisanceGeometryConstant sep R)) *
            (B.nuisanceGeometryConstant sep R *
              B.nuisanceSelectedSquare x) :=
      mul_le_mul_of_nonneg_left hgeom hscale
    _ = (lambda ^ 2 / 2) * B.nuisanceSelectedSquare x := by
      field_simp [ne_of_gt hC]
    _ ≤ B.nuisanceCoarseBaseline.covarianceForm x := hcoarse
    _ ≤ B.nuisanceFineBaseline.covarianceForm x :=
      B.nuisanceCoarseCertificate.coarse_covarianceForm_le_fine x

/-- Operator form of the same baseline bound. -/
theorem nuisanceCovarianceOperator_zero_uniform_gap [Nonempty Head]
    {lambda sep R : ℝ} (hlambda : 0 < lambda)
    (hsep : 0 < sep)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (hphysical : sep ≤
      B.cellPhysicalMean (B.referenceHead, .plus) -
        B.cellPhysicalMean (B.referenceHead, .minus))
    (hmean : ∀ c : Cell Head, |B.cellPhysicalMean c| ≤ R)
    (x : B.NuisanceSpace) :
    B.uniformNuisanceGap lambda sep R * ‖x‖ ^ 2 ≤
      inner ℝ x (B.nuisanceCovarianceOperator 0 x) := by
  rw [B.nuisanceCovarianceOperator_quadratic, B.nuisanceFineAt_zero]
  exact B.nuisanceFineBaseline_uniform_gap hlambda hsep
    hweight hphysical hmean x

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperHeadSimplex -/
section


/-!
# The literal finite head-pattern simplex used in Section 8

For a fixed finite head-prime set `P` and a positive exponent `E`, the paper
uses the vertices `0` and `E e_p`.  This module constructs those exact
valuation patterns and proves that two different vertices cannot contain the
same positive integer.  The result discharges the cell-disjointness premise
used when tagged structured cells are returned to literal integer
coordinates.
-/

namespace Erdos390.Full.PaperHeadSimplex

noncomputable section

/-- `none` is the zero pattern and `some p` is the vertex `E e_p`. -/
abbrev Tag (P : Finset Nat) := Option {p : Nat // p ∈ P}

/-- Exact exponent vector of one simplex vertex. -/
def exponent (P : Finset Nat) (E : Nat) (tag : Tag P) (r : Nat) : Nat :=
  match tag with
  | none => 0
  | some p => if r = p.1 then E else 0

/-- All vertices prescribe valuations at the same finite prime set. -/
def pattern (P : Finset Nat) (hprime : ∀ p ∈ P, p.Prime)
    (E : Nat) (tag : Tag P) : HeadPattern.Pattern where
  primes := P
  exponent := exponent P E tag
  prime_mem := hprime

@[simp] theorem exponent_none (P : Finset Nat) (E r : Nat) :
    exponent P E (none : Tag P) r = 0 := rfl

@[simp] theorem exponent_some_self (P : Finset Nat) (E : Nat)
    (p : {p : Nat // p ∈ P}) :
    exponent P E (some p) p.1 = E := by
  simp [exponent]

@[simp] theorem exponent_some_ne (P : Finset Nat) (E : Nat)
    (p : {p : Nat // p ∈ P}) (r : Nat) (hr : r ≠ p.1) :
    exponent P E (some p) r = 0 := by
  simp [exponent, hr]



end

end Erdos390.Full.PaperHeadSimplex

end

/- Source module: Erdos390.Full.PaperBridgeFitFeasibility -/
section


/-!
# Feasibility and frozen-ledger consequences of the actual bridge tilt

The nonlinear bridge changes only the active structured-cell coordinates.
This file records, for the literal finite exponential family used in
`PaperBridgeFit`, the conclusions which are independent of the analytic
covariance estimates: positivity, preservation of the active mass, an
explicit coordinate ceiling on a preselected parameter ball, and literal
preservation of every frozen top/protected coordinate and integer quota.

The coordinate ceiling is not postulated as a property of the output.  It is
deduced from the exact finite density-ratio estimate and an explicit baseline
slack inequality.  In the final Proposition 8.7 specialization that baseline
slack is discharged by the structured-cell count and the paper's `O(1/L)`
baseline-coordinate bound.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteExponentialFamily

namespace StructuredSampleData

variable {Head : Type*} [Fintype Head]

/-- The finite head patterns used by the bridge are pairwise separated when
two different tags prescribe different valuations at a common head prime. -/
def HeadPatternsSeparated (D : StructuredSampleData Head) : Prop :=
  forall h k, h ≠ k -> exists p,
    p ∈ (D.pattern h).primes ∧
    p ∈ (D.pattern k).primes ∧
    (D.pattern h).exponent p ≠ (D.pattern k).exponent p

/-- Physical separation and separated head valuations make the tagged
disjointification injective on the underlying natural-number coordinate. -/
theorem value_injective_of_headPatternsSeparated
    (D : StructuredSampleData Head) (hsep : D.HeadPatternsSeparated) :
    Function.Injective D.value := by
  intro m k hvalue
  have hsign : (D.cellOf m).2 = (D.cellOf k).2 := by
    cases hm : (D.cellOf m).2 <;> cases hk : (D.cellOf k).2
    · rfl
    · have hmhi : D.value m <= D.hi .minus := by
        simpa [hm] using D.value_le_hi m
      have hklo : D.lo .plus < D.value k := by
        simpa [hk] using D.lo_lt_value k
      rw [hvalue] at hmhi
      have hsepPhysical := D.physical_separated
      omega
    · have hmlo : D.lo .plus < D.value m := by
        simpa [hm] using D.lo_lt_value m
      have hkhi : D.value k <= D.hi .minus := by
        simpa [hk] using D.value_le_hi k
      rw [hvalue] at hmlo
      have hsepPhysical := D.physical_separated
      omega
    · rfl
  have hhead : (D.cellOf m).1 = (D.cellOf k).1 := by
    by_contra hne
    obtain ⟨p, hpm, hpk, hpne⟩ :=
      hsep (D.cellOf m).1 (D.cellOf k).1 hne
    have hmm := D.value_matches_head m p hpm
    have hkm := D.value_matches_head k p hpk
    apply hpne
    rw [← hmm, ← hkm, hvalue]
  have hcell : D.cellOf m = D.cellOf k := Prod.ext hhead hsign
  rcases m with ⟨cm, ⟨vm, hvm⟩⟩
  rcases k with ⟨ck, ⟨vk, hvk⟩⟩
  simp only [cellOf] at hcell
  simp only [value] at hvalue
  subst ck
  have hv : (⟨vm, hvm⟩ : D.SampleAt cm) = ⟨vk, hvk⟩ :=
    Subtype.ext hvalue
  cases hv
  rfl



end StructuredSampleData

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual active coordinate weight at a bridge parameter. -/
def activeCoordinateWeight [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) : Real :=
  B.vectorFamily.scalarFamily.activeWeight xi m









/-! The paper uses a compact *effective-score* box, not the crude sum of
all score norms.  The next estimates therefore take the correct pointwise
score bound and have constants independent of the number of active cells. -/













/-! ## Actual natural-number coordinates -/

/-- Active mass accumulated at one literal integer coordinate.  Under the
paper's disjoint-cell property the sum contains at most one term. -/
def ambientActiveWeight [Nonempty Head]
    (xi : B.ParamSpace) (a : Nat) : Real :=
  Finset.univ.sum fun m : B.sampleData.Sample =>
    if B.sampleData.value m = a then B.activeCoordinateWeight xi m else 0







/-- Total weight at a literal integer coordinate when the frozen
top/protected contribution may overlap the active smooth sample. -/
def ambientCombinedWeight [Nonempty Head]
    (frozenWeight : Nat -> Real) (xi : B.ParamSpace) (a : Nat) : Real :=
  frozenWeight a + B.ambientActiveWeight xi a







/-! ## Frozen top/protected coordinates and the integer ledger -/

/-- The total bridge vector on a tagged disjoint union.  The left summand is
every frozen top/protected/other coordinate; the right summand is the active
structured sample. -/
def combinedWeight [Nonempty Head]
    {Fixed : Type*} (fixedWeight : Fixed -> Real)
    (xi : B.ParamSpace) : Fixed ⊕ B.sampleData.Sample -> Real
  | Sum.inl f => fixedWeight f
  | Sum.inr m => B.activeCoordinateWeight xi m

@[simp] theorem combinedWeight_fixed [Nonempty Head]
    {Fixed : Type*} (fixedWeight : Fixed -> Real)
    (xi : B.ParamSpace) (f : Fixed) :
    B.combinedWeight fixedWeight xi (Sum.inl f) = fixedWeight f := rfl

@[simp] theorem combinedWeight_active [Nonempty Head]
    {Fixed : Type*} (fixedWeight : Fixed -> Real)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.combinedWeight fixedWeight xi (Sum.inr m) =
      B.activeCoordinateWeight xi m := rfl











end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Lemma75 -/
section


/-!
# The finite algebraic core of Lemma 7.5

This file formalizes the part of Lemma 7.5 which is independent of the
marked-friable asymptotics.  The analytic estimates enter only as explicit
hypotheses.  The reciprocal weight `u i` is instantiated in the paper by
`1 / p`, `rowScale i` by `p`, and `invW` by `1 / W`.
-/

open scoped BigOperators

namespace Erdos390.Lemma75

/-- A probability distribution on a finite type, kept in `ℝ` so that all
expectation and covariance identities reduce to finite-sum algebra. -/
structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  mass_sum : ∑ ω, mass ω = 1

namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]

def expect (μ : FiniteProbability Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, μ.mass ω * X ω

def covariance (μ : FiniteProbability Ω) (X Y : Ω → ℝ) : ℝ :=
  μ.expect (fun ω => X ω * Y ω) - μ.expect X * μ.expect Y

def variance (μ : FiniteProbability Ω) (X : Ω → ℝ) : ℝ :=
  μ.covariance X X

@[simp] theorem expect_zero (μ : FiniteProbability Ω) :
    μ.expect (fun _ => 0) = 0 := by
  simp [expect]







@[simp] theorem expect_const (μ : FiniteProbability Ω) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, μ.mass_sum]

































end FiniteProbability

section PrimePowerAlgebra

variable {Ω ι κ : Type*} [Fintype Ω]

















end PrimePowerAlgebra

section FiniteContraction

variable {Ω ι κ : Type*} [Fintype Ω]





















end FiniteContraction

end Erdos390.Lemma75

end

/- Source module: Erdos390.Full.PrimePowerRowTransfer -/
section


/-!
# Actual finite-law row contraction for prime powers

The original finite contraction theorem in `Erdos390.Lemma75` is pure
finite-sum algebra, but it was stated for the audit companion's duplicate
probability structure.  This file transports that theorem definitionally to
the genuine `Full.FiniteProbability` and then specializes it to the actual
valuation columns of `BoundedValuationLaw`.

No analytic covariance estimate is asserted here.  The point is that once the
actual `JI`, `IJ`, `JJ`, diagonal, prime-sum, and endpoint bounds are proved,
their contraction to the paper's full-valuation row norm is now a theorem
about the same probability law and the same valuation functions.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerRowTransfer

noncomputable section

open Erdos390.Full
open Erdos390.Full.PrimePowerCovariance

variable {Omega Iota : Type*} [Fintype Omega]

set_option maxHeartbeats 800000

/-- The duplicate audit probability structure has exactly the same data as
the full finite probability structure. -/
def toLegacyProbability (mu : Erdos390.Full.FiniteProbability Omega) :
    Erdos390.Lemma75.FiniteProbability Omega where
  mass := mu.mass
  mass_nonneg := mu.mass_nonneg
  mass_sum := mu.mass_sum

@[simp] theorem toLegacyProbability_expect
    (mu : Erdos390.Full.FiniteProbability Omega) (F : Omega -> Real) :
    (toLegacyProbability mu).expect F = mu.expect F := rfl

@[simp] theorem toLegacyProbability_covariance
    (mu : Erdos390.Full.FiniteProbability Omega) (F G : Omega -> Real) :
    (toLegacyProbability mu).covariance F G = mu.covariance F G := rfl



namespace BoundedValuationLaw

variable {M : Nat} (law : BoundedValuationLaw Omega M)



end BoundedValuationLaw

end

end Erdos390.Full.PrimePowerRowTransfer

end

/- Source module: Erdos390.Full.PaperStatisticNorm -/
section


/-!
# An actual `O(log n)` bound for the paper bridge statistic

This file discharges the pointwise statistic-norm hypothesis used by the
finite feasibility layer of Proposition 8.7.  The proof uses the genuine
valuation statistic on the actual prime band, the physical interval bound,
and fixed mesh/head constants.  No covariance or ODE conclusion is assumed.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperStatisticNorm

open ArithmeticModel Scale ValuationTiltCell
open PaperBridgeFit

noncomputable section

/-- Converts the fixed physical ceiling `C n` to a multiple of `log n`. -/
def physicalLogCoefficient (C : ℝ) : ℝ :=
  1 + Real.log C / Real.log 2

/-- Converts the total band valuation to a multiple of `log n`. -/
def valuationLogCoefficient (C : ℝ) (W : ℕ) : ℝ :=
  physicalLogCoefficient C / Real.log (W : ℝ)





lemma physicalLogCoefficient_nonneg {C : ℝ} (hC : 1 ≤ C) :
    0 ≤ physicalLogCoefficient C := by
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold physicalLogCoefficient
  positivity

lemma valuationLogCoefficient_nonneg {C : ℝ} {W : ℕ}
    (hC : 1 ≤ C) (hW : 1 < W) :
    0 ≤ valuationLogCoefficient C W := by
  unfold valuationLogCoefficient
  exact div_nonneg (physicalLogCoefficient_nonneg hC)
    (Real.log_pos (by exact_mod_cast hW)).le





namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

lemma log_two_le_L : Real.log 2 ≤ B.L := by
  unfold PaperBridgeFit.BridgeData.L
  apply Real.log_le_log (by norm_num)
  exact_mod_cast B.n_gt_one

/-- The actual physical endpoint has logarithm at most the displayed fixed
multiple of `L=log n`. -/
theorem log_physicalBound_le
    {C : ℝ} (hC : 1 ≤ C) :
    Real.log (physicalBound C B.sampleData.n : ℝ) ≤
      physicalLogCoefficient C * B.L := by
  have hn0 : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
  have hnR : (0 : ℝ) < (B.sampleData.n : ℝ) := by exact_mod_cast hn0
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hphysical : B.sampleData.n ≤ physicalBound C B.sampleData.n := by
    unfold physicalBound
    apply Nat.le_floor
    exact_mod_cast (show (B.sampleData.n : ℝ) ≤
      C * (B.sampleData.n : ℝ) by
        nlinarith [show (0 : ℝ) ≤ (B.sampleData.n : ℝ) by positivity])
  have hMpos : (0 : ℝ) < (physicalBound C B.sampleData.n : ℝ) := by
    exact_mod_cast hn0.trans_le hphysical
  have hMcast : (physicalBound C B.sampleData.n : ℝ) ≤
      C * (B.sampleData.n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hCpos.le hnR.le)
  have hlogM : Real.log (physicalBound C B.sampleData.n : ℝ) ≤
      Real.log C + B.L := by
    calc
      Real.log (physicalBound C B.sampleData.n : ℝ) ≤
          Real.log (C * (B.sampleData.n : ℝ)) :=
        Real.log_le_log hMpos hMcast
      _ = Real.log C + Real.log (B.sampleData.n : ℝ) := by
        rw [Real.log_mul hCpos.ne' hnR.ne']
      _ = Real.log C + B.L := by rfl
  have hlogC0 : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCL : Real.log C ≤ (Real.log C / Real.log 2) * B.L := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hlog2).2
      (mul_le_mul_of_nonneg_left (log_two_le_L B) hlogC0)
  calc
    Real.log (physicalBound C B.sampleData.n : ℝ) ≤
        Real.log C + B.L := hlogM
    _ ≤ physicalLogCoefficient C * B.L := by
      unfold physicalLogCoefficient
      nlinarith

/-- Total valuation on the genuine prime band is `O(L)` with an explicit
fixed-cutoff coefficient. -/
theorem totalBandValuation_le
    {C : ℝ} (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (m : B.sampleData.Sample) :
    (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        valuation p (B.sampleData.value m)) ≤
      valuationLogCoefficient C B.sampleData.W * B.L := by
  have hm := B.sampleData.value_pos m
  have hmM : B.sampleData.value m ≤ physicalBound C B.sampleData.n :=
    (B.sampleData.value_le_hi m).trans (hhi (B.sampleData.cellOf m).2)
  have hpW : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      B.sampleData.W ≤ p := by
    intro p hp
    exact (cutoff_lt_of_mem_primeBand hp).le
  have hraw := sum_valuation_le_log_ratio
    (primeBand B.sampleData.n B.sampleData.W) hm hmM hW hpW
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  calc
    _ ≤ Real.log (physicalBound C B.sampleData.n : ℝ) /
        Real.log (B.sampleData.W : ℝ) := hraw
    _ ≤ (physicalLogCoefficient C * B.L) /
        Real.log (B.sampleData.W : ℝ) :=
      div_le_div_of_nonneg_right (log_physicalBound_le B hC) hlogW.le
    _ = valuationLogCoefficient C B.sampleData.W * B.L := by
      unfold valuationLogCoefficient
      ring











theorem log_C_le_physicalLogCoefficient_mul_L
    {C : ℝ} (hC : 1 ≤ C) :
    Real.log C ≤ physicalLogCoefficient C * B.L := by
  have hlogC0 : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCL : Real.log C ≤ (Real.log C / Real.log 2) * B.L := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hlog2).2
      (mul_le_mul_of_nonneg_left (log_two_le_L B) hlogC0)
  unfold physicalLogCoefficient
  nlinarith [B.L_pos]

/-- The physical logarithm is uniformly `O(L)` on the two actual physical
pools. -/
theorem abs_physicalScore_le
    {C : ℝ} (hC : 1 ≤ C)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (m : B.sampleData.Sample) :
    |B.physicalScore m| ≤ physicalLogCoefficient C * B.L := by
  have hn0 : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
  have hnR : (0 : ℝ) < (B.sampleData.n : ℝ) := by exact_mod_cast hn0
  have hm0 := B.sampleData.value_pos m
  have hmR : (0 : ℝ) < (B.sampleData.value m : ℝ) := by exact_mod_cast hm0
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hmM : B.sampleData.value m ≤ physicalBound C B.sampleData.n :=
    (B.sampleData.value_le_hi m).trans (hhi (B.sampleData.cellOf m).2)
  have hMcast : (physicalBound C B.sampleData.n : ℝ) ≤
      C * (B.sampleData.n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hCpos.le hnR.le)
  have hmUpper : (B.sampleData.value m : ℝ) ≤
      C * (B.sampleData.n : ℝ) :=
    (by exact_mod_cast hmM : (B.sampleData.value m : ℝ) ≤
      (physicalBound C B.sampleData.n : ℝ)).trans hMcast
  have hratioPos : 0 < (B.sampleData.value m : ℝ) /
      (B.sampleData.n : ℝ) := div_pos hmR hnR
  have hratioUpper : (B.sampleData.value m : ℝ) /
      (B.sampleData.n : ℝ) ≤ C := (div_le_iff₀ hnR).2 (by
        simpa only [mul_comm] using hmUpper)
  have hratioLower : 1 / (B.sampleData.n : ℝ) ≤
      (B.sampleData.value m : ℝ) / (B.sampleData.n : ℝ) := by
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast hm0 : (1 : ℝ) ≤ B.sampleData.value m) hnR.le
  have hlogUpper : B.physicalScore m ≤ Real.log C := by
    unfold PaperBridgeFit.BridgeData.physicalScore
    exact Real.log_le_log hratioPos hratioUpper
  have hlogLower : -B.L ≤ B.physicalScore m := by
    have hlog := Real.log_le_log (one_div_pos.mpr hnR) hratioLower
    unfold PaperBridgeFit.BridgeData.physicalScore
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hnR.ne',
      Real.log_one, zero_sub] at hlog
    exact hlog
  have hPL : B.L ≤ physicalLogCoefficient C * B.L := by
    have hPone : 1 ≤ physicalLogCoefficient C := by
      unfold physicalLogCoefficient
      have : 0 ≤ Real.log C / Real.log 2 :=
        div_nonneg (Real.log_nonneg hC)
          (Real.log_pos (by norm_num)).le
      linarith
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hPone B.L_pos.le)
  rw [abs_le]
  constructor
  · linarith
  · exact hlogUpper.trans (log_C_le_physicalLogCoefficient_mul_L B hC)

theorem normalizedCellMass_le_one [Nonempty Head]
    (c : Cell Head) : B.baseline.normalizedCellMass c ≤ 1 := by
  rw [← B.baseline.normalizedCellMass_sum]
  exact Finset.single_le_sum
    (fun d hd ↦ (B.baseline.normalizedCellMass_pos d).le)
    (Finset.mem_univ c)

theorem headBaselineMass_nonneg [Nonempty Head] (h : Head) :
    0 ≤ B.headBaselineMass h := by
  unfold PaperBridgeFit.BridgeData.headBaselineMass
  exact Finset.sum_nonneg fun sigma hsigma ↦
    (B.baseline.normalizedCellMass_pos (h, sigma)).le

theorem headBaselineMass_le_two [Nonempty Head] (h : Head) :
    B.headBaselineMass h ≤ 2 := by
  unfold PaperBridgeFit.BridgeData.headBaselineMass
  calc
    (∑ sigma : PhysicalSign,
        B.baseline.normalizedCellMass (h, sigma)) ≤
        ∑ _sigma : PhysicalSign, (1 : ℝ) := by
      exact Finset.sum_le_sum fun sigma hsigma ↦
        normalizedCellMass_le_one B (h, sigma)
    _ = 2 := by
      have hcard : Fintype.card PhysicalSign = 2 := by rfl
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard

theorem abs_centeredHeadScore_le_three [Nonempty Head]
    (h : B.HeadIndex) (m : B.sampleData.Sample) :
    |B.centeredHeadScore h m| ≤ 3 := by
  have hI0 : 0 ≤ B.headIndicator h.1 m := by
    unfold PaperBridgeFit.BridgeData.headIndicator
    split <;> norm_num
  have hI1 : B.headIndicator h.1 m ≤ 1 := by
    unfold PaperBridgeFit.BridgeData.headIndicator
    split <;> norm_num
  have hH0 := headBaselineMass_nonneg B h.1
  have hH2 := headBaselineMass_le_two B h.1
  unfold PaperBridgeFit.BridgeData.centeredHeadScore
  rw [abs_le]
  constructor <;> linarith





theorem three_le_headCoefficient_mul_L :
    (3 : ℝ) ≤ (3 / Real.log 2) * B.L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (3 : ℝ) = (3 / Real.log 2) * Real.log 2 := by field_simp
    _ ≤ (3 / Real.log 2) * B.L :=
      mul_le_mul_of_nonneg_left (log_two_le_L B) (by positivity)









end BridgeData

end

end Erdos390.Full.PaperStatisticNorm

end

/- Source module: Erdos390.Full.PaperPhysicalIntervalNuisanceGap -/
section


/-!
# Uniform nuisance geometry from the fixed physical intervals

The paper fixes two scaled intervals `(a_sigma n, b_sigma n]`.  This file
connects their literal floored natural endpoints to the physical logarithm
used by `BridgeData`.  It produces the fixed separation and fixed bound
required by `PaperUniformNuisanceGap`; neither constant depends on `n`.
-/

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel PaperGuardCensus

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- A sample in a floored scaled physical cell lies below the corresponding
fixed real upper endpoint after division by `n`. -/
theorem physicalScore_le_log_upper
    (I : PaperGuardCensus.PhysicalIntervals)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (m : B.sampleData.Sample) :
    B.physicalScore m ≤ Real.log (I.upper (B.sampleData.cellOf m).2) := by
  let sigma := (B.sampleData.cellOf m).2
  have hn : (0 : ℝ) < B.sampleData.n := by
    exact_mod_cast (Nat.zero_lt_of_lt B.n_gt_one)
  have hv : (0 : ℝ) < B.sampleData.value m := by
    exact_mod_cast B.sampleData.value_pos m
  have hmleNat : B.sampleData.value m ≤
      physicalBound (I.upper sigma) B.sampleData.n := by
    simpa only [sigma, hhi] using B.sampleData.value_le_hi m
  have hmle : (B.sampleData.value m : ℝ) ≤
      (physicalBound (I.upper sigma) B.sampleData.n : ℝ) := by
    exact_mod_cast hmleNat
  have hfloor : (physicalBound (I.upper sigma) B.sampleData.n : ℝ) ≤
      I.upper sigma * (B.sampleData.n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg
      (le_of_lt ((I.lower_pos sigma).trans (I.lower_lt_upper sigma)))
      (Nat.cast_nonneg _))
  have hratio :
      (B.sampleData.value m : ℝ) / (B.sampleData.n : ℝ) ≤
        I.upper sigma := by
    apply (div_le_iff₀ hn).2
    exact hmle.trans hfloor
  unfold physicalScore
  exact Real.log_le_log (div_pos hv hn) hratio

/-- The strict lower endpoint survives the natural floor because the sample
coordinate is an integer strictly above that floor. -/
theorem log_lower_lt_physicalScore
    (I : PaperGuardCensus.PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (m : B.sampleData.Sample) :
    Real.log (I.lower (B.sampleData.cellOf m).2) < B.physicalScore m := by
  let sigma := (B.sampleData.cellOf m).2
  have hn : (0 : ℝ) < B.sampleData.n := by
    exact_mod_cast (Nat.zero_lt_of_lt B.n_gt_one)
  have hmgtNat : physicalBound (I.lower sigma) B.sampleData.n <
      B.sampleData.value m := by
    simpa only [sigma, hlo] using B.sampleData.lo_lt_value m
  have hfloorlt : I.lower sigma * (B.sampleData.n : ℝ) <
      (physicalBound (I.lower sigma) B.sampleData.n : ℝ) + 1 := by
    unfold physicalBound
    exact Nat.lt_floor_add_one _
  have hsuccNat : physicalBound (I.lower sigma) B.sampleData.n + 1 ≤
      B.sampleData.value m := by omega
  have hsucc :
      (physicalBound (I.lower sigma) B.sampleData.n : ℝ) + 1 ≤
        (B.sampleData.value m : ℝ) := by
    exact_mod_cast hsuccNat
  have hscaled : I.lower sigma * (B.sampleData.n : ℝ) <
      (B.sampleData.value m : ℝ) := hfloorlt.trans_le hsucc
  have hratio : I.lower sigma <
      (B.sampleData.value m : ℝ) / (B.sampleData.n : ℝ) := by
    apply (lt_div_iff₀ hn).2
    simpa only [mul_comm] using hscaled
  unfold physicalScore
  exact Real.log_lt_log (I.lower_pos sigma) hratio

/-- If all fixed lower endpoints exceed one and all upper endpoints are at
most `U`, every physical logarithm is nonnegative and at most `log U`. -/
theorem abs_physicalScore_le_log_upperBound
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (m : B.sampleData.Sample) :
    |B.physicalScore m| ≤ Real.log U := by
  have hlower := B.log_lower_lt_physicalScore I hlo m
  have hlowerLog : 0 ≤
      Real.log (I.lower (B.sampleData.cellOf m).2) :=
    Real.log_nonneg (hlowerOne _)
  have hscore0 : 0 ≤ B.physicalScore m :=
    hlowerLog.trans hlower.le
  rw [abs_of_nonneg hscore0]
  exact (B.physicalScore_le_log_upper I hhi m).trans
    (Real.log_le_log
      ((I.lower_pos _).trans (I.lower_lt_upper _))
      (hupperU _))

/-- The two fixed physical pools give a quantitative gap between their
conditional means. -/
theorem fixedInterval_cellPhysicalMean_separation [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (h : Head) :
    Real.log (I.lower .plus) - Real.log (I.upper .minus) ≤
      B.cellPhysicalMean (h, .plus) -
        B.cellPhysicalMean (h, .minus) := by
  apply B.cellPhysicalMean_sub_ge_of_cellwise h
    (Real.log (I.upper .minus)) (Real.log (I.lower .plus))
  · intro m hm
    exact (B.physicalScore_le_log_upper I hhi m).trans_eq (by
      congr 1
      exact congrArg I.upper (congrArg Prod.snd hm))
  · intro m hm
    exact (B.log_lower_lt_physicalScore I hlo m).le.trans_eq' (by
      congr 1
      exact congrArg I.lower (congrArg Prod.snd hm))

/-- Uniform absolute bound for every conditional physical mean. -/
theorem fixedInterval_abs_cellPhysicalMean_le [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (c : Cell Head) :
    |B.cellPhysicalMean c| ≤ Real.log U := by
  apply B.abs_cellPhysicalMean_le_of_cellwise c (Real.log U)
  intro m hm
  exact B.abs_physicalScore_le_log_upperBound I
    hlowerOne hupperU hlo hhi m











theorem fixedInterval_separation_pos
    (I : PaperGuardCensus.PhysicalIntervals) :
    0 < Real.log (I.lower .plus) - Real.log (I.upper .minus) := by
  have hminus : I.upper .minus ∈ Set.Ioi (0 : ℝ) :=
    (I.lower_pos .minus).trans (I.lower_lt_upper .minus)
  have hplus : I.lower .plus ∈ Set.Ioi (0 : ℝ) := I.lower_pos .plus
  exact sub_pos.mpr (Real.strictMonoOn_log hminus hplus I.separated)

/-- The uniform baseline nuisance gap specialized to the literal fixed
physical intervals.  Once the common normalized cell-mass margin `lambda`
is supplied by the barycentric active-measure construction, the conclusion
contains no `n`-dependent gap and no limiting covariance. -/
theorem nuisanceCovarianceOperator_zero_fixedIntervals
    [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals) {U lambda : ℝ}
    (hlambda : 0 < lambda)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (x : B.NuisanceSpace) :
    B.uniformNuisanceGap lambda
        (Real.log (I.lower .plus) - Real.log (I.upper .minus))
        (Real.log U) * ‖x‖ ^ 2 ≤
      inner ℝ x (B.nuisanceCovarianceOperator 0 x) := by
  apply B.nuisanceCovarianceOperator_zero_uniform_gap
    hlambda (fixedInterval_separation_pos I) hweight
  · exact B.fixedInterval_cellPhysicalMean_separation I hlo hhi
      B.referenceHead
  · exact B.fixedInterval_abs_cellPhysicalMean_le I
      hlowerOne hupperU hlo hhi



end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

/- Source module: Erdos390.Full.PaperCanonicalBaseline -/
section


/-!
# Canonical barycentric baseline allocation

The active bridge first fixes positive head barycentric masses and then mixes
the two separated physical pools to hit the required logarithmic moment.
This file performs that construction exactly on the literal guarded finite
cells.  The resulting common cell-mass margin is an output.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperGuardCensus

open PaperBridgeFit ArithmeticModel

noncomputable section

variable {Head : Type*} [Fintype Head] [Nonempty Head]

theorem sum_physicalSign (f : PhysicalSign → ℝ) :
    ∑ sigma : PhysicalSign, f sigma = f .minus + f .plus := by
  have huniv : (Finset.univ : Finset PhysicalSign) =
      {.minus, .plus} := by decide
  rw [huniv]
  simp

/-- Uniform physical-log mean of one actual guard-deleted cell. -/
def cellLogMean (D : StructuredSampleData Head) (c : Cell Head) : ℝ :=
  (∑ m : D.SampleAt c,
      Real.log ((m.1 : ℝ) / (D.n : ℝ))) /
    Fintype.card (D.SampleAt c)

/-- Head-barycentric mean in one physical pool. -/
def poolLogMean (D : StructuredSampleData Head)
    (beta : Head → ℝ) (sigma : PhysicalSign) : ℝ :=
  ∑ h : Head, beta h * cellLogMean D (h, sigma)

/-- The physical mixing coordinate which hits `mu`. -/
def physicalMixingWeight (D : StructuredSampleData Head)
    (beta : Head → ℝ) (mu : ℝ) : ℝ :=
  (mu - poolLogMean D beta .minus) /
    (poolLogMean D beta .plus - poolLogMean D beta .minus)

/-- Positive head barycentric data and a quantitatively interior physical
target.  These are the finite reserve choices made before the covariance
argument; no covariance or inverse conclusion is stored here. -/
structure BarycentricTarget (D : StructuredSampleData Head) where
  beta : Head → ℝ
  beta_pos : ∀ h, 0 < beta h
  beta_sum : ∑ h, beta h = 1
  betaFloor : ℝ
  betaFloor_pos : 0 < betaFloor
  betaFloor_le : ∀ h, betaFloor ≤ beta h
  mu : ℝ
  tau : ℝ
  tau_pos : 0 < tau
  pool_separated : poolLogMean D beta .minus < poolLogMean D beta .plus
  left_interior :
    tau * (poolLogMean D beta .plus - poolLogMean D beta .minus) ≤
      mu - poolLogMean D beta .minus
  right_interior :
    tau * (poolLogMean D beta .plus - poolLogMean D beta .minus) ≤
      poolLogMean D beta .plus - mu

namespace BarycentricTarget

variable {D : StructuredSampleData Head} (T : BarycentricTarget D)

omit [Nonempty Head] in
theorem denominator_pos :
    0 < poolLogMean D T.beta .plus - poolLogMean D T.beta .minus :=
  sub_pos.mpr T.pool_separated

omit [Nonempty Head] in
theorem mixingWeight_pos :
    0 < physicalMixingWeight D T.beta T.mu := by
  unfold physicalMixingWeight
  exact div_pos
    ((mul_pos T.tau_pos T.denominator_pos).trans_le T.left_interior)
    T.denominator_pos

omit [Nonempty Head] in
theorem mixingWeight_lt_one :
    physicalMixingWeight D T.beta T.mu < 1 := by
  unfold physicalMixingWeight
  apply (div_lt_one T.denominator_pos).2
  have hright : 0 < poolLogMean D T.beta .plus - T.mu :=
    (mul_pos T.tau_pos T.denominator_pos).trans_le T.right_interior
  linarith

omit [Nonempty Head] in
theorem tau_le_mixingWeight :
    T.tau ≤ physicalMixingWeight D T.beta T.mu := by
  unfold physicalMixingWeight
  exact (le_div_iff₀ T.denominator_pos).2 T.left_interior

omit [Nonempty Head] in
theorem tau_le_one_sub_mixingWeight :
    T.tau ≤ 1 - physicalMixingWeight D T.beta T.mu := by
  calc
    T.tau ≤
        (poolLogMean D T.beta .plus - T.mu) /
          (poolLogMean D T.beta .plus - poolLogMean D T.beta .minus) :=
      (le_div_iff₀ T.denominator_pos).2 T.right_interior
    _ = 1 - physicalMixingWeight D T.beta T.mu := by
      unfold physicalMixingWeight
      field_simp [T.denominator_pos.ne']
      ring

/-- Exact normalized cell mass selected by the head barycenter and physical
mixing coordinate. -/
def cellProbability (c : Cell Head) : ℝ :=
  match c.2 with
  | .minus => T.beta c.1 * (1 - physicalMixingWeight D T.beta T.mu)
  | .plus => T.beta c.1 * physicalMixingWeight D T.beta T.mu

omit [Nonempty Head] in
theorem cellProbability_pos (c : Cell Head) : 0 < T.cellProbability c := by
  cases c with
  | mk h sigma =>
      cases sigma with
      | minus =>
          exact mul_pos (T.beta_pos h) (sub_pos.mpr T.mixingWeight_lt_one)
      | plus =>
          exact mul_pos (T.beta_pos h) T.mixingWeight_pos

omit [Nonempty Head] in
theorem sum_cellProbability : ∑ c : Cell Head, T.cellProbability c = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_physicalSign]
  simp only [cellProbability]
  calc
    ∑ h : Head,
        (T.beta h * (1 - physicalMixingWeight D T.beta T.mu) +
          T.beta h * physicalMixingWeight D T.beta T.mu) =
        ∑ h : Head, T.beta h := by
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = 1 := T.beta_sum

/-- The canonical `BaselineAllocation`; its cell masses already sum to one. -/
def baseline : BaselineAllocation D where
  cellMass := T.cellProbability
  cellMass_pos := T.cellProbability_pos

omit [Nonempty Head] in
theorem baseline_totalMass : T.baseline.totalMass = 1 := by
  exact T.sum_cellProbability

omit [Nonempty Head] in
theorem baseline_normalizedCellMass (c : Cell Head) :
    T.baseline.normalizedCellMass c = T.cellProbability c := by
  unfold BaselineAllocation.normalizedCellMass
  change T.cellProbability c / T.baseline.totalMass = T.cellProbability c
  rw [T.baseline_totalMass, div_one]

/-- A positive common cell-mass margin, independent of the prime mesh. -/
def cellMassMargin : ℝ := T.betaFloor * T.tau

omit [Nonempty Head] in
theorem cellMassMargin_pos : 0 < T.cellMassMargin :=
  mul_pos T.betaFloor_pos T.tau_pos

omit [Nonempty Head] in
theorem cellMassMargin_le (c : Cell Head) :
    T.cellMassMargin ≤ T.baseline.normalizedCellMass c := by
  rw [T.baseline_normalizedCellMass]
  cases c with
  | mk h sigma =>
      cases sigma with
      | minus =>
          exact mul_le_mul (T.betaFloor_le h)
            T.tau_le_one_sub_mixingWeight T.tau_pos.le
            (T.beta_pos h).le
      | plus =>
          exact mul_le_mul (T.betaFloor_le h)
            T.tau_le_mixingWeight T.tau_pos.le
            (T.beta_pos h).le







end BarycentricTarget

end

end Erdos390.Full.PaperGuardCensus

end

/- Source module: Erdos390.Full.PaperEffectiveNorm -/
section


/-!
# The concrete effective parameter norm of Proposition 8.7

The paper controls a parameter by three quantities: the largest effective
prime fugacity, the Euclidean nuisance block, and the scaled slow parameter
`w * lambda`.  The slow coordinate of `BridgeData.ParamSpace` is already
`w * lambda`.  We therefore map the actual parameter space injectively into
the product of these three normed spaces and use the norm inherited by the
range.  This gives a genuine complete finite-dimensional normed space and a
continuous linear equivalence back to the original parameter space, exactly
the input required by `EquivalentNormODE`.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit
namespace BridgeData

open ArithmeticBandGeometry

noncomputable section

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The full band coefficient reconstructed from the quotient gauge. -/
def bandParameter (xi : B.ParamSpace) (j : Band) : ℝ :=
  if h : j = B.lowBand then
    -∑ k : B.GaugeIndex,
      B.lowRatio k * xi (MomentCoord.gauge k)
  else
    xi (MomentCoord.gauge ⟨j, h⟩)

@[simp]
theorem bandParameter_gauge (xi : B.ParamSpace) (j : B.GaugeIndex) :
    B.bandParameter xi j.1 = xi (MomentCoord.gauge j) := by
  simp [bandParameter, j.2]

@[simp]
theorem bandParameter_low (xi : B.ParamSpace) :
    B.bandParameter xi B.lowBand =
      -∑ k : B.GaugeIndex,
        B.lowRatio k * xi (MomentCoord.gauge k) := by
  simp [bandParameter]

theorem bandParameter_add (x y : B.ParamSpace) (j : Band) :
    B.bandParameter (x + y) j =
      B.bandParameter x j + B.bandParameter y j := by
  by_cases h : j = B.lowBand
  · simp only [bandParameter, h, ↓reduceDIte, PiLp.add_apply]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    ring
  · simp [bandParameter, h]

theorem bandParameter_smul (a : ℝ) (x : B.ParamSpace) (j : Band) :
    B.bandParameter (a • x) j = a * B.bandParameter x j := by
  by_cases h : j = B.lowBand
  · simp only [bandParameter, h, ↓reduceDIte, PiLp.smul_apply, smul_eq_mul]
    rw [mul_neg]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simp [bandParameter, h, smul_eq_mul]

/-- The literal coefficient of `v_p` in the exponent represented by `xi`.
The division by `w` converts the stored slow coordinate back to `lambda`. -/
def effectivePrimeCoefficient (xi : B.ParamSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) : ℝ :=
  B.bandParameter xi (B.partition.band p) +
    (xi MomentCoord.slow / B.w) * B.primeDeviation p

theorem effectivePrimeCoefficient_add (x y : B.ParamSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (x + y) p =
      B.effectivePrimeCoefficient x p +
        B.effectivePrimeCoefficient y p := by
  simp only [effectivePrimeCoefficient, B.bandParameter_add, PiLp.add_apply,
    add_div]
  ring

theorem effectivePrimeCoefficient_smul (a : ℝ) (x : B.ParamSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (a • x) p =
      a * B.effectivePrimeCoefficient x p := by
  simp only [effectivePrimeCoefficient, B.bandParameter_smul,
    PiLp.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt B.w_pos]

/-- The physical/head block extracted from an actual parameter. -/
def nuisanceParameter (xi : B.ParamSpace) : B.NuisanceSpace :=
  (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm
    (fun c => match c with
      | .physical => xi MomentCoord.physical
      | .head h => xi (MomentCoord.head h))

@[simp]
theorem nuisanceParameter_physical (xi : B.ParamSpace) :
    B.nuisanceParameter xi NuisanceCoord.physical =
      xi MomentCoord.physical := rfl

@[simp]
theorem nuisanceParameter_head (xi : B.ParamSpace) (h : B.HeadIndex) :
    B.nuisanceParameter xi (NuisanceCoord.head h) =
      xi (MomentCoord.head h) := rfl

/-- Product space carrying the max versions of the three effective
coordinates.  Its norm is uniformly equivalent (within a factor three) to
the sum convention used in the paper. -/
abbrev EffectiveAmbient :=
  (((BandPrime B.sampleData.n B.sampleData.W → ℝ) × B.NuisanceSpace) × ℝ)

def effectiveCoordinateLinearMap : B.ParamSpace →ₗ[ℝ] B.EffectiveAmbient where
  toFun xi :=
    (((fun p => B.effectivePrimeCoefficient xi p), B.nuisanceParameter xi),
      xi MomentCoord.slow)
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext
      · funext p
        exact B.effectivePrimeCoefficient_add x y p
      · apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
        funext c
        cases c <;> rfl
    · rfl
  map_smul' a x := by
    apply Prod.ext
    · apply Prod.ext
      · funext p
        exact B.effectivePrimeCoefficient_smul a x p
      · apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
        funext c
        cases c <;> rfl
    · rfl

@[simp]
theorem effectiveCoordinateLinearMap_apply (xi : B.ParamSpace) :
    B.effectiveCoordinateLinearMap xi =
      (((fun p => B.effectivePrimeCoefficient xi p), B.nuisanceParameter xi),
        xi MomentCoord.slow) := rfl

theorem effectiveCoordinateLinearMap_injective :
    Function.Injective B.effectiveCoordinateLinearMap := by
  intro x y hxy
  apply (EuclideanSpace.equiv B.Coord ℝ).injective
  funext c
  have hslow : x MomentCoord.slow = y MomentCoord.slow :=
    congrArg (fun z : B.EffectiveAmbient => z.2) hxy
  cases c with
  | slow => exact hslow
  | physical =>
      have h := congrArg
        (fun z : B.EffectiveAmbient => z.1.2 NuisanceCoord.physical) hxy
      exact h
  | head h =>
      have hz := congrArg
        (fun z : B.EffectiveAmbient => z.1.2 (NuisanceCoord.head h)) hxy
      exact hz
  | gauge j =>
      obtain ⟨p, hp⟩ := B.partition.fiber_nonempty j.1
      have hpBand : B.partition.band p = j.1 := hp
      have hpEq := congrArg
        (fun z : B.EffectiveAmbient => z.1.1 p) hxy
      simp only [effectiveCoordinateLinearMap_apply,
        effectivePrimeCoefficient, hpBand, B.bandParameter_gauge] at hpEq
      rw [hslow] at hpEq
      exact add_right_cancel hpEq

/-- Continuous version of the concrete effective-coordinate injection. -/
def effectiveCoordinateCLM : B.ParamSpace →L[ℝ] B.EffectiveAmbient :=
  B.effectiveCoordinateLinearMap.toContinuousLinearMap

theorem effectiveCoordinateCLM_injective :
    Function.Injective B.effectiveCoordinateCLM :=
  B.effectiveCoordinateLinearMap_injective

/-- The effective parameter space is the closed range of the concrete
coordinate map. -/
abbrev EffectiveParamSpace :=
  LinearMap.range B.effectiveCoordinateCLM.toLinearMap

theorem effectiveCoordinateCLM_range_closed :
    IsClosed (Set.range B.effectiveCoordinateCLM) := by
  have hker : LinearMap.ker B.effectiveCoordinateCLM.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr B.effectiveCoordinateCLM_injective
  exact (LinearMap.isClosedEmbedding_of_injective hker).isClosed_range

/-- Continuous linear equivalence from the effective normed space back to
the original Euclidean parameter space. -/
def effectiveParamEquiv : B.EffectiveParamSpace ≃L[ℝ] B.ParamSpace :=
  (B.effectiveCoordinateCLM.equivRange
    B.effectiveCoordinateCLM_injective
    B.effectiveCoordinateCLM_range_closed).symm

/-- The sum convention used in the paper: largest prime fugacity, nuisance
norm, and the stored slow coordinate `w * lambda`. -/
def paperEffectiveSize (xi : B.ParamSpace) : ℝ :=
  ‖fun p => B.effectivePrimeCoefficient xi p‖ +
    ‖B.nuisanceParameter xi‖ + |xi MomentCoord.slow|



/-- The inherited range norm is exactly the maximum of the three paper
coordinates. -/
theorem norm_effectiveCoordinateCLM_eq (xi : B.ParamSpace) :
    ‖B.effectiveCoordinateCLM xi‖ =
      max (max ‖fun p => B.effectivePrimeCoefficient xi p‖
        ‖B.nuisanceParameter xi‖) |xi MomentCoord.slow| := by
  rfl



/-- Conversely the paper's sum convention is at most three times the max
norm.  The constant is absolute and independent of the number of bands. -/
theorem paperEffectiveSize_le_three_mul_norm_effectiveCoordinateCLM
    (xi : B.ParamSpace) :
    B.paperEffectiveSize xi ≤ 3 * ‖B.effectiveCoordinateCLM xi‖ := by
  let a := ‖fun p => B.effectivePrimeCoefficient xi p‖
  let b := ‖B.nuisanceParameter xi‖
  let c := |xi MomentCoord.slow|
  let m := max (max a b) c
  have ha : a ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb : b ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have hc : c ≤ m := le_max_right _ _
  have hm : ‖B.effectiveCoordinateCLM xi‖ = m := by
    simpa only [a, b, c, m] using B.norm_effectiveCoordinateCLM_eq xi
  unfold paperEffectiveSize
  dsimp only [a, b, c] at ha hb hc
  rw [hm]
  linarith

@[simp]
theorem effectiveCoordinateCLM_effectiveParamEquiv
    (z : B.EffectiveParamSpace) :
    B.effectiveCoordinateCLM (B.effectiveParamEquiv z) = z.1 := by
  have h := B.effectiveParamEquiv.symm_apply_apply z
  exact congrArg Subtype.val h

@[simp]
theorem norm_effectiveParamEquiv_symm (xi : B.ParamSpace) :
    ‖B.effectiveParamEquiv.symm xi‖ =
      ‖B.effectiveCoordinateCLM xi‖ := by
  rfl

/-- A radius in the inherited effective max norm implies the literal paper
box with radius three times as large.  This is the dimension-free conversion
used in the non-circular ODE argument. -/
theorem paperEffectiveSize_effectiveParamEquiv_le
    (z : B.EffectiveParamSpace) :
    B.paperEffectiveSize (B.effectiveParamEquiv z) ≤ 3 * ‖z‖ := by
  calc
    B.paperEffectiveSize (B.effectiveParamEquiv z)
        ≤ 3 * ‖B.effectiveCoordinateCLM (B.effectiveParamEquiv z)‖ :=
      B.paperEffectiveSize_le_three_mul_norm_effectiveCoordinateCLM _
    _ = 3 * ‖z‖ := by
      rw [B.effectiveCoordinateCLM_effectiveParamEquiv]
      rfl

/-! ## Non-circular ODE transport in the literal paper norm -/





end

end BridgeData
end Erdos390.Full.PaperBridgeFit

end


