-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:38:06.398323+00:00
-- url     : https://prove2.me/submissions/643b35d5-4db6-427a-9a08-be27aef7cdab

import Definitions.Def_erdos390_remaining_analytic_propositions_004
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_005
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_010
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshEventualCoherentBridgeSourceObligation_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider_compact
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshUniformP87_compact
import Theorems.Thm_Erdos390_WholePaper_eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact






section
theorem Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower : Erdos390.RemainingAnalyticGoal008_004 := @Erdos390.WholePaper.eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshUniformP87 : Erdos390.RemainingAnalyticGoal005_004 := @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshUniformP87_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider : Erdos390.RemainingAnalyticGoal005_003 := @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshEventualCoherentBridgeSourceObligation : Erdos390.RemainingAnalyticGoal005_002 := @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshEventualCoherentBridgeSourceObligation_compact
end
section
theorem Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput : Erdos390.RemainingAnalyticGoal004_012 := @Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput_compact
end
/- Source module: Erdos390.Full.RegularRelativeMesh -/
section


/-!
# Existence of a finite regular relative mesh

Section 8.4 partitions the positive logarithmic interval `[delta,1]` into
geometric cells.  This file constructs such a mesh rather than leaving its
existence as a certificate.  Given `0 < delta < 1` and a requested upper
relative width `eta > 0`, the number of cells is the ceiling of the relevant
logarithmic ratio and the common relative width is adjusted so that the last
endpoint is exactly `1`.
-/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMesh

noncomputable section



namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)













theorem endpoint_succ (k : ℕ) :
    M.endpoint (k + 1) = M.endpoint k * (1 + M.ratio) := by
  unfold endpoint
  rw [pow_succ]
  ring



theorem endpoint_pos (hdelta : 0 < delta) (k : ℕ) :
    0 < M.endpoint k := by
  unfold endpoint
  exact mul_pos hdelta (pow_pos (by linarith [M.ratio_pos]) k)

theorem lower_pos (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.lower k := M.endpoint_pos hdelta k.1

theorem width_eq_ratio_mul_lower (k : Fin M.cellCount) :
    M.width k = M.ratio * M.lower k := by
  unfold width upper lower
  rw [M.endpoint_succ]
  ring

theorem width_pos (hdelta : 0 < delta) (k : Fin M.cellCount) :
    0 < M.width k := by
  rw [M.width_eq_ratio_mul_lower]
  exact mul_pos M.ratio_pos (M.lower_pos hdelta k)

theorem lower_lt_upper (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.lower k < M.upper k := by
  rw [← sub_pos, ← width]
  exact M.width_pos hdelta k



theorem upper_le_one (hdelta : 0 < delta) (k : Fin M.cellCount) :
    M.upper k ≤ 1 := by
  have hpow : (1 + M.ratio) ^ (k.1 + 1) ≤
      (1 + M.ratio) ^ M.cellCount :=
    pow_le_pow_right₀ (by linarith [M.ratio_pos]) (Nat.succ_le_iff.mpr k.2)
  unfold upper endpoint
  calc
    delta * (1 + M.ratio) ^ (k.1 + 1) ≤
        delta * (1 + M.ratio) ^ M.cellCount :=
      mul_le_mul_of_nonneg_left hpow hdelta.le
    _ = 1 := M.lastEndpoint





end Mesh



end

end Erdos390.Full.RegularRelativeMesh

end

/- Source module: Erdos390.Full.SelectedDyadicRegularMesh -/
section


/-!
# An explicit arbitrarily fine regular mesh with a fixed anchor block

For integers `K ≥ 3`, `N ≥ 1`, adjacent endpoints have ratio
`exp(log 2 / N)`.  The mesh runs from `2^{-K}` to `1`, and the consecutive
block of cells between `1/4` and `1/2` has total width exactly `1/4`.
Increasing `K` shrinks the moving-low cutoff; increasing `N` refines every
positive cell, without shrinking that total interior anchor mass.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.SelectedDyadicRegularMesh

open RegularRelativeMesh































theorem delta_tendsto_zero : Tendsto delta atTop (nhds 0) := by
  unfold delta
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)

theorem ratio_tendsto_zero : Tendsto ratio atTop (nhds 0) := by
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ ↦ ((N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hquot : Tendsto (fun N : ℕ ↦ Real.log 2 / (N : ℝ)) atTop
      (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hquot
  have hone : Tendsto (fun _N : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa only [ratio, Real.exp_zero, sub_self] using hexp.sub hone

/-- Both the low cell and every positive relative cell can be made finer
than an arbitrary prescribed tolerance, while the anchor block stays fixed. -/
theorem exists_fine_mesh (tol : ℝ) (htol : 0 < tol) :
    ∃ K N : ℕ, ∃ hK : 3 ≤ K, ∃ hN : 0 < N,
      delta K < tol ∧ ratio N < tol ∧
      ∀ k : Fin ((mesh K N (by omega) hN).cellCount),
        (mesh K N (by omega) hN).width k < tol := by
  obtain ⟨K0, hK0⟩ := eventually_atTop.1
    (delta_tendsto_zero.eventually (eventually_lt_nhds htol))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    (ratio_tendsto_zero.eventually (eventually_lt_nhds htol))
  let K := max 3 K0
  let N := max 1 N0
  have hK : 3 ≤ K := le_max_left _ _
  have hN : 0 < N := by exact (by omega : 0 < max 1 N0)
  have hdelta : delta K < tol := hK0 K (le_max_right _ _)
  have hratio : ratio N < tol := hN0 N (le_max_right _ _)
  refine ⟨K, N, hK, hN, hdelta, hratio, ?_⟩
  intro k
  rw [(mesh K N (by omega) hN).width_eq_ratio_mul_lower]
  have hlower : (mesh K N (by omega) hN).lower k ≤ 1 :=
    (mesh K N (by omega) hN).lower_lt_upper (by
      unfold delta
      positivity) k |>.le.trans
      ((mesh K N (by omega) hN).upper_le_one (by
        unfold delta
        positivity) k)
  have hrnonneg : 0 ≤ ratio N := (ratio_pos hN).le
  calc
    ratio N * (mesh K N (by omega) hN).lower k ≤ ratio N * 1 :=
      mul_le_mul_of_nonneg_left hlower hrnonneg
    _ < tol := by simpa only [mul_one] using hratio

end Erdos390.Full.SelectedDyadicRegularMesh

end

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)











theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.WholePaper.UpperScale -/
section


/-!
# Elementary scale facts for the upper bound

This module isolates the exact ceiling and endpoint used on the upper-bound
side of the paper.  Every asymptotic statement is proved directly from
elementary real-logarithm limits.  No prime-counting input is used.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section





/-- The elementary logarithmic comparison `log n / n → 0`, made public
for later upper-bound estimates. -/
theorem log_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

/-- The second-order scale `n / log n` diverges to infinity. -/
theorem secondOrderScale_tendsto_atTop :
    Tendsto secondOrderScale atTop atTop := by
  have hpos :
      ∀ᶠ n : ℕ in atTop,
        0 < Real.log (n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (by positivity)
  have hright :
      Tendsto
        (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨log_natCast_div_natCast_tendsto_zero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦ by
    change (Real.log (n : ℝ) / (n : ℝ))⁻¹ =
      secondOrderScale n
    rw [secondOrderScale, inv_div]

/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

/-- Eventually the second-order scale is strictly positive. -/
theorem eventually_secondOrderScale_pos :
    ∀ᶠ n : ℕ in atTop, 0 < secondOrderScale n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact secondOrderScale_pos hn































end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughHeadCompatibleFinitePoint -/
section


/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/





















/-! ## The finite head and raw weights -/









/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero



/-- The complete zero-head stratum has strictly positive density. -/
theorem roughHeadDensity_pos (W : ℕ) :
    0 < roughHeadDensity W := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot : (0 : ℝ) < ((roughHeadModulus W).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (roughHeadModulus_pos W)
  exact div_pos htot hmod



































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightLedger -/
section


/-!
# The exact smooth-row quota and height ledger from Section 8

This file records the algebraic part of the paper's smooth-row initialization
without replacing any actual finite mass by an asymptotic main term.

The literal active base component is the constant weight `betaAct / L n` on
the head-free, `yNat n`-smooth part of the broad interval.  Its exact support
is the complete-rough row with label one.  The later definitions follow the
paper verbatim:

* `Q_sm(0)` is the nearest integer to `m_sm,fr + qTilde`, with a half-integer
  tie sent to the smaller integer;
* `q0 = Q_sm(0) - m_sm,fr`;
* `Q_sm(d) = Q_sm(0) - d` and `qAct(d) = q0 - d`;
* `A0 = logY - Lambda0 - q0 * L` and `A(d) = A0 + d * L`;
* `d` is the tie-lower nearest integer to
  `(mu * q0 - A0) / (L + mu)`.

All displayed identities and the two nearest-integer errors are unconditional.
The analytic comparison between the raw base mass and the actual post-guard
mass is deliberately left to the companion asymptotic module.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal rough smooth base component -/

















/-! ## Tie-lower nearest integers -/









/-- The universal half-unit rounding error. -/
theorem bankPaperNearestIntegerTieLower_abs_sub_le (x : Real) :
    |(bankPaperNearestIntegerTieLower x : Real) - x| ≤ 1 / 2 := by
  have hcell :=
    (bankPaperNearestIntegerTieLower_eq_iff x
      (bankPaperNearestIntegerTieLower x)).1 rfl
  apply abs_le.mpr
  constructor <;> linarith

/-! ## Exact smooth-row quota initialization -/







/-- Exact expression for the initialization error. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_sub_actual
    (mFrozen qTilde : Real) :
    bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde =
      (bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
        (mFrozen + qTilde) := by
  unfold bankPaperCanonicalSmoothInitialActiveMass
  ring

/-- The paper's literal bound `|q0 - qTilde| <= 1/2`. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen qTilde : Real) :
    |bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde| ≤
      1 / 2 := by
  rw [bankPaperCanonicalSmoothInitialActiveMass_sub_actual]
  exact bankPaperNearestIntegerTieLower_abs_sub_le (mFrozen + qTilde)

















/-! ## Exact frozen-height ledger and centered adjustment -/











/-- The rounded height adjustment is within one half of `dStar`. -/
theorem bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
    (n : Nat) (mu q0 A0 : Real) :
    |(bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real) -
        bankPaperCanonicalSmoothHeightCenter n mu q0 A0| ≤ 1 / 2 :=
  bankPaperNearestIntegerTieLower_abs_sub_le
    (bankPaperCanonicalSmoothHeightCenter n mu q0 A0)















/-! ## Literal Section 8 families -/



















/-- Family-level half-unit initialization error. -/
theorem bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
    (mFrozen qTilde : Nat -> Real) (n : Nat) :
    |bankPaperCanonicalSmoothQ0Family mFrozen qTilde n - qTilde n| <=
      1 / 2 :=
  bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen n) (qTilde n)





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic -/
section


/-!
# Eventual raw broad-pool surplus on every active rough row

The tangent clean-list estimate is global in the common multiplier and
therefore cannot by itself give a lower bound in each complete rough row.
The rowwise input needed by the guard-capacity reduction is instead the
`active-clean-pool` estimate from Section 6 of the paper.  This file derives
that estimate from the already proved uniform de Bruijn bound and the
already proved fixed-head endpoint shift.

The proof has three quantitative layers.

* On a fixed-ratio interval `(A,B]`, the Dickman endpoint main term grows by
  a fixed positive multiple of `B-A`.  The uniform friable error is absorbed
  once `log y` is large.
* Exact head Möbius inversion and the fixed-divisor endpoint shift retain a
  fixed multiple of `A` in the head-free smooth interval.
* For an active label, `A = n / label` tends to infinity uniformly, while
  both `label / n` and `upperTailLength c n / n` tend to zero.  Consequently
  the broad pool dominates the literal upper-row quota and the three local
  guards.

The final theorem constructs
`RoughCanonicalActiveRawBroadSurplus ... 3 poolMinimum` for every fixed
`poolMinimum`, without a selector premise or an additional analytic
assumption.  The stronger linear real lower bound used to absorb that
constant is retained separately below.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells
open BankPaperRealization

noncomputable section

/-! ## A positive Dickman floor -/



/-- The fixed Dickman floor is strictly positive. -/
theorem roughCanonicalPoolDickmanFloor_pos :
    0 < roughCanonicalPoolDickmanFloor := by
  unfold roughCanonicalPoolDickmanFloor
  exact rho_pos_on_zero_five (by norm_num) le_rfl



/-! ## Growth of the unrestricted smooth interval -/





/-! ## Closing the fixed head -/









/-! ## Literal rough-row adapters -/



/-- The retained raw broad-pool density is strictly positive. -/
theorem roughCanonicalRawBroadPoolDensity_pos (W : Nat) :
    0 < roughCanonicalRawBroadPoolDensity W := by
  unfold roughCanonicalRawBroadPoolDensity
  exact div_pos
    (mul_pos (roughHeadDensity_pos W)
      roughCanonicalPoolDickmanFloor_pos) (by norm_num)









/-! ## Uniform paper-scale choices -/























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalHeadActiveMassEventually -/
section


/-!
# Eventual lower bound for the paper's head-reserve active mass

The paper obtains its final active mass from the exact ledger

`q^{act}(d) = q₀ - d`,

where the rough smooth active mass satisfies `q₀ ≍ n / log n` and the
height-centering change satisfies `d = O(n / log² n)`.  Only the lower
half of that comparison is needed to prove the constructor hypothesis
`1 <= q^{act}(d)` for all sufficiently large `n`.

The repository's `HeadSimplexReserve` currently stores only
`0 < activeMass`.  It has no family constructor, no connection to the
rough smooth active mass, and no asymptotic lower-bound field.  This file
therefore isolates the exact missing paper input as a positive lower
multiple of `secondOrderScale n = n / log n`.  Everything after that input
is proved here:

* the active mass tends to infinity and eventually exceeds every constant;
* in particular it is eventually at least one;
* an `o(n / log n)` height change preserves a fixed positive lower multiple;
* the paper's stronger `O(n / log² n)` change is automatically little-o;
* the canonical scaled seed has eventual mass at least one and its
  self-selector satisfies the full actual-active-measure constructor.

A concrete reserve of mass `1 / 2` is also constructed.  It proves that
strict positivity alone cannot imply the desired inequality, so the
repository needs an additional growth input until the missing
rough-active-mass construction is connected to `HeadSimplexReserve`.
The predicate below is exactly the lower half of the growth statement
used in the paper.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

/-! ## The irreducible paper-scale input -/





/-! ## Positivity is genuinely insufficient -/









/-! ## All eventual consequences of the minimal input -/

/-- A fixed positive multiple of `n / log n` tends to infinity, hence so
does any active mass lying eventually above it. -/
theorem bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    Tendsto q atTop atTop := by
  rcases H with ⟨c, hc, hq⟩
  have hscale : Tendsto
      (fun n : Nat => c * secondOrderScale n) atTop atTop :=
    secondOrderScale_tendsto_atTop.const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ hscale
  exact hq

/-- Every fixed real threshold is eventually below the active mass. -/
theorem eventually_const_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) (C : Real) :
    ∀ᶠ n : Nat in atTop, C <= q n :=
  (bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower q H).eventually
    (eventually_ge_atTop C)

/-- The exact constructor threshold follows with `C = 1`. -/
theorem eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    ∀ᶠ n : Nat in atTop, 1 <= q n :=
  eventually_const_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    q H 1





/-! ## The exact `q₀-d` height-centering algebra -/

/-- The paper's error scale `n / log² n` is little-o of
`secondOrderScale n = n / log n`. -/
theorem secondOrderScale_div_L_isLittleO_secondOrderScale :
    (fun n : Nat => secondOrderScale n / L n) =o[atTop]
      secondOrderScale := by
  have hzero : ∀ᶠ n : Nat in atTop,
      secondOrderScale n = 0 -> secondOrderScale n / L n = 0 :=
    Eventually.of_forall fun n hn => by simp [hn]
  apply (isLittleO_iff_tendsto' hzero).mpr
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : Nat => (L n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hLTop
  apply hinv.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hL : 0 < L n := L_pos hn
  field_simp [hscale.ne', hL.ne']

/-- Subtracting a little-o height-centering change from a macroscopically
positive base mass preserves half of its lower constant. -/
theorem bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
    (q0 d : Nat -> Real)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =o[atTop] secondOrderScale) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => q0 n - d n) := by
  rcases Hq0 with ⟨c, hc, hq0⟩
  refine ⟨c / 2, half_pos hc, ?_⟩
  have hdBound := hd.bound (half_pos hc)
  filter_upwards [hq0, hdBound, eventually_secondOrderScale_pos]
      with n hq0n hdn hscale
  have hdn' : |d n| <= (c / 2) * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscale] using hdn
  have hdle : d n <= (c / 2) * secondOrderScale n :=
    (le_abs_self (d n)).trans hdn'
  calc
    (c / 2) * secondOrderScale n =
        c * secondOrderScale n -
          (c / 2) * secondOrderScale n := by ring
    _ <= q0 n - (c / 2) * secondOrderScale n :=
      sub_le_sub_right hq0n _
    _ <= q0 n - d n := sub_le_sub_left hdle _

/-- This is the paper's displayed implication: a base mass bounded below
on the `n / log n` scale and a change of order `n / log² n` yield a final
active mass with the required positive paper-scale lower bound. -/
theorem bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
    (q0 d : Nat -> Real)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =O[atTop]
      (fun n : Nat => secondOrderScale n / L n)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => q0 n - d n) := by
  apply bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
    q0 d Hq0
  exact hd.trans_isLittleO
    secondOrderScale_div_L_isLittleO_secondOrderScale





/-! ## Literal scaled seeds and actual-measure constructors -/







/-! ## The literal paper-head specialization -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic -/
section


/-!
# The analytic Section 8 smooth-row quota and height bridge

The raw active smooth component from the exact companion file has a positive
`n / log n` lower bound by the repository's uniform de Bruijn--Saias and
fixed-head estimates.  This file proves that bound directly for complete-
rough label one, then propagates it through the exact nearest-integer and
height-center constructions.

Only one repository-level analytic ledger remains absent.  It is named
`BankPaperCanonicalSectionEightAnalyticLedger` below and contains exactly:

* the actual post-guard smooth mass differs from the explicit raw base mass
  by `o(n / log n)`;
* the literal frozen height defect `A0` is `O(n / log n)`.

These are precisely the two estimates asserted together in the paper's
Section 8 frozen ledger.  No selector, active-measure, or positivity premise
is hidden in that predicate.  Every consequence after it, including
`d = O(n / log^2 n)` and the positive lower bound for `q0 - d`, is proved
here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The label-one raw base pool is macroscopically large -/







/-- Therefore the literal `betaAct / L` base component has the minimal
positive paper-scale lower bound whenever `betaAct > 0`. -/
theorem bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
    (W K : Nat) {c betaAct : Real} (hc : 0 < c) (hbeta : 0 < betaAct) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct) := by
  use betaAct * roughCanonicalRawBroadPoolDensity W,
    mul_pos hbeta (roughCanonicalRawBroadPoolDensity_pos W)
  have hpool :=
    eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower W K hc
  filter_upwards [hpool, eventually_gt_atTop 1] with n hpoolN hn
  have hL : 0 < L n := L_pos hn
  calc
    (betaAct * roughCanonicalRawBroadPoolDensity W) * secondOrderScale n =
        (betaAct / L n) *
          (roughCanonicalRawBroadPoolDensity W * (n : Real)) := by
      unfold secondOrderScale L
      ring
    _ <= (betaAct / L n) *
          ((bankPaperCanonicalRawSmoothBasePool W n
            (upperTailLength c n) K).card : Real) :=
      mul_le_mul_of_nonneg_left hpoolN (div_nonneg hbeta.le hL.le)
    _ = bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) K betaAct := by
      rfl

/-- The raw base mass is also `O(n / log n)`, by the elementary containment
of its support in the broad interval. -/
theorem bankPaperCanonicalRawSmoothBaseMass_isBigO
    (W K : Nat) (c betaAct : Real) :
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct) =O[atTop] secondOrderScale := by
  apply (isBigO_iff).2
  use |betaAct|
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hscale : 0 < secondOrderScale n := secondOrderScale_pos (by omega)
  have hsubset : bankPaperCanonicalRawSmoothBasePool W n
      (upperTailLength c n) K ⊆
        roughBroadLowerBlock n (upperTailLength c n) K := by
    intro a ha
    change a ∈ roughCanonicalBroadCorrectionPool W n
      (upperTailLength c n) K (yNat n) 1 at ha
    have haRow := mem_completeRoughRowFiber.mp ha
    exact (mem_roughHeadFree.mp haRow.1).1
  have hcardNat :
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card <= n := by
    calc
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card <=
          (roughBroadLowerBlock n (upperTailLength c n) K).card :=
        Finset.card_le_card hsubset
      _ <= n := by
        simp only [roughBroadLowerBlock, Nat.card_Ioc]
        omega
  have hcard :
      ((bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card : Real) <= (n : Real) := by
    exact_mod_cast hcardNat
  have hcardNonneg :
      (0 : Real) <=
        ((bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) :=
    Nat.cast_nonneg _
  rw [bankPaperCanonicalRawSmoothBaseMass, Real.norm_eq_abs,
    abs_mul, abs_div, abs_of_pos hL, abs_of_nonneg hcardNonneg,
    Real.norm_eq_abs, abs_of_pos hscale]
  rw [secondOrderScale]
  have hcoef : 0 <= |betaAct| / L n :=
    div_nonneg (abs_nonneg _) hL.le
  calc
    |betaAct| / L n *
        ((bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) <=
        |betaAct| / L n * (n : Real) :=
      mul_le_mul_of_nonneg_left hcard hcoef
    _ = |betaAct| * ((n : Real) / L n) := by ring

/-! ## The exact missing analytic ledger -/



/-! ## Nearest-integer initialization preserves the paper scale -/

/-- The uniformly bounded initialization error is little-o of
`secondOrderScale`. -/
theorem bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
    (mFrozen qTilde : Nat -> Real) :
    (fun n => bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
      qTilde n) =o[atTop] secondOrderScale := by
  have hbounded :
      (fun n => bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
        qTilde n) =O[atTop] (fun _n : Nat => (1 : Real)) := by
    apply (isBigO_iff).2
    use 1 / 2
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
        mFrozen qTilde n
  have hnorm : Tendsto (norm ∘ secondOrderScale) atTop atTop := by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using
      tendsto_abs_atTop_atTop.comp secondOrderScale_tendsto_atTop
  have hone : (fun _n : Nat => (1 : Real)) =o[atTop]
      secondOrderScale :=
    isLittleO_const_left.mpr (Or.inr hnorm)
  exact hbounded.trans_isLittleO hone

/-- A negligible raw-to-post-guard loss transfers the positive lower bound
from the explicit raw base mass to the actual mass `qTilde`. -/
theorem bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (rawBase qTilde : Nat -> Real)
    (Hraw : BankPaperCanonicalActiveMassPaperScaleLower rawBase)
    (Hguard : (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale) :
    BankPaperCanonicalActiveMassPaperScaleLower qTilde := by
  rcases bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
      rawBase (fun n => rawBase n - qTilde n) Hraw Hguard with
    ⟨C, hC, hlower⟩
  use C, hC
  filter_upwards [hlower] with n hn
  convert hn using 1 ; ring

/-- The half-unit nearest-integer initialization transfers that lower bound
from `qTilde` to the literal `q0` family. -/
theorem bankPaperCanonicalSmoothQ0Family_paperScaleLower
    (mFrozen qTilde : Nat -> Real)
    (HqTilde : BankPaperCanonicalActiveMassPaperScaleLower qTilde) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde) := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  have hd : (fun n => qTilde n -
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde n) =o[atTop]
        secondOrderScale :=
    hround.neg_left.congr_left (fun n => by ring)
  rcases bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
      qTilde
      (fun n => qTilde n -
        bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
      HqTilde hd with ⟨C, hC, hlower⟩
  use C, hC
  filter_upwards [hlower] with n hn
  convert hn using 1 ; ring

/-- A little-o raw-to-post-guard error also transfers the upper `O(N)`
bound. -/
theorem bankPaperCanonicalPostGuardSmoothMass_isBigO
    (rawBase qTilde : Nat -> Real)
    (Hraw : rawBase =O[atTop] secondOrderScale)
    (Hguard : (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale) :
    qTilde =O[atTop] secondOrderScale := by
  exact (Hraw.sub Hguard.isBigO).congr_left (fun n => by ring)

/-- The nearest-integer `q0` family inherits the upper `O(N)` bound. -/
theorem bankPaperCanonicalSmoothQ0Family_isBigO
    (mFrozen qTilde : Nat -> Real)
    (HqTilde : qTilde =O[atTop] secondOrderScale) :
    bankPaperCanonicalSmoothQ0Family mFrozen qTilde =O[atTop]
      secondOrderScale := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  exact (HqTilde.add hround.isBigO).congr_left (fun n => by ring)

/-! ## The logarithmically smaller height adjustment -/

/-- The paper's scale `n / log^2 n` tends to infinity. -/
theorem secondOrderScale_div_L_tendsto_atTop :
    Tendsto (fun n : Nat => secondOrderScale n / L n) atTop atTop := by
  have hzero : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (nhds 0) := by
    simpa only [L, Function.comp_apply, id_eq] using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := Real))).tendsto_div_nhds_zero
  have hpos : ∀ᶠ n : Nat in atTop,
      0 < L n ^ 2 / (n : Real) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (pow_pos (L_pos hn) 2) (by positivity)
  have hright : Tendsto
      (fun n : Nat => L n ^ 2 / (n : Real)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hnReal : (n : Real) ≠ 0 := by positivity
  apply (eq_div_iff hL.ne').2
  change (L n ^ 2 / (n : Real))⁻¹ * L n = (n : Real) / L n
  rw [inv_div]
  field_simp [hL.ne', hnReal]

/-- The reciprocal of `L + mu` is `O(1/L)` for fixed positive `mu`. -/
theorem bankPaperCanonical_inv_L_add_mu_isBigO_inv_L
    {mu : Real} (hmu : 0 < mu) :
    (fun n : Nat => (L n + mu)⁻¹) =O[atTop]
      (fun n : Nat => (L n)⁻¹) := by
  apply (isBigO_iff).2
  use 1
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : 0 < L n := L_pos hn
  have hdenom : 0 < L n + mu := add_pos hL hmu
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdenom),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), one_mul]
  exact (inv_le_inv₀ hdenom hL).2 (le_add_of_nonneg_right hmu.le)

/-- From `q0 = O(N)` and `A0 = O(N)`, the exact rounded height adjustment
constructed in the companion file satisfies `d = O(N/L)`. -/
theorem bankPaperCanonicalSmoothHeightAdjustment_isBigO
    {mu : Real} (hmu : 0 < mu) (q0 A0 : Nat -> Real)
    (Hq0 : q0 =O[atTop] secondOrderScale)
    (HA0 : A0 =O[atTop] secondOrderScale) :
    (fun n => (bankPaperCanonicalSmoothHeightAdjustment
      n mu (q0 n) (A0 n) : Real)) =O[atTop]
        (fun n => secondOrderScale n / L n) := by
  have hnum : (fun n => mu * q0 n - A0 n) =O[atTop]
      secondOrderScale :=
    (Hq0.const_mul_left mu).sub HA0
  have hinv := bankPaperCanonical_inv_L_add_mu_isBigO_inv_L hmu
  have hcenter : (fun n => bankPaperCanonicalSmoothHeightCenter
      n mu (q0 n) (A0 n)) =O[atTop]
        (fun n => secondOrderScale n / L n) := by
    apply (hnum.mul hinv).congr
    · intro n
      rw [bankPaperCanonicalSmoothHeightCenter, div_eq_mul_inv]
    · intro n
      rw [div_eq_mul_inv]
  have hroundOne :
      (fun n => (bankPaperCanonicalSmoothHeightAdjustment
          n mu (q0 n) (A0 n) : Real) -
        bankPaperCanonicalSmoothHeightCenter n mu (q0 n) (A0 n))
        =O[atTop] (fun _n : Nat => (1 : Real)) := by
    apply (isBigO_iff).2
    use 1 / 2
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
        n mu (q0 n) (A0 n)
  have hone : (fun _n : Nat => (1 : Real)) =O[atTop]
      (fun n => secondOrderScale n / L n) := by
    apply (isBigO_iff).2
    use 1
    have hlarge := secondOrderScale_div_L_tendsto_atTop.eventually
      (eventually_ge_atTop (1 : Real))
    filter_upwards [hlarge] with n hn
    have hnonneg : 0 <= secondOrderScale n / L n := zero_le_one.trans hn
    simpa only [norm_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg hnonneg] using hn
  have hround := hroundOne.trans hone
  exact (hcenter.add hround).congr_left (fun n => by ring)

/-! ## Full propagation from the minimal missing ledger -/

/-- Under the single missing Section 8 analytic ledger, the literal `q0`
family has a positive paper-scale lower bound. -/
theorem bankPaperCanonicalSectionEight_q0_paperScaleLower
    (W K : Nat) {c betaAct : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde) := by
  have hraw := bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
    W K hc hbeta
  have hpost := bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    qTilde hraw Hledger.1
  exact bankPaperCanonicalSmoothQ0Family_paperScaleLower
    mFrozen qTilde hpost

/-- The same ledger gives the paper's displayed `d = O(n/log^2 n)`. -/
theorem bankPaperCanonicalSectionEight_d_isBigO
    (W K : Nat) (c betaAct : Real) {mu : Real} (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    bankPaperCanonicalSmoothDRealFamily
        mu logY Lambda0 mFrozen qTilde =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  have hrawBigO := bankPaperCanonicalRawSmoothBaseMass_isBigO
    W K c betaAct
  have hpostBigO := bankPaperCanonicalPostGuardSmoothMass_isBigO
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    qTilde hrawBigO Hledger.1
  have hq0BigO := bankPaperCanonicalSmoothQ0Family_isBigO
    mFrozen qTilde hpostBigO
  simpa only [bankPaperCanonicalSmoothDRealFamily,
      bankPaperCanonicalSmoothDIntFamily] using
    bankPaperCanonicalSmoothHeightAdjustment_isBigO hmu
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde)
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)
      hq0BigO Hledger.2

/-- Consequently the constructed final active mass `qAct(d) = q0 - d`
retains a positive `n / log n` lower bound. -/
theorem bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
    (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde) := by
  have hq0 := bankPaperCanonicalSectionEight_q0_paperScaleLower
    W K hc hbeta logY Lambda0 mFrozen qTilde Hledger
  have hd := bankPaperCanonicalSectionEight_d_isBigO
    W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  exact bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde)
    (bankPaperCanonicalSmoothDRealFamily
      mu logY Lambda0 mFrozen qTilde) hq0 hd



/-- The exact active-measure constructor threshold follows eventually. -/
theorem eventually_one_le_bankPaperCanonicalSectionEight_finalActiveMass
    (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      1 <= bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde n :=
  eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
    (bankPaperCanonicalSmoothFinalActiveMassFamily
      mu logY Lambda0 mFrozen qTilde)
    (bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
      W K hc hbeta hmu logY Lambda0 mFrozen qTilde Hledger)





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







/-- The fixed-head gap is positive whenever the endpoint-ratio cap is below
two. -/
theorem tangentPaperHeadGap_pos
    (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperHeadGap W r0 := by
  unfold tangentPaperHeadGap
  exact mul_pos (roughHeadDensity_pos W) (sub_pos.mpr hr0)

/-- The retained one-sixteenth clean-list density is positive under the same
ratio cap. -/
theorem tangentPaperCleanListDensity_pos
    (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperCleanListDensity W r0 := by
  unfold tangentPaperCleanListDensity
  exact div_pos (tangentPaperHeadGap_pos W hr0) (by norm_num)











/-! ## The harmonic main term -/





/-! ## Moving-scale negligibility -/





/-! ## Eventual exceptional-loss absorption -/





/-! ## The fixed-head candidate at the paper endpoints -/





/-! ## The literal candidate floor absorbs every canonical loss -/



/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRatioCellMomentTraffic -/
section


/-!
# Moment collapse of the canonical ratio-cell traffic

The endpoint-by-endpoint Mertens envelope is useful for pointwise ports,
but it is deliberately too wasteful for the sum over all cell cuts: its
uniform error is repeated once at every cut.  For total traffic one first
interchanges the two finite sums.  A vertex in cell `i` occurs in exactly
`i` strict tails, so the complete tail census is the first moment of the
literal cell index.

For the canonical multiplicative cells that index is at most

`(log y / log rho) * (t_p - t_lower)`.

The arithmetic moment bounds already proved for the canonical regular
mesh then give the paper-sized factor `delta + ratio`.  The only loss from
the natural floors is the explicit quantity `log 2 / log y`.

No new asymptotic or distribution hypothesis occurs in this file.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## The finite cut/tail interchange -/



/-! ## Logarithmic control of the concrete cell index -/





/-! ## The exact shifted-coordinate moment -/







/-! ## Canonical-mesh bound for the shifted moment -/









/-! ## Moment majorants for the complete traffic ledger -/











/-! ## Paper-scale scalar reduction -/







/-! ## Concrete geometry for the normalized pointwise port -/









/-! ## Scalar Mertens cancellation in one PNT-normalized port -/









/-! ## Collapse of the remaining band endpoint gap -/





/-! ## Uniform paper-scale port envelope -/







/-! ## Paper-scale scalar reduction for the incident ledger -/











/-! ## A manifestly vanishing upper coefficient for total traffic -/











/-! ## Explicit fixed choices for the paper budgets -/



/-- The fixed main-budget coefficient is positive for every `rho > 1`. -/
theorem bankPaperCanonical_ratioCellMainCoefficient_pos
    {rho : Real} (hrho : 1 < rho) :
    0 < bankPaperCanonicalRatioCellMainCoefficient rho := by
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  have hrho0 : 0 < rho := lt_trans zero_lt_one hrho
  have hrhoGap : 0 < rho - 1 := sub_pos.mpr hrho
  unfold bankPaperCanonicalRatioCellMainCoefficient
    bankPaperCanonicalRatioCellTrafficConstant
    bankPaperCanonicalRatioCellIncidentConstant
  exact add_pos
    (mul_pos (by norm_num) (div_pos (by norm_num) hlogrho))
    (mul_pos (by norm_num)
      (div_pos (mul_pos (by norm_num) (sq_pos_of_pos hrho0)) hrhoGap))



/-- The explicit paper width choice is positive under the paper parameter
sign conditions. -/
theorem bankPaperCanonical_ratioCellPaperWidthChoice_pos
    {density sigma rho tangentConstant : Real}
    (hdensity : 0 < density) (hsigma : 0 < sigma)
    (hrho : 1 < rho) (htangent : 0 < tangentConstant) :
    0 < bankPaperCanonicalRatioCellPaperWidthChoice
      density sigma rho tangentConstant := by
  have hcoefficient :
      0 < bankPaperCanonicalRatioCellMainCoefficient rho :=
    bankPaperCanonical_ratioCellMainCoefficient_pos hrho
  unfold bankPaperCanonicalRatioCellPaperWidthChoice
  positivity













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPhysicalMarginAlgebra -/
section


/-!
# The explicit post-height physical margin

This file fixes one completely explicit pair of paper-valid physical
intervals around

`mu = log (3 / 2)`.

The minus pool is `[1, 4 / 3]` and the plus pool is
`[5 / 3, 7 / 4]`.  Thus both pools lie in the paper's physical range
`[1, 2]`, and there is a fixed logarithmic gap on either side of `mu`.

The analytic input is kept transparent.  A generic lemma says that an
error which is `O(scale)` tends to zero whenever `scale` does, and hence
the corresponding centered mean eventually retains half of any fixed
`PhysicalInterpolationTarget` margin.  It is then applied to the literal
post-height physical-mean error and the paper's scale

`L / N`, where `N = secondOrderScale = n / L`.

No target/source wrapper and no conclusion-bearing premise is introduced.
-/

open Filter Topology Set Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

/-! ## Explicit paper-valid physical data -/













/-- The explicit intervals satisfy the lower endpoint restriction used by
the canonical guarded sample. -/
theorem bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one
    (sigma : PhysicalSign) :
    1 ≤ bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
      sigma := by
  cases sigma <;> norm_num



theorem bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos :
    0 < bankPaperCanonicalSectionNinePostHeightPhysicalMu := by
  unfold bankPaperCanonicalSectionNinePostHeightPhysicalMu
  exact Real.log_pos (by norm_num)



















/-! ## The elementary asymptotic margin algebra -/







/-! ## The literal post-height physical mean -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightCoherentTargetConstructor -/
section


/-!
# The coherent finite post-height target constructor

This file closes the finite choice boundary between the depth-first
combined-charge terminal and the fresh Section 9 post-height bridge.

There are two deliberately separate pieces.

* The first theorem turns the eventual existential output of
  `BankPaperCombinedChargeTerminalAtDepth` into one honest tail family.  Its
  conclusion repeats the six literal terminal properties pointwise; no
  conclusion-bearing structure is introduced.
* The bridge definitions below start from an actual
  `StructuredSampleData`, build a harmless scaffold bridge, form the
  paper's literal head/physical barycentric target on that sample, and then
  install that same target in a canonical bridge.  This removes the
  otherwise circular-looking dependence of `barycentricTargetOfPaperData`
  on an already supplied `BridgeData`.

The eventual head and physical interior estimates are proved in the
remaining sections of this module.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

/-! ## One coherent family chosen from the eventual terminal -/

/-- Choose one realization/certificate pair on a genuine tail from the
depth-first combined-charge terminal.

The six conjuncts are the terminal's literal finite conclusions, retained
for the very same fiber selected by `F`.  In particular this theorem does
not hide any capacity estimate in a new record or contract. -/
theorem
    exists_bankPaperCanonicalGuardedTailFamily_of_combinedChargeTerminalAtDepth
    {c deltaStar : Real} {depth : Nat}
    (H : BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) :
    ∃ N : Nat, ∃ F : BankPaperCanonicalGuardedTailFamily c depth N,
      ∀ n (hn : N ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar) *
              R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) =
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n) := by
  simp only [BankPaperCombinedChargeTerminalAtDepth] at H
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp H
  choose R hR using hN
  choose certificate hcertificate using hR
  let F : BankPaperCanonicalGuardedTailFamily c depth N :=
    { fiber := fun n hn => ⟨R n hn, certificate n hn⟩ }
  refine ⟨N, F, ?_⟩
  intro n hn
  simpa only [F, BankPaperCanonicalGuardedTailFamily.realization,
    BankPaperCanonicalGuardedTailFamily.certificate] using
      hcertificate n hn

/-! ## Uniform finite head bounds from the same fibers -/











/-! ## One pair of source/post-height mass envelopes -/

/-- The final active mass inherits an `O(secondOrderScale)` upper bound from
the guarded smooth mass and the logarithmically smaller integer height
adjustment. -/
theorem bankPaperCanonicalSectionNinePostHeight_finalActiveMass_isBigO
    (W K : Nat) (c betaAct : Real)
    {mu : Real} (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde =O[atTop]
      secondOrderScale := by
  have hraw :=
    bankPaperCanonicalRawSmoothBaseMass_isBigO W K c betaAct
  have hqTilde :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde hraw Hledger.1
  have hq0 :=
    bankPaperCanonicalSmoothQ0Family_isBigO
      mFrozen qTilde hqTilde
  have hdLog :=
    bankPaperCanonicalSectionEight_d_isBigO
      W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  have hd :
      bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde =O[atTop]
        secondOrderScale :=
    hdLog.trans
      secondOrderScale_div_L_isLittleO_secondOrderScale.isBigO
  exact (hq0.sub hd).congr_left fun n => rfl



/-! ## Exact synchronization of the local and family physical means -/



/-! ## A non-circular bridge built from structured sample data -/























/-! ## Finite coherent assembly of the fresh bridge inputs -/



namespace BankPaperRealization



/-! ## Eventual coherent target construction on supplied sample geometry -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceObligationPublicSyncConnector -/
section


/-!
# Public synchronization from the post-height source obligation

This connector projects the three public family equalities carried by the
eventual coherent bridge/source obligation.  It introduces no new
construction or analytic assumption: the public bridge has the ambient
index and fixed width, and its mass is the Section 8 final-active-mass
family.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-- The bridge family exported by the coherent source obligation is
eventually synchronized with the ambient index, the fixed prime width, and
the final active-mass family. -/
theorem
    eventually_bankPaperCanonicalSectionNinePostHeight_coherentBridgeSourceObligation_publicSync
    (P : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 E Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    (deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor Cmass density : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta)
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (Hsource :
      BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
        P Patterns I Cprom Cbank G (c := c) depth W K0 E Ntail F
        deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
        physicalEtaFloor postMarginFloor Cmass density
        logY Lambda0 mFrozen qTilde M hdelta B) :
    ∀ᶠ n : Nat in atTop,
      (B n).sampleData.n = n ∧
        (B n).sampleData.W = W ∧
        (B n).q =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde n := by
  simp only
    [BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation]
    at Hsource
  filter_upwards [Hsource] with n hsourceN
  rcases hsourceN with
    ⟨Bsource, _hnTail, J, _S, Hgap, _hsep, _hremaining,
      hbridge, hBn, hBW, _hbetaProtSync, _hbetaActSync,
      _hcanonical, _hqTilde, _hCmassSync, _hdensitySync⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      (B n).sampleData.n = J.postHeightBridge.sampleData.n := by
        rw [hbridge]
      _ = Bsource.sampleData.n := by
        rw [J.postHeightBridge_sampleData]
      _ = n := hBn
  · calc
      (B n).sampleData.W = J.postHeightBridge.sampleData.W := by
        rw [hbridge]
      _ = Bsource.sampleData.W := by
        rw [J.postHeightBridge_sampleData]
      _ = W := hBW
  · calc
      (B n).q = J.postHeightBridge.q := by
        rw [hbridge]
      _ = J.qn := J.postHeightBridge_q
      _ =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n :=
        Hgap.finalActiveMass_family
      _ =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde n := by
        rw [hBn]

end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCutoffAwareAnalyticCompletion -/
section


/-!
# Cutoff-aware source-first analytic completion

This module performs the remaining source-first choices in the dependency
order used by the paper.  At a fixed capacity depth, Proposition 8.7 first
selects a mesh tolerance and a width cutoff.  Only after the final width is
given do we choose the guarded tail family, the positive protected/active
split, the common Section 8 ledger, the selector and Proposition 8.7
constants, and the tangent budget.  The final dyadic regular mesh is selected
last, fine enough simultaneously for Proposition 8.7 and the Section 9
tangent width.

The conclusion is the public synchronized analytic completion, not a
distributed terminal.  Thus the depth-first combined-charge terminal remains
an explicit input to this construction.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperPermittedRegularMesh
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 4000000 in
/-- At each already selected capacity depth, choose one Proposition 8.7
width cutoff.  Every later width satisfying that cutoff and the public
Section 9 cutoffs admits the complete frozen-top synchronized analytic
completion for the same combined tangent exponent and capacity terminal.

The mesh tolerance is chosen before `W`; all numerical, ledger, selector,
and P87 constants are chosen before the final explicit dyadic mesh. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion
    {c : Real} (hc : C0 < c) :
    ∀ depth : Nat, 201 ≤ depth →
      ∃ W0 : Nat, ∀ W : Nat, W0 ≤ W →
        2 ≤ W →
        2 * depth + 1 ≤ W →
        fullReciprocalSumUniformCutoff ≤ W →
        canonicalActualMomentCutoff ≤ W →
        ∀ r0 deltaStar : Real,
          1 < r0 →
          r0 < 3 / 2 →
          IsPaperCombinedTangentDeltaStar c W r0 deltaStar →
          BankPaperCombinedChargeTerminalAtDepth c deltaStar depth →
          BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion
            c depth W r0 deltaStar := by
  intro depth _hdepth
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  let G : ∀ n, Ledger n 2 0 :=
    roughCanonicalBridgeRelevantLedgerFamily depth
  have hlowerOne : ∀ sign, 1 ≤ I.lower sign := by
    intro sign
    simpa only [I] using
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one sign
  have hupperTwo : ∀ sign, I.upper sign ≤ (2 : Real) := by
    intro sign
    cases sign <;>
      norm_num [I,
        bankPaperCanonicalSectionNinePostHeightPhysicalIntervals]
  have HP87uniform :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshUniformP87
      I 2 0 G
  unfold
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Statement
    at HP87uniform
  obtain ⟨meshTol, hmeshTol, W0, HP87width⟩ :=
    HP87uniform hlowerOne hupperTwo
  refine ⟨W0, ?_⟩
  intro W hW0 hTwoW hprefix _hMertens hMoment
    r0 deltaStar _hr0one hr0three hdeltaStar Hcharge
  have hcPos : 0 < c :=
    (show (0 : Real) < C0 by norm_num [C0]).trans hc
  have hWpos : 0 < W := by omega
  obtain ⟨Ntail, F, hterminal⟩ :=
    exists_bankPaperCanonicalGuardedTailFamily_of_combinedChargeTerminalAtDepth
      Hcharge

  /- The protected and active pieces are a fixed positive half-budget split.
  The multiplicity is then selected by the Archimedean property. -/
  let betaPiece : Real :=
    (c / roughHeadDensity W) / 4
  let betaProt : Real := betaPiece
  let betaAct : Real := betaPiece
  have hHeadDensity : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  have hBetaScale : 0 < c / roughHeadDensity W :=
    div_pos hcPos hHeadDensity
  have hbetaPiece : 0 < betaPiece := by
    dsimp only [betaPiece]
    positivity
  have hbetaProt : 0 < betaProt := by
    simpa only [betaProt] using hbetaPiece
  have hbetaAct : 0 < betaAct := by
    simpa only [betaAct] using hbetaPiece
  have hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W := by
    dsimp only [betaProt, betaAct, betaPiece]
    linarith
  obtain ⟨K0, hK0⟩ :=
    exists_nat_gt (1 / roughHeadDensity W)
  have hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real)) := by
    calc
      1 / roughHeadDensity W ≤ (K0 : Real) := hK0.le
      _ ≤ (((K0 + 1 : Nat) : Real)) := by norm_num

  have HpreMeshSource :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshEventualCoherentBridgeSourceObligation
      hc hdeltaStar.1 hWpos hbetaProt.le hbetaAct hbetaUpper hKlarge
        hprefix F hterminal
  dsimp only at HpreMeshSource
  obtain
      ⟨E, sourceCellMargin, postMargin, Cmass, sourceDensity,
        logY, Lambda0, mFrozen, hE, hsourceCellMargin,
        hpostMargin, hphysicalEtaFloor, hpostCellMargin,
        hCmass, hsourceDensity, hlogY, HledgerRaw, HsourceRaw⟩ :=
    HpreMeshSource

  let P := primesUpTo W
  let hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    simpa only [P] using
      bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W p hp
  let Patterns : PaperHeadSimplex.Tag P → Pattern :=
    PaperHeadSimplex.pattern P hprime E
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar
  let physicalEtaFloor : Real :=
    bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2
  let postCellMargin : Real :=
    postMargin *
      (physicalEtaFloor /
        PhysicalInterpolationTarget.physicalSpan I)
  let qMass : Nat → Real :=
    bankPaperCanonicalSmoothFinalActiveMassFamily
      bankPaperCanonicalSectionNinePostHeightPhysicalMu
      logY Lambda0 mFrozen qTilde
  have Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
            (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde) := by
    simpa only [qTilde] using HledgerRaw
  have Hsource :
      ∀ {delta eta : Real}
          (M : RegularRelativeMesh.Mesh delta eta)
          (hdelta : 0 < delta),
        ∃ B : Nat → BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M),
          BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
            P Patterns I 2 0 G (c := c) depth W K0 E Ntail F
            deltaStar betaProt betaAct
            bankPaperCanonicalSectionNinePostHeightPhysicalMu
            sourceCellMargin postMargin physicalEtaFloor postCellMargin
            Cmass sourceDensity logY Lambda0 mFrozen qTilde
            M hdelta B := by
    intro delta eta M hdelta
    obtain ⟨B, HsourceM⟩ := HsourceRaw M hdelta
    refine ⟨B, ?_⟩
    simpa only [
      P, hprime, Patterns, I, G, qTilde, physicalEtaFloor, postCellMargin]
      using HsourceM
  have hqMassOne :
      ∀ᶠ n : Nat in atTop, 1 ≤ qMass n := by
    simpa only [qMass] using
      eventually_one_le_bankPaperCanonicalSectionEight_finalActiveMass
        W (K0 + 1) hcPos hbetaAct
          bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
          logY Lambda0 mFrozen qTilde Hledger
  have hPatterns :
      ∀ h : PaperHeadSimplex.Tag P, ∀ p : Nat,
        p ∈ (Patterns h).primes ↔ p.Prime ∧ p ≤ W := by
    intro h p
    change p ∈ P ↔ p.Prime ∧ p ≤ W
    simpa only [P] using (mem_primesUpTo (B := W) (p := p))
  have hHeadLe :
      ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W := by
    intro h q hq
    exact ((hPatterns h q).mp hq).2

  /- The common ledger selects the public bridge-mass coefficient and the
  mesh-uniform selector before the P87 constants and before the mesh. -/
  have HqMassBigO : qMass =O[atTop] secondOrderScale := by
    simpa only [qMass] using
      bankPaperCanonicalSectionNinePostHeight_finalActiveMass_isBigO
        W (K0 + 1) c betaAct
          bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
          logY Lambda0 mFrozen qTilde Hledger
  obtain ⟨Cq, hCq, HqMassNorm⟩ := HqMassBigO.exists_pos
  have HqMassUpper :
      ∀ᶠ n : Nat in atTop,
        qMass n ≤ Cq * secondOrderScale n := by
    filter_upwards [
      HqMassNorm.bound, eventually_secondOrderScale_pos] with
        n hnorm hscale
    calc
      qMass n ≤ |qMass n| := le_abs_self _
      _ = ‖qMass n‖ := (Real.norm_eq_abs _).symm
      _ ≤ Cq * ‖secondOrderScale n‖ := hnorm
      _ = Cq * secondOrderScale n := by
        rw [Real.norm_eq_abs, abs_of_pos hscale]
  obtain ⟨Cinitial, hCinitial, Hselector⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider
      Patterns I 2 0 G (c := c) depth W K0
        deltaStar betaProt betaAct
        bankPaperCanonicalSectionNinePostHeightPhysicalMu
        logY Lambda0 mFrozen qTilde Hledger
        hTwoW hHeadLe hcPos hdeltaStar.1.1 hdeltaStar.1.2.1
        hbetaAct hprefix
        bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
  obtain ⟨radius, hradius, CP87, hCP87, HP87mesh⟩ :=
    HP87width W hW0 qMass hqMassOne Patterns hPatterns
      (c := c) depth K0 deltaStar betaProt betaAct
        postCellMargin Cmass sourceDensity
        hbetaProt.le hCmass.le hsourceDensity hpostCellMargin
        Cinitial hCinitial

  let rho : Real := 21 / 20
  let sigma : Real := betaProt / 2
  let tangentConstant : Real :=
    max 1 ((2 / 9 : Real) * CP87 * Cq)
  have hrho : 1 < rho := by norm_num [rho]
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    positivity
  have hsigmaProt : sigma ≤ betaProt := by
    dsimp only [sigma]
    linarith
  have htangent : 0 < tangentConstant :=
    zero_lt_one.trans_le (by
      dsimp only [tangentConstant]
      exact le_max_left _ _)
  have hcoefficient :
      (2 / 9 : Real) * CP87 * Cq ≤ tangentConstant := by
    dsimp only [tangentConstant]
    exact le_max_right _ _
  have hCleanDensity :
      0 < tangentPaperCleanListDensity W r0 :=
    tangentPaperCleanListDensity_pos W
      (hr0three.trans (by norm_num))
  let widthChoice : Real :=
    bankPaperCanonicalRatioCellPaperWidthChoice
      (tangentPaperCleanListDensity W r0)
      sigma rho tangentConstant
  have hwidthChoice : 0 < widthChoice := by
    simpa only [widthChoice] using
      bankPaperCanonical_ratioCellPaperWidthChoice_pos
        hCleanDensity hsigma hrho htangent
  let meshChoiceTol : Real :=
    min meshTol widthChoice / 2
  have hmeshChoiceTol : 0 < meshChoiceTol := by
    dsimp only [meshChoiceTol]
    exact div_pos (lt_min hmeshTol hwidthChoice) (by norm_num)
  obtain ⟨Kmesh, Nmesh, hKmesh, hNmesh,
      hdeltaFine, hratioFine, _hcellFine⟩ :=
    SelectedDyadicRegularMesh.exists_fine_mesh
      meshChoiceTol hmeshChoiceTol
  let delta : Real := SelectedDyadicRegularMesh.delta Kmesh
  let eta : Real := SelectedDyadicRegularMesh.ratio Nmesh
  let M : RegularRelativeMesh.Mesh delta eta :=
    SelectedDyadicRegularMesh.mesh Kmesh Nmesh (by omega) hNmesh
  have hdelta : 0 < delta := by
    dsimp only [delta, SelectedDyadicRegularMesh.delta]
    positivity
  have hfine : delta + eta ≤ meshTol := by
    have hsum : delta + eta < 2 * meshChoiceTol := by
      dsimp only [delta, eta]
      linarith
    have hmin : min meshTol widthChoice ≤ meshTol :=
      min_le_left _ _
    dsimp only [meshChoiceTol] at hsum
    linarith
  have hwidth : delta + M.ratio ≤ widthChoice := by
    have hsum : delta + eta < 2 * meshChoiceTol := by
      dsimp only [delta, eta]
      linarith
    have hmin : min meshTol widthChoice ≤ widthChoice :=
      min_le_right _ _
    have hratioM : M.ratio = eta := rfl
    rw [hratioM]
    dsimp only [meshChoiceTol] at hsum
    linarith
  have hPermitted :
      IsPermitted (cMesh := (1 : Real)) M := by
    unfold IsPermitted
    change (1 : Real) * eta ≤ eta
    norm_num
  obtain ⟨B, HsourceM⟩ := Hsource M hdelta
  have HP87M :=
    HP87mesh M hdelta hPermitted hfine
  have Hinput :=
    bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput
      M Patterns I 2 0 G (c := c) depth W K0 E Ntail F
        deltaStar betaProt betaAct
        bankPaperCanonicalSectionNinePostHeightPhysicalMu
        sourceCellMargin postMargin physicalEtaFloor postCellMargin
        Cmass sourceDensity logY Lambda0 mFrozen qTilde
        rho sigma Cinitial radius CP87 hdelta B HsourceM
        Hselector HP87M hCinitial hradius hCP87 hcPos hTwoW
        hdeltaStar.1.1 hbetaProt.le hbetaAct hbetaUpper hKlarge
        hCmass.le hsourceDensity hsigma hsigmaProt hMoment
  have Hpublic :=
    eventually_bankPaperCanonicalSectionNinePostHeight_coherentBridgeSourceObligation_publicSync
      P Patterns I 2 0 G (c := c) depth W K0 E Ntail F
        deltaStar betaProt betaAct
        bankPaperCanonicalSectionNinePostHeightPhysicalMu
        sourceCellMargin postMargin physicalEtaFloor postCellMargin
        Cmass sourceDensity logY Lambda0 mFrozen qTilde
        M hdelta B HsourceM
  have Hsync :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n ∧
          (B n).sampleData.W = W :=
    Hpublic.mono fun _ hn => ⟨hn.1, hn.2.1⟩
  have HBqUpper :
      ∀ᶠ n : Nat in atTop,
        (B n).q ≤ Cq * secondOrderScale n := by
    filter_upwards [Hpublic, HqMassUpper] with n hpublic hupper
    calc
      (B n).q = qMass n := by
        simpa only [qMass] using hpublic.2.2
      _ ≤ Cq * secondOrderScale n := hupper

  unfold
    BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion
  refine
    ⟨delta, eta, M, P, B, K0, tangentConstant, sigma,
      CP87, Cq, hdelta, htangent, hsigma, ?_, hCP87,
      hcoefficient, Hsync, HBqUpper, ?_⟩
  · simpa only [widthChoice, rho] using hwidth
  · simpa only [rho] using Hinput

end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal004_019 := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion
