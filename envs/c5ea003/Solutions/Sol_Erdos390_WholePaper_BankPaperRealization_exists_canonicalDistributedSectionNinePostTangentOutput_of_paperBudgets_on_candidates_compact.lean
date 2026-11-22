-- Prove2me | solution 1 for Erdos390.WholePaper.BankPaperRealization.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:28:10.471623+00:00
-- url     : https://prove2.me/submissions/e1436de8-4cce-4e4c-83fd-ec0eab71f5be

import Definitions.Def_erdos390_remaining_analytic_propositions_007
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Definitions.Def_erdos390_analytic_foundations_007
import Definitions.Def_erdos390_analytic_foundations_008
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
import Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus_compact


section
universe u_1
theorem Erdos390.WholePaper.BankPaperRealization.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus : Erdos390.RemainingAnalyticGoal008_001.{u_1} := @Erdos390.WholePaper.BankPaperRealization.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus_compact
end
/- Source module: Erdos390.WholePaper.BankAnchorCollisionFree -/
section


/-!
# Collision freedom between the complete central anchors and the actual bank

The large-anchor branch recovers the common prime marker from the complete
rough factorization above `yNat`.  Once the marker is recovered, the guarded
central-cofactor certificate excludes the two incident state cores.

The residual branch uses the more rigid shape
`2^k * p^e`.  A bottom marker is already above the residual cutoff.  For an
ordinary marker, divisibility first forces the residual base prime to be the
marker; its marker valuation is then one, so cancellation would make the
ordinary state core a power of two, contrary to the path certificate.

Donor-only occurrences do not create an extra case: ordinary donors and the
two nonterminal bottom donors lie above `2n`, while terminal bottom donors
are literally their upper endpoint state.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## The two eventual scale separations used by marker recovery -/

/-- The elementary square bound behind the separation
`yNat n < centralAnchorCutoff depth n`. -/
theorem bankAnchor_yNat_mul_self_le_self
    {n : ℕ} (hn : 1 ≤ n) : yNat n * yNat n ≤ n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hyFloorNonneg : (0 : ℝ) ≤ yNat n := by positivity
  have hsq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyFloorNonneg hyNonneg).2 hyFloor
  have hpow : (n : ℝ) ^ (4 / 9 : ℝ) ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne
        (by norm_num : (4 / 9 : ℝ) ≤ 1)
  rw [Erdos390.Full.Scale.y_pow_two] at hsq
  have hcast : ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    simpa only [pow_two] using hsq.trans hpow
  exact_mod_cast hcast









/-! ## Arithmetic collision kernels -/



namespace BankPaperRealization



/-! ## Literal recovery of the incident cores from actual requests -/





















/-! ## Complete finite collision theorem -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentStarTransport -/
section


/-!
# Exact finite star transport for tangent residuals

A zero-sum residual on a finite vertex type is transported through one
chosen pivot.  Positive residual leaves its vertex for the pivot; negative
residual is supplied from the pivot.  The construction is literal,
nonnegative, supported on the star, and has exactly the requested
divergence.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







variable {V : Type*} [DecidableEq V]

/-! ## Pointwise support and sign -/











/-! ## Exact outgoing and incoming sums -/

variable [Fintype V]















/-! ## Traffic -/





/-! ## Boundary identities consumed by `TangentFlowAlgebra` -/

/-- Finite integration by parts for any directed flow. -/
theorem tangentFlow_weightedBoundary_eq_divergence
    {W : Type*} [Fintype W]
    (flow : W → W → ℝ) (value : W → ℝ) :
    (∑ source : W, ∑ target : W,
        flow source target * (value source - value target)) =
      ∑ v : W, tangentFlowDivergence flow v * value v := by
  classical
  have hout :
      (∑ source : W, ∑ target : W,
          flow source target * value source) =
        ∑ source : W,
          (∑ target : W, flow source target) * value source := by
    apply Finset.sum_congr rfl
    intro source _hsource
    rw [Finset.sum_mul]
  have hin :
      (∑ source : W, ∑ target : W,
          flow source target * value target) =
        ∑ target : W,
          (∑ source : W, flow source target) * value target := by
    calc
      (∑ source : W, ∑ target : W,
          flow source target * value target) =
          ∑ target : W, ∑ source : W,
            flow source target * value target := by
        rw [Finset.sum_comm]
      _ = ∑ target : W,
          (∑ source : W, flow source target) * value target := by
        apply Finset.sum_congr rfl
        intro target _htarget
        rw [Finset.sum_mul]
  calc
    (∑ source : W, ∑ target : W,
        flow source target * (value source - value target)) =
        (∑ source : W, ∑ target : W,
          flow source target * value source) -
        ∑ source : W, ∑ target : W,
          flow source target * value target := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ source : W,
          (∑ target : W, flow source target) * value source) -
        ∑ target : W,
          (∑ source : W, flow source target) * value target := by
      rw [hout, hin]
    _ = ∑ v : W, tangentFlowDivergence flow v * value v := by
      simp only [tangentFlowDivergence, sub_mul,
        Finset.sum_sub_distrib]









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentRequestSplitting -/
section


/-!
# Literal finite splitting of tangent-flow requests

This file formalizes only the algebra in the paper's request splitting.
It assumes concrete nonnegative edge masses and forms explicit `Fin k`
families of equal pieces.  It contains no flow-existence, list-capacity,
or collision-avoidance assertion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem one_le_tangentRequestCount (L sigma f : ℝ) :
    1 ≤ tangentRequestCount L sigma f := by
  exact le_max_left 1 (Nat.ceil (4 * L * f / sigma))

theorem tangentRequestCount_pos (L sigma f : ℝ) :
    0 < tangentRequestCount L sigma f := by
  exact lt_of_lt_of_le Nat.zero_lt_one (one_le_tangentRequestCount L sigma f)











/-- The `Fin k` equal pieces of one edge sum exactly to its original mass. -/
theorem sum_tangentRequestPieceMass
    (L sigma f : ℝ) :
    (∑ _i : Fin (tangentRequestCount L sigma f),
        tangentRequestPieceMass L sigma f) = f := by
  have hk : (tangentRequestCount L sigma f : ℝ) ≠ 0 := by
    exact_mod_cast (tangentRequestCount_pos L sigma f).ne'
  simp only [tangentRequestPieceMass, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp





























/-- Request splitting preserves the complete directed edge boundary when
tested against any label function.  This is the exact bridge from the
paper's edge flow to the request family consumed by `tangentUpdate`. -/
theorem sum_tangentSplitRequestWeight_mul_sub
    {E P : Type*} (edges : Finset E) (source target : E → P)
    (L sigma : ℝ) (flow : E → ℝ) (value : P → ℝ) :
    (∑ request : TangentSplitRequest edges L sigma flow,
        tangentSplitRequestWeight request *
          (value (tangentSplitRequestSource source request) -
            value (tangentSplitRequestTarget target request))) =
      ∑ e ∈ edges, flow e * (value (source e) - value (target e)) := by
  classical
  simp only [TangentSplitRequest, tangentSplitRequestWeight,
    tangentSplitRequestSource, tangentSplitRequestTarget,
    tangentSplitRequestEdge, Fintype.sum_sigma]
  calc
    (∑ e : ↑edges,
        ∑ _i : Fin (tangentRequestCount L sigma (flow e.1)),
          tangentRequestPieceMass L sigma (flow e.1) *
            (value (source e.1) - value (target e.1))) =
      ∑ e : ↑edges,
        flow e.1 * (value (source e.1) - value (target e.1)) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [← Finset.sum_mul, sum_tangentRequestPieceMass]
    _ = ∑ e ∈ edges,
        flow e * (value (source e) - value (target e)) := by
      simpa using Finset.sum_attach edges
        (fun e ↦ flow e * (value (source e) - value (target e)))















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridge -/
section


/-!
# Literal canonical residual for the selector-to-tangent handoff

The canonical Saias reduction currently stops at a selector continuation: it
does not yet construct the pre-tangent rounded selector.  This file removes
the *generic residual* ambiguity without asserting that missing construction.

For a supplied selector `x`, the residual coordinate at a medium prime is
defined literally as

`valuation(selectorTailTarget) - valuation(x)`.

The two remaining selector inputs are named explicitly.  The post-rounding
prime-band balance says that these coordinates sum to zero, while prime-band
support says that the selector already has the target valuation at every
prime outside the band.  Neither fact follows merely from
`roughCanonicalRawRowQuotaError`: that quantity is a complete-rough row quota
error, not a prime-coordinate valuation identity.

From those inputs, the finite prime residual has zero total mass and its
positive star split requests have exactly the valuation deficit required by
`tangentUpdate_valuation_eq_target`.  The final theorem also retains the
all-row integrality input verbatim.  It does not claim that clean common
multipliers, feasibility of the tangent update, or the selector itself have
already been constructed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal selector deficit and its finite prime domain -/















/-! ## Prime-label geometry and exact residual algebra -/

/-- The subtype-to-natural prime label map is injective. -/
theorem bankPaperCanonicalTangentPrimeLabel_injective
    {n W : ℕ} :
    Function.Injective
      (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W)) := by
  intro p q hpq
  exact Subtype.ext hpq

/-- Every canonical tangent label is prime. -/
theorem bankPaperCanonicalTangentPrimeLabel_prime
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p).Prime := by
  exact prime_of_mem_primeBand p.2

/-- Every canonical tangent label lies below the paper smooth cutoff. -/
theorem bankPaperCanonicalTangentPrimeLabel_le_yNat
    {n W : ℕ} (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalTangentPrimeLabel p ≤ yNat n := by
  exact le_yNat_of_mem_primeBand p.2

/-- At a non-prime coordinate, both the target and every candidate
factorization vanish. -/
theorem bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_not_prime
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ) {q : ℕ}
    (hq : ¬q.Prime) :
    bankPaperCanonicalSelectorValuationDeficit
      R certificate fixed candidates x q = 0 := by
  simp [bankPaperCanonicalSelectorValuationDeficit,
    Nat.factorization_eq_zero_of_not_prime _ hq]



/-- Prime labels form the standard factorization basis on the finite band.
This statement is independent of the selector and is useful for exposing
the exact support requirement. -/
theorem sum_bankPaperCanonicalTangentPrime_factorization
    {n W : ℕ} (coefficient : ℕ → ℝ) (q : ℕ) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
        coefficient p.1 *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
      if q ∈ primeBand n W then coefficient q else 0 := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime n W,
        coefficient p.1 *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
        ∑ p ∈ primeBand n W,
          coefficient p * (p.factorization q : ℝ) := by
      simpa only [bankPaperCanonicalTangentPrimeLabel] using
        (Finset.sum_subtype (primeBand n W) (fun _p ↦ Iff.rfl)
          (fun p ↦ coefficient p * (p.factorization q : ℝ))).symm
    _ = if q ∈ primeBand n W then coefficient q else 0 := by
      by_cases hq : q ∈ primeBand n W
      · rw [if_pos hq, Finset.sum_eq_single q]
        · simp only [(prime_of_mem_primeBand hq).factorization_self,
            Nat.cast_one, mul_one]
        · intro p hp hpq
          have hpPrime : p.Prime := prime_of_mem_primeBand hp
          have hfactorization : p.factorization q = 0 := by
            by_contra hnonzero
            exact hpq (hpPrime.eq_of_factorization_pos hnonzero)
          simp only [hfactorization, Nat.cast_zero, mul_zero]
        · exact fun hqNotMem ↦ (hqNotMem hq).elim
      · rw [if_neg hq]
        apply Finset.sum_eq_zero
        intro p hp
        have hpPrime : p.Prime := prime_of_mem_primeBand hp
        have hpq : p ≠ q := by
          intro hpq
          apply hq
          simpa only [hpq] using hp
        have hfactorization : p.factorization q = 0 := by
          by_contra hnonzero
          exact hpq (hpPrime.eq_of_factorization_pos hnonzero)
        simp only [hfactorization, Nat.cast_zero, mul_zero]

/-- The finite prime residual expands to the full selector valuation deficit.
The only non-definitional input is exact agreement outside the prime band. -/
theorem sum_bankPaperCanonicalTangentResidual_mul_factorization_eq_deficit
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
      R certificate fixed candidates x) (q : ℕ) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
            R certificate fixed candidates x p *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
      bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates x q := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
            R certificate fixed candidates x p *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : ℝ)) =
        if q ∈ primeBand n W then
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x q
        else 0 := by
      simpa only [bankPaperCanonicalTangentResidual] using
        sum_bankPaperCanonicalTangentPrime_factorization
          (n := n) (W := W)
          (fun p ↦ bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x p) q
    _ = bankPaperCanonicalSelectorValuationDeficit
          R certificate fixed candidates x q := by
      by_cases hqBand : q ∈ primeBand n W
      · rw [if_pos hqBand]
      · rw [if_neg hqBand]
        by_cases hqPrime : q.Prime
        · exact (hsupport q hqPrime hqBand).symm
        · exact (bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_not_prime
            R certificate fixed candidates x hqPrime).symm

/-! ## Instantiation of the star split-request boundary -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentDistributedFlowCensus -/
section


/-!
# Distributed finite-band flow census

This file isolates the quantitative interface needed between a genuine
finite-band earthmover and the already formalized split-request collision
terminal.  Unlike the one-pivot star, a distributed earthmover records a
separate port load at every vertex.  Its two analytic ledgers are

* `traffic <= (1/2) * ||residual||_1 + 2 * cutTraffic`;
* `incident(label v) <= |residual v| + 2 * portLoad v`.

These are the literal estimates produced by the cell-boundary construction
in the paper.  They are strictly stronger than the final collision target
and do not mention a density or the constant `1 / 24`.

The module proves all consequences after those construction ledgers:

* positive support has at most `|V|^2` edges;
* the total split-request count and every endpoint-label request load have
  explicit upper bounds;
* fixed main/error/ceiling parameter budgets imply the exact existing guard
  `4*T + I_source + I_target <= density^2/24` for every request;
* hence the already proved `1/8` collision-census conclusion follows.

Existence of the cell earthmover is deliberately not postulated here.  It
must be constructed from band balance, prefix-load bounds, cell cardinality,
and adjacent-cell ratio geometry.  The downstream theorems keep every
construction estimate as a visible
hypothesis, so the unfinished construction cannot be confused with a
selector theorem or with the final collision target.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Residual, cut, and port ledgers -/









/-! ## Literal ratio-cell cuts and uniform adjacent-cell ports -/







































/-- Uniform distribution makes the absolute boundary divergence at a port
no larger than its two-sided incident boundary traffic. -/
theorem abs_tangentRatioCellBoundaryDivergence_le_portLoad
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) :
    |tangentRatioCellBoundaryDivergence residual bandOf cellIndex v| <=
      tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  unfold tangentRatioCellBoundaryDivergence
    tangentRatioCellUniformPortLoad
  rw [abs_div]
  have hcardNonneg :
      0 ≤ (tangentRatioCellCard bandOf cellIndex
        (bandOf v) (cellIndex v) : Real) := Nat.cast_nonneg _
  rw [abs_of_nonneg hcardNonneg]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [add_comm] using
    abs_sub
      (tangentRatioCellPrefixMass residual bandOf cellIndex
        (bandOf v) (cellIndex v))
      (tangentRatioCellLeftPrefixMass residual bandOf cellIndex v)

/-- Once an internal matching realizes the adjusted residual with incident
mass `|q_p|`, adding the two boundary ports gives exactly the paper's
pointwise ledger `|q_p| + b_p <= |r_p| + 2 b_p`. -/
theorem abs_internalResidual_add_portLoad_le
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) :
    |tangentRatioCellInternalResidual residual bandOf cellIndex v| +
        tangentRatioCellUniformPortLoad residual bandOf cellIndex v <=
      |residual v| +
        2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  have hboundary :=
    abs_tangentRatioCellBoundaryDivergence_le_portLoad
      residual bandOf cellIndex v
  have hinternal :
      |tangentRatioCellInternalResidual residual bandOf cellIndex v| <=
        |residual v| +
          |tangentRatioCellBoundaryDivergence
            residual bandOf cellIndex v| := by
    simpa only [tangentRatioCellInternalResidual] using
      abs_sub (residual v)
        (tangentRatioCellBoundaryDivergence
          residual bandOf cellIndex v)
  linarith

/-! ## Visible hypotheses for a distributed construction -/

/- The construction estimates are deliberately *not* bundled into a
structure.  The repository audit discipline forbids hiding a claimed
traffic or incident estimate in a conclusion-bearing certificate.  Every
generic theorem below therefore displays the exact flow property that it
uses. -/

/-! ## Support, locality, and literal traffic consequences -/









/-! ## Boundary preservation for an arbitrary distributed flow -/

/-- Restricting a nonnegative flow to its strictly positive support does not
change any weighted edge sum. -/
theorem sum_tangentPositiveFlowEdges_mul_eq_full_of_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (value : V × V -> Real) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * value edge) =
      ∑ edge : V × V, flow edge.1 edge.2 * value edge := by
  classical
  apply Finset.sum_subset
    (Finset.subset_univ (tangentPositiveFlowEdges flow))
  intro edge _hedge hedge
  have hnotPos : ¬0 < flow edge.1 edge.2 := by
    simpa only [mem_tangentPositiveFlowEdges] using hedge
  have hzero : flow edge.1 edge.2 = 0 :=
    le_antisymm (le_of_not_gt hnotPos) (hflow edge.1 edge.2)
  simp only [hzero, zero_mul]

/-- The positive support of a distributed earthmover has exactly the
prescribed residual boundary against every vertex test function. -/
theorem tangentDistributedPositiveEdges_boundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (value : V -> Real) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * (value edge.1 - value edge.2)) =
      ∑ v : V, residual v * value v := by
  calc
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * (value edge.1 - value edge.2)) =
      ∑ edge : V × V,
        flow edge.1 edge.2 * (value edge.1 - value edge.2) :=
      sum_tangentPositiveFlowEdges_mul_eq_full_of_nonneg
        flow hflow
          (fun edge => value edge.1 - value edge.2)
    _ = ∑ source : V, ∑ target : V,
        flow source target * (value source - value target) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ v : V,
        tangentFlowDivergence flow v * value v :=
      tangentFlow_weightedBoundary_eq_divergence flow value
    _ = ∑ v : V, residual v * value v := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [hdivergence v]

/-- Factorization-coordinate form of the distributed boundary. -/
theorem tangentDistributedPositiveEdges_factorizationBoundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (p : Nat) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 *
          (((tangentStarEdgeSource label edge).factorization p : Real) -
            ((tangentStarEdgeTarget label edge).factorization p : Real))) =
      ∑ v : V, residual v * (label v).factorization p := by
  simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using
    tangentDistributedPositiveEdges_boundary_eq_residual
      flow residual hflow hdivergence
      (fun v => ((label v).factorization p : Real))

/-- Equal request splitting preserves the distributed residual boundary. -/
theorem tangentDistributedSplitRequest_factorizationBoundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (L sigma : Real) (p : Nat) :
    (∑ request : TangentSplitRequest
          (tangentPositiveFlowEdges flow) L sigma
            (fun edge : V × V => flow edge.1 edge.2),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource (tangentStarEdgeSource label)
                request).factorization p : Real) -
            ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                request).factorization p : Real))) =
      ∑ v : V, residual v * (label v).factorization p := by
  calc
    (∑ request : TangentSplitRequest
          (tangentPositiveFlowEdges flow) L sigma
            (fun edge : V × V => flow edge.1 edge.2),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource (tangentStarEdgeSource label)
                request).factorization p : Real) -
            ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                request).factorization p : Real))) =
      ∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 *
          (((tangentStarEdgeSource label edge).factorization p : Real) -
            ((tangentStarEdgeTarget label edge).factorization p : Real)) := by
      simpa only using
        sum_tangentSplitRequestWeight_mul_sub
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          L sigma (fun edge : V × V => flow edge.1 edge.2)
          (fun q => (q.factorization p : Real))
    _ = ∑ v : V, residual v * (label v).factorization p :=
      tangentDistributedPositiveEdges_factorizationBoundary_eq_residual
        flow label residual hflow hdivergence p

/-! ## Weighted per-label port control -/









/-! ## Total and endpoint request counts -/









/-! ## Paper-parameter closure of the collision guard

The three budgets below mirror the actual parameter order in Section 9.
The main term is made small by the fixed band width `w`; the error and
ceiling terms are absorbed only after the mesh is fixed and `n` tends to
infinity.  None of them is a traffic or request-count hypothesis. -/















/-! ## Connector to the actual paper collision terminal -/

namespace BankPaperRealization



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalPreTangentSelector -/
section


/-!
# Honest selector-rounding interface for the finite-band tangent

The canonical Saias theorem controls complete-rough row quota errors, while
the tangent consumes prime-valuation residuals of an actual rounded
selector.  Those are different index sets, so a row error cannot simply be
renamed as traffic.

This file records the minimal missing selector-rounding output as a
predicate on an explicit selector.  It contains no flow, request count,
density, or collision target.  The residual estimates are exactly the two
inputs used upstream of the paper earthmover:

* the pointwise prime estimate;
* signed prefix estimates on literal ratio-cell cuts.

Unlike a conclusion-bearing structure, the selector and every requested
property remain visible in the existential handoff proposition.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section





/-! ## Direct projections used by downstream assembly -/

theorem bankPaperCanonicalRoundedSelectorTangentInput_selectorState
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      left right changed}
    {fixed candidates : Finset Nat}
    {Band : Type*} [DecidableEq Band]
    {bandOf : BankPaperCanonicalTangentPrime n W -> Band}
    {cellIndex : BankPaperCanonicalTangentPrime n W -> Nat}
    {pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real}
    {prefixUpper : Band -> Nat -> Real}
    {selector : Nat -> Real}
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector) :
    (∀ a ∈ candidates,
        0 <= selector a ∧ selector a <= 1) ∧
      BankPaperCanonicalSelectorRowIntegral n candidates selector ∧
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed candidates selector ∧
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed candidates selector := by
  exact ⟨S.1, S.2.1, S.2.2.1, S.2.2.2.1⟩

theorem bankPaperCanonicalRoundedSelectorTangentInput_residualBounds
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      left right changed}
    {fixed candidates : Finset Nat}
    {Band : Type*} [DecidableEq Band]
    {bandOf : BankPaperCanonicalTangentPrime n W -> Band}
    {cellIndex : BankPaperCanonicalTangentPrime n W -> Nat}
    {pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real}
    {prefixUpper : Band -> Nat -> Real}
    {selector : Nat -> Real}
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector) :
    (forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0) ∧
      (forall p : BankPaperCanonicalTangentPrime n W,
        |bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p| <=
          pointwiseUpper p) ∧
      (forall band : Band, forall cut : Nat,
        |tangentRatioCellPrefixMass
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex band cut| <= prefixUpper band cut) := by
  exact ⟨S.2.2.2.2.1, S.2.2.2.2.2.1, S.2.2.2.2.2.2⟩

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentBalancedProductFlow -/
section


/-!
# Canonical balanced product transport

For a finite signed residual of total mass zero, this file gives the
explicit dense transport

`max (q u) 0 * max (-q v) 0 / sum_w max (q w) 0`.

Thus every positive coordinate sends its mass proportionally to all
negative coordinates.  The construction is nonnegative, has no loops,
has divergence exactly `q`, total traffic exactly half the `ell^1` mass,
and incident traffic at `v` exactly `|q v|`.  The last identity is why this
construction is used inside a ratio cell: a star or a deterministic chain
would concentrate the internal traffic at a pivot and would not give the
paper's pointwise endpoint ledger.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem tangentPositiveMass_nonneg
    {V : Type*} [Fintype V] (q : V -> Real) :
    0 <= tangentPositiveMass q := by
  unfold tangentPositiveMass
  exact Finset.sum_nonneg fun v _hv => le_max_right (q v) 0



/-- Zero total signed mass is equivalent to equality of the two Jordan
masses. -/
theorem tangentPositiveMass_eq_negativeMass
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) :
    tangentPositiveMass q = tangentNegativeMass q := by
  have hdiff :
      tangentPositiveMass q - tangentNegativeMass q =
        ∑ v : V, q v := by
    unfold tangentPositiveMass tangentNegativeMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _hv
    exact max_zero_sub_max_neg_zero_eq_self (q v)
  linarith

/-- The two Jordan masses add to the `ell^1` mass. -/
theorem tangentPositiveMass_add_negativeMass
    {V : Type*} [Fintype V] (q : V -> Real) :
    tangentPositiveMass q + tangentNegativeMass q =
      ∑ v : V, |q v| := by
  unfold tangentPositiveMass tangentNegativeMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  exact max_zero_add_max_neg_zero_eq_abs_self (q v)

theorem tangentBalancedProductFlow_nonneg
    {V : Type*} [Fintype V] (q : V -> Real)
    (source target : V) :
    0 <= tangentBalancedProductFlow q source target := by
  unfold tangentBalancedProductFlow
  exact div_nonneg
    (mul_nonneg (le_max_right (q source) 0)
      (le_max_right (-q target) 0))
    (tangentPositiveMass_nonneg q)





/-- If the common positive mass vanishes, every coordinate of a balanced
signed vector vanishes. -/
theorem tangentBalanced_eq_zero_of_positiveMass_eq_zero
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0)
    (hmass : tangentPositiveMass q = 0) :
    forall v, q v = 0 := by
  have hnegative : tangentNegativeMass q = 0 := by
    rw [← tangentPositiveMass_eq_negativeMass q hsum]
    exact hmass
  have hpositiveZero : (fun v ↦ max (q v) 0) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun w ↦ le_max_right (q w) 0)).mp hmass
  have hnegativeZero : (fun v ↦ max (-q v) 0) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun w ↦ le_max_right (-q w) 0)).mp hnegative
  have hpositivePoint : forall v, max (q v) 0 = 0 := by
    intro v
    exact congrFun hpositiveZero v
  have hnegativePoint : forall v, max (-q v) 0 = 0 := by
    intro v
    exact congrFun hnegativeZero v
  intro v
  have hparts := max_zero_sub_max_neg_zero_eq_self (q v)
  simpa only [hpositivePoint v, hnegativePoint v, sub_zero] using hparts.symm

/-- A row of the proportional matching is exactly the positive part of its
source coordinate. -/
theorem sum_tangentBalancedProductFlow_out
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0)
    (hmass : tangentPositiveMass q ≠ 0) (source : V) :
    (∑ target : V, tangentBalancedProductFlow q source target) =
      max (q source) 0 := by
  unfold tangentBalancedProductFlow
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change max (q source) 0 * tangentNegativeMass q /
      tangentPositiveMass q = max (q source) 0
  rw [← tangentPositiveMass_eq_negativeMass q hsum]
  field_simp [hmass]

/-- A column of the proportional matching is exactly the negative part of
its target coordinate. -/
theorem sum_tangentBalancedProductFlow_in
    {V : Type*} [Fintype V] (q : V -> Real)
    (hmass : tangentPositiveMass q ≠ 0) (target : V) :
    (∑ source : V, tangentBalancedProductFlow q source target) =
      max (-q target) 0 := by
  unfold tangentBalancedProductFlow
  rw [← Finset.sum_div, ← Finset.sum_mul]
  change tangentPositiveMass q * max (-q target) 0 /
      tangentPositiveMass q = max (-q target) 0
  field_simp [hmass]

/-- The explicit proportional matching has the requested divergence. -/
theorem tangentBalancedProductFlow_divergence_eq
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) (v : V) :
    tangentFlowDivergence (tangentBalancedProductFlow q) v = q v := by
  by_cases hmass : tangentPositiveMass q = 0
  · have hq := tangentBalanced_eq_zero_of_positiveMass_eq_zero
      q hsum hmass
    simp [tangentFlowDivergence, tangentBalancedProductFlow,
      hmass, hq v]
  · rw [tangentFlowDivergence,
      sum_tangentBalancedProductFlow_out q hsum hmass v,
      sum_tangentBalancedProductFlow_in q hmass v]
    exact max_zero_sub_max_neg_zero_eq_self (q v)

/-- Total traffic is the common positive/negative mass. -/
theorem tangentBalancedProductFlow_traffic_eq_positiveMass
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) :
    tangentFlowTraffic (tangentBalancedProductFlow q) =
      tangentPositiveMass q := by
  by_cases hmass : tangentPositiveMass q = 0
  · simp [tangentFlowTraffic, tangentBalancedProductFlow, hmass]
  · unfold tangentFlowTraffic
    simp_rw [sum_tangentBalancedProductFlow_out q hsum hmass]
    exact rfl

/-- Hence total traffic is exactly half the `ell^1` residual mass. -/
theorem tangentBalancedProductFlow_traffic_eq_half_sum_abs
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) :
    tangentFlowTraffic (tangentBalancedProductFlow q) =
      (∑ v : V, |q v|) / 2 := by
  rw [tangentBalancedProductFlow_traffic_eq_positiveMass q hsum]
  have hmass := tangentPositiveMass_eq_negativeMass q hsum
  have habs := tangentPositiveMass_add_negativeMass q
  linarith

/-- Full incoming plus outgoing traffic at a vertex is exactly the absolute
value of its signed residual. -/
theorem tangentBalancedProductFlow_incident_eq_abs
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) (v : V) :
    (∑ w : V, tangentBalancedProductFlow q v w) +
        (∑ w : V, tangentBalancedProductFlow q w v) = |q v| := by
  by_cases hmass : tangentPositiveMass q = 0
  · have hq := tangentBalanced_eq_zero_of_positiveMass_eq_zero
      q hsum hmass
    simp [tangentBalancedProductFlow, hmass, hq v]
  · rw [sum_tangentBalancedProductFlow_out q hsum hmass v,
      sum_tangentBalancedProductFlow_in q hmass v]
    exact max_zero_add_max_neg_zero_eq_abs_self (q v)



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentRatioCellEarthmover -/
section


/-!
# Explicit ratio-cell earthmover

This file implements the missing finite transport layer behind
`TangentDistributedFlowCensus`.

Inside every exponent band the occupied ratio cells are numbered
`0, ..., lastCell b`.  At the cut after cell `i` the signed prefix mass
`F_i` is spread uniformly over the complete bipartite graph joining cells
`i` and `i+1`, in the direction determined by the sign of `F_i`.  After
these boundary transports, the adjusted residual `q_p` has sum zero in
each cell.  It is transported by the canonical proportional matching from
`TangentBalancedProductFlow`.

The resulting flow is a visible formula, not a conclusion-bearing
certificate.  Its divergence, locality, traffic, and pointwise incident
estimates are theorems.  In particular, no final collision smallness bound
is assumed or stored here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Uniform cell weights and one boundary cut -/









theorem tangentRatioCellUniformWeight_nonneg
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cell : Nat) (v : V) :
    0 <= tangentRatioCellUniformWeight bandOf cellIndex band cell v := by
  unfold tangentRatioCellUniformWeight
  split_ifs <;> positivity

theorem sum_tangentRatioCellUniformWeight
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cell : Nat)
    (hcard : tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    (∑ v : V, tangentRatioCellUniformWeight
      bandOf cellIndex band cell v) = 1 := by
  classical
  unfold tangentRatioCellUniformWeight
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change
    (tangentRatioCellCard bandOf cellIndex band cell : Real) *
        (1 / tangentRatioCellCard bandOf cellIndex band cell) = 1
  field_simp [Nat.cast_ne_zero.mpr hcard]





theorem tangentRatioCellBoundaryCutFlow_nonneg
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (source target : V) :
    0 <= tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target := by
  unfold tangentRatioCellBoundaryCutFlow
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (le_max_right _ _)
        (tangentRatioCellUniformWeight_nonneg
          bandOf cellIndex band cut source))
      (tangentRatioCellUniformWeight_nonneg
        bandOf cellIndex band (cut + 1) target))
    (mul_nonneg
      (mul_nonneg (le_max_right _ _)
        (tangentRatioCellUniformWeight_nonneg
          bandOf cellIndex band (cut + 1) source))
      (tangentRatioCellUniformWeight_nonneg
        bandOf cellIndex band cut target))







theorem sum_tangentRatioCellBoundaryCutFlow_out
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0)
    (source : V) :
    (∑ target : V, tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target) =
      max (tangentRatioCellPrefixMass residual bandOf cellIndex band cut) 0 *
          tangentRatioCellUniformWeight bandOf cellIndex band cut source +
        max (-tangentRatioCellPrefixMass residual bandOf cellIndex band cut) 0 *
          tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) source := by
  unfold tangentRatioCellBoundaryCutFlow
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) hright,
    sum_tangentRatioCellUniformWeight bandOf cellIndex band cut hleft]
  ring

theorem sum_tangentRatioCellBoundaryCutFlow_in
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0)
    (target : V) :
    (∑ source : V, tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target) =
      max (tangentRatioCellPrefixMass residual bandOf cellIndex band cut) 0 *
          tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) target +
        max (-tangentRatioCellPrefixMass residual bandOf cellIndex band cut) 0 *
          tangentRatioCellUniformWeight bandOf cellIndex band cut target := by
  dsimp only [tangentRatioCellBoundaryCutFlow]
  rw [Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.mul_sum, ← Finset.mul_sum,
    sum_tangentRatioCellUniformWeight bandOf cellIndex band cut hleft,
    sum_tangentRatioCellUniformWeight
      bandOf cellIndex band (cut + 1) hright]
  ring

theorem tangentRatioCellBoundaryCutFlow_divergence
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellBoundaryCutFlow
          residual bandOf cellIndex band cut) v =
      tangentRatioCellPrefixMass residual bandOf cellIndex band cut *
        (tangentRatioCellUniformWeight bandOf cellIndex band cut v -
          tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) v) := by
  rw [tangentFlowDivergence,
    sum_tangentRatioCellBoundaryCutFlow_out
      residual bandOf cellIndex band cut hleft hright v,
    sum_tangentRatioCellBoundaryCutFlow_in
      residual bandOf cellIndex band cut hleft hright v]
  calc
    _ =
        (max (tangentRatioCellPrefixMass
            residual bandOf cellIndex band cut) 0 -
          max (-tangentRatioCellPrefixMass
            residual bandOf cellIndex band cut) 0) *
          (tangentRatioCellUniformWeight bandOf cellIndex band cut v -
            tangentRatioCellUniformWeight
              bandOf cellIndex band (cut + 1) v) := by
        ring
    _ = _ := by
      rw [max_zero_sub_max_neg_zero_eq_self]





theorem tangentRatioCellBoundaryCutFlow_traffic
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0) :
    tangentFlowTraffic
        (tangentRatioCellBoundaryCutFlow
          residual bandOf cellIndex band cut) =
      |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| := by
  unfold tangentFlowTraffic
  simp_rw [sum_tangentRatioCellBoundaryCutFlow_out
    residual bandOf cellIndex band cut hleft hright]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_tangentRatioCellUniformWeight bandOf cellIndex band cut hleft,
    sum_tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) hright]
  simpa only [mul_one] using
    max_zero_add_max_neg_zero_eq_abs_self
      (tangentRatioCellPrefixMass residual bandOf cellIndex band cut)

theorem tangentRatioCellBoundaryCutFlow_incident
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0)
    (v : V) :
    (∑ w : V, tangentRatioCellBoundaryCutFlow
        residual bandOf cellIndex band cut v w) +
      (∑ w : V, tangentRatioCellBoundaryCutFlow
        residual bandOf cellIndex band cut w v) =
      |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| *
        (tangentRatioCellUniformWeight bandOf cellIndex band cut v +
          tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) v) := by
  rw [sum_tangentRatioCellBoundaryCutFlow_out
      residual bandOf cellIndex band cut hleft hright v,
    sum_tangentRatioCellBoundaryCutFlow_in
      residual bandOf cellIndex band cut hleft hright v,
    ← max_zero_add_max_neg_zero_eq_abs_self
      (tangentRatioCellPrefixMass residual bandOf cellIndex band cut)]
  ring

/-! ## Finite-sum linearity for flows -/

theorem tangentFlowDivergence_finset_sum
    {V I : Type*} [Fintype V] (indices : Finset I)
    (flow : I -> V -> V -> Real) (v : V) :
    tangentFlowDivergence
        (fun source target => ∑ i ∈ indices, flow i source target) v =
      ∑ i ∈ indices, tangentFlowDivergence (flow i) v := by
  unfold tangentFlowDivergence
  have hout :
      (∑ w : V, ∑ i ∈ indices, flow i v w) =
        ∑ i ∈ indices, ∑ w : V, flow i v w := by
    exact Finset.sum_comm
  have hin :
      (∑ w : V, ∑ i ∈ indices, flow i w v) =
        ∑ i ∈ indices, ∑ w : V, flow i w v := by
    exact Finset.sum_comm
  rw [hout, hin]
  rw [← Finset.sum_sub_distrib]

theorem tangentFlowTraffic_finset_sum
    {V I : Type*} [Fintype V] (indices : Finset I)
    (flow : I -> V -> V -> Real) :
    tangentFlowTraffic
        (fun source target => ∑ i ∈ indices, flow i source target) =
      ∑ i ∈ indices, tangentFlowTraffic (flow i) := by
  unfold tangentFlowTraffic
  calc
    (∑ source : V, ∑ target : V,
        ∑ i ∈ indices, flow i source target) =
        ∑ source : V, ∑ i ∈ indices,
          ∑ target : V, flow i source target := by
      apply Finset.sum_congr rfl
      intro source _hsource
      exact Finset.sum_comm
    _ = ∑ i ∈ indices, ∑ source : V,
          ∑ target : V, flow i source target := by
      exact Finset.sum_comm

theorem tangentVertexIncident_finset_sum
    {V I : Type*} [Fintype V] (indices : Finset I)
    (flow : I -> V -> V -> Real) (v : V) :
    (∑ w : V, ∑ i ∈ indices, flow i v w) +
        (∑ w : V, ∑ i ∈ indices, flow i w v) =
      ∑ i ∈ indices,
        ((∑ w : V, flow i v w) + ∑ w : V, flow i w v) := by
  have hout :
      (∑ w : V, ∑ i ∈ indices, flow i v w) =
        ∑ i ∈ indices, ∑ w : V, flow i v w := by
    exact Finset.sum_comm
  have hin :
      (∑ w : V, ∑ i ∈ indices, flow i w v) =
        ∑ i ∈ indices, ∑ w : V, flow i w v := by
    exact Finset.sum_comm
  rw [hout, hin, ← Finset.sum_add_distrib]

/-! ## All canonical cuts in one finite band family -/





theorem tangentRatioCellBoundaryFlow_nonneg
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) :
    0 <= tangentRatioCellBoundaryFlow
      lastCell residual bandOf cellIndex source target := by
  unfold tangentRatioCellBoundaryFlow
  exact Finset.sum_nonneg fun band _hband =>
    Finset.sum_nonneg fun cut _hcut =>
      tangentRatioCellBoundaryCutFlow_nonneg
        residual bandOf cellIndex band cut source target



/-! ## Prefix algebra and exact boundary divergence -/

/-- At the final cell of a band, the prefix is the full band sum. -/
theorem tangentRatioCellPrefixMass_lastCell
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (band : Band) :
    tangentRatioCellPrefixMass residual bandOf cellIndex
        band (lastCell band) =
      ∑ v : V, if bandOf v = band then residual v else 0 := by
  unfold tangentRatioCellPrefixMass
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hv : bandOf v = band
  · have hle : cellIndex v <= lastCell band := by
      simpa only [hv] using hindex v
    simp [hv, hle]
  · simp [hv]

/-- The residual mass of cell `i` is the difference of its right and left
prefixes. -/
theorem sum_tangentRatioCell_eq_prefix_sub_left
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cell : Nat) :
    (∑ v : V,
        if bandOf v = band ∧ cellIndex v = cell then residual v else 0) =
      tangentRatioCellPrefixMass residual bandOf cellIndex band cell -
        (if cell = 0 then 0 else
          tangentRatioCellPrefixMass residual bandOf cellIndex
            band (cell - 1)) := by
  cases cell with
  | zero =>
      unfold tangentRatioCellPrefixMass
      simp
  | succ cell =>
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      unfold tangentRatioCellPrefixMass
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hband : bandOf v = band
      · simp only [hband, true_and]
        by_cases hlePrevious : cellIndex v <= cell
        · have hsucc : cellIndex v <= cell + 1 := by omega
          have hne : cellIndex v ≠ cell + 1 := by omega
          simp [hsucc, hlePrevious, hne]
        · by_cases hsucc : cellIndex v <= cell + 1
          · have heq : cellIndex v = cell + 1 := by omega
            simp [heq]
          · have hne : cellIndex v ≠ cell + 1 := by omega
            simp [hsucc, hlePrevious, hne]
      · simp [hband]

theorem tangentRatioCellBoundaryFlow_divergence_cutSum
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellBoundaryFlow
          lastCell residual bandOf cellIndex) v =
      ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellPrefixMass residual bandOf cellIndex band cut *
          (tangentRatioCellUniformWeight bandOf cellIndex band cut v -
            tangentRatioCellUniformWeight bandOf cellIndex
              band (cut + 1) v) := by
  unfold tangentRatioCellBoundaryFlow
  rw [tangentFlowDivergence_finset_sum]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentFlowDivergence_finset_sum]
  apply Finset.sum_congr rfl
  intro cut hcut
  have hcutlt : cut < lastCell band := Finset.mem_range.mp hcut
  rw [tangentRatioCellBoundaryCutFlow_divergence
    residual bandOf cellIndex band cut
      (hoccupied band cut (by omega))
      (hoccupied band (cut + 1) (by omega)) v]

/-- Only the cut immediately to the right of `v` contributes its left-port
weight; at a terminal cell its prefix is zero by band balance. -/
theorem sum_prefix_mul_leftUniformWeight
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    (∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellPrefixMass residual bandOf cellIndex band cut *
          tangentRatioCellUniformWeight bandOf cellIndex band cut v) =
      tangentRatioCellPrefixMass residual bandOf cellIndex
          (bandOf v) (cellIndex v) /
        tangentRatioCellCard bandOf cellIndex
          (bandOf v) (cellIndex v) := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · have hle := hindex v
    by_cases hlt : cellIndex v < lastCell (bandOf v)
    · rw [Finset.sum_eq_single (cellIndex v)]
      · simp [tangentRatioCellUniformWeight, div_eq_mul_inv]
      · intro cut hcut hne
        have hcell : cellIndex v ≠ cut := Ne.symm hne
        simp [tangentRatioCellUniformWeight, hcell]
      · intro hnotmem
        exact (hnotmem (Finset.mem_range.mpr hlt)).elim
    · have heq : cellIndex v = lastCell (bandOf v) := by omega
      have hprefix :
          tangentRatioCellPrefixMass residual bandOf cellIndex
              (bandOf v) (cellIndex v) = 0 := by
        rw [heq, tangentRatioCellPrefixMass_lastCell
          lastCell residual bandOf cellIndex hindex]
        exact hbalance (bandOf v)
      rw [hprefix, zero_div]
      apply Finset.sum_eq_zero
      intro cut hcut
      have hcutlt := Finset.mem_range.mp hcut
      have hne : cellIndex v ≠ cut := by omega
      simp [tangentRatioCellUniformWeight, hne]
  · intro band hband
    apply Finset.sum_eq_zero
    intro cut hcut
    have hne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellUniformWeight, hne]

/-- Only the cut immediately to the left of `v` contributes its right-port
weight. -/
theorem sum_prefix_mul_rightUniformWeight
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (v : V) :
    (∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellPrefixMass residual bandOf cellIndex band cut *
          tangentRatioCellUniformWeight bandOf cellIndex
            band (cut + 1) v) =
      tangentRatioCellLeftPrefixMass residual bandOf cellIndex v /
        tangentRatioCellCard bandOf cellIndex
          (bandOf v) (cellIndex v) := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · cases hcell : cellIndex v with
    | zero =>
        rw [show tangentRatioCellLeftPrefixMass
            residual bandOf cellIndex v = 0 by
          simp [tangentRatioCellLeftPrefixMass, hcell], zero_div]
        apply Finset.sum_eq_zero
        intro cut hcut
        have hne : cellIndex v ≠ cut + 1 := by omega
        simp [tangentRatioCellUniformWeight, hne]
    | succ previous =>
        have hprevlt : previous < lastCell (bandOf v) := by
          have hle := hindex v
          omega
        rw [Finset.sum_eq_single previous]
        · simp [tangentRatioCellUniformWeight,
            tangentRatioCellLeftPrefixMass, hcell, div_eq_mul_inv]
        · intro cut hcut hne
          have hcellne : cellIndex v ≠ cut + 1 := by omega
          simp [tangentRatioCellUniformWeight, hcellne]
        · intro hnotmem
          exact (hnotmem (Finset.mem_range.mpr hprevlt)).elim
  · intro band hband
    apply Finset.sum_eq_zero
    intro cut hcut
    have hne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellUniformWeight, hne]

/-- The sum of the uniform cut divergences is exactly the previously
declared boundary-divergence formula. -/
theorem tangentRatioCellBoundaryFlow_divergence_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellBoundaryFlow
          lastCell residual bandOf cellIndex) v =
      tangentRatioCellBoundaryDivergence
        residual bandOf cellIndex v := by
  rw [tangentRatioCellBoundaryFlow_divergence_cutSum
      lastCell residual bandOf cellIndex hoccupied v]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [sum_prefix_mul_leftUniformWeight
      lastCell residual bandOf cellIndex hindex hbalance v,
    sum_prefix_mul_rightUniformWeight
      lastCell residual bandOf cellIndex hindex v]
  unfold tangentRatioCellBoundaryDivergence
  ring

theorem tangentRatioCellBoundaryFlow_traffic_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    tangentFlowTraffic
        (tangentRatioCellBoundaryFlow
          lastCell residual bandOf cellIndex) =
      tangentRatioCellCanonicalCutTraffic
        lastCell residual bandOf cellIndex := by
  unfold tangentRatioCellBoundaryFlow tangentRatioCellCanonicalCutTraffic
  rw [tangentFlowTraffic_finset_sum]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentFlowTraffic_finset_sum]
  apply Finset.sum_congr rfl
  intro cut hcut
  have hcutlt := Finset.mem_range.mp hcut
  exact tangentRatioCellBoundaryCutFlow_traffic
    residual bandOf cellIndex band cut
      (hoccupied band cut (by omega))
      (hoccupied band (cut + 1) (by omega))

theorem tangentRatioCellBoundaryFlow_incident_cutSum
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    (∑ w : V, tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex w v) =
      ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| *
          (tangentRatioCellUniformWeight bandOf cellIndex band cut v +
            tangentRatioCellUniformWeight bandOf cellIndex
              band (cut + 1) v) := by
  unfold tangentRatioCellBoundaryFlow
  rw [tangentVertexIncident_finset_sum
    (Finset.univ : Finset Band)
    (fun band source target =>
      ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellBoundaryCutFlow residual bandOf cellIndex
          band cut source target) v]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentVertexIncident_finset_sum
    (Finset.range (lastCell band))
    (fun cut source target =>
      tangentRatioCellBoundaryCutFlow residual bandOf cellIndex
        band cut source target) v]
  apply Finset.sum_congr rfl
  intro cut hcut
  have hcutlt := Finset.mem_range.mp hcut
  exact tangentRatioCellBoundaryCutFlow_incident
    residual bandOf cellIndex band cut
      (hoccupied band cut (by omega))
      (hoccupied band (cut + 1) (by omega)) v

theorem sum_abs_prefix_mul_leftUniformWeight
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    (∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| *
          tangentRatioCellUniformWeight bandOf cellIndex band cut v) =
      |tangentRatioCellPrefixMass residual bandOf cellIndex
          (bandOf v) (cellIndex v)| /
        tangentRatioCellCard bandOf cellIndex
          (bandOf v) (cellIndex v) := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · have hle := hindex v
    by_cases hlt : cellIndex v < lastCell (bandOf v)
    · rw [Finset.sum_eq_single (cellIndex v)]
      · simp [tangentRatioCellUniformWeight, div_eq_mul_inv]
      · intro cut hcut hne
        have hcell : cellIndex v ≠ cut := Ne.symm hne
        simp [tangentRatioCellUniformWeight, hcell]
      · intro hnotmem
        exact (hnotmem (Finset.mem_range.mpr hlt)).elim
    · have heq : cellIndex v = lastCell (bandOf v) := by omega
      have hprefix :
          tangentRatioCellPrefixMass residual bandOf cellIndex
              (bandOf v) (cellIndex v) = 0 := by
        rw [heq, tangentRatioCellPrefixMass_lastCell
          lastCell residual bandOf cellIndex hindex]
        exact hbalance (bandOf v)
      rw [hprefix, abs_zero, zero_div]
      apply Finset.sum_eq_zero
      intro cut hcut
      have hcutlt := Finset.mem_range.mp hcut
      have hne : cellIndex v ≠ cut := by omega
      simp [tangentRatioCellUniformWeight, hne]
  · intro band hband
    apply Finset.sum_eq_zero
    intro cut hcut
    have hne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellUniformWeight, hne]

theorem sum_abs_prefix_mul_rightUniformWeight
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (v : V) :
    (∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| *
          tangentRatioCellUniformWeight bandOf cellIndex
            band (cut + 1) v) =
      |tangentRatioCellLeftPrefixMass residual bandOf cellIndex v| /
        tangentRatioCellCard bandOf cellIndex
          (bandOf v) (cellIndex v) := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · cases hcell : cellIndex v with
    | zero =>
        rw [show tangentRatioCellLeftPrefixMass
            residual bandOf cellIndex v = 0 by
          simp [tangentRatioCellLeftPrefixMass, hcell], abs_zero, zero_div]
        apply Finset.sum_eq_zero
        intro cut hcut
        have hne : cellIndex v ≠ cut + 1 := by omega
        simp [tangentRatioCellUniformWeight, hne]
    | succ previous =>
        have hprevlt : previous < lastCell (bandOf v) := by
          have hle := hindex v
          omega
        rw [Finset.sum_eq_single previous]
        · simp [tangentRatioCellUniformWeight,
            tangentRatioCellLeftPrefixMass, hcell, div_eq_mul_inv]
        · intro cut hcut hne
          have hcellne : cellIndex v ≠ cut + 1 := by omega
          simp [tangentRatioCellUniformWeight, hcellne]
        · intro hnotmem
          exact (hnotmem (Finset.mem_range.mpr hprevlt)).elim
  · intro band hband
    apply Finset.sum_eq_zero
    intro cut hcut
    have hne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellUniformWeight, hne]

/-- Boundary traffic incident to a vertex is exactly its declared uniform
two-port load. -/
theorem tangentRatioCellBoundaryFlow_incident_eq_portLoad
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    (∑ w : V, tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex w v) =
      tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  rw [tangentRatioCellBoundaryFlow_incident_cutSum
      lastCell residual bandOf cellIndex hoccupied v]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [sum_abs_prefix_mul_leftUniformWeight
      lastCell residual bandOf cellIndex hindex hbalance v,
    sum_abs_prefix_mul_rightUniformWeight
      lastCell residual bandOf cellIndex hindex v]
  unfold tangentRatioCellUniformPortLoad
  ring

/-! ## The balanced residual inside each cell -/





theorem tangentRatioCellInternalFlow_nonneg
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) :
    0 <= tangentRatioCellInternalFlow
      lastCell residual bandOf cellIndex source target := by
  unfold tangentRatioCellInternalFlow
  exact Finset.sum_nonneg fun band _hband =>
    Finset.sum_nonneg fun cell _hcell =>
      tangentBalancedProductFlow_nonneg
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target



/-- Summing the uniform boundary divergence over one cell recovers the
difference of its two prefix masses. -/
theorem sum_tangentRatioCellBoundaryDivergence_eq_prefix_sub_left
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cell : Nat)
    (hcard : tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    (∑ v : V,
        if bandOf v = band ∧ cellIndex v = cell then
          tangentRatioCellBoundaryDivergence residual bandOf cellIndex v
        else 0) =
      tangentRatioCellPrefixMass residual bandOf cellIndex band cell -
        (if cell = 0 then 0 else
          tangentRatioCellPrefixMass residual bandOf cellIndex
            band (cell - 1)) := by
  classical
  rw [← Finset.sum_filter]
  let numerator :=
    tangentRatioCellPrefixMass residual bandOf cellIndex band cell -
      (if cell = 0 then 0 else
        tangentRatioCellPrefixMass residual bandOf cellIndex
          band (cell - 1))
  calc
    (∑ v ∈ (Finset.univ : Finset V).filter
        (fun v => bandOf v = band ∧ cellIndex v = cell),
        tangentRatioCellBoundaryDivergence residual bandOf cellIndex v) =
        ∑ _v ∈ (Finset.univ : Finset V).filter
          (fun v => bandOf v = band ∧ cellIndex v = cell),
            numerator / tangentRatioCellCard bandOf cellIndex band cell := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvdata := (Finset.mem_filter.mp hv).2
      rcases hvdata with ⟨hvband, hvcell⟩
      simp [tangentRatioCellBoundaryDivergence,
        tangentRatioCellLeftPrefixMass, hvband, hvcell, numerator]
    _ = (tangentRatioCellCard bandOf cellIndex band cell : Real) *
          (numerator / tangentRatioCellCard bandOf cellIndex band cell) := by
      simp [tangentRatioCellCard, Finset.sum_const, nsmul_eq_mul]
    _ = numerator := by
      field_simp [Nat.cast_ne_zero.mpr hcard]

/-- After removing the boundary divergence, each cell has zero internal
residual. -/
theorem sum_tangentRatioCellMaskedInternalResidual_eq_zero
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (band : Band) (cell : Nat) (hcell : cell <= lastCell band) :
    (∑ v : V, tangentRatioCellMaskedInternalResidual
      residual bandOf cellIndex band cell v) = 0 := by
  calc
    (∑ v : V, tangentRatioCellMaskedInternalResidual
        residual bandOf cellIndex band cell v) =
        (∑ v : V,
          if bandOf v = band ∧ cellIndex v = cell then residual v else 0) -
        ∑ v : V,
          if bandOf v = band ∧ cellIndex v = cell then
            tangentRatioCellBoundaryDivergence residual bandOf cellIndex v
          else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hv : bandOf v = band ∧ cellIndex v = cell
      · simp [tangentRatioCellMaskedInternalResidual,
          tangentRatioCellInternalResidual, hv]
      · simp [tangentRatioCellMaskedInternalResidual, hv]
    _ = 0 := by
      rw [sum_tangentRatioCell_eq_prefix_sub_left,
        sum_tangentRatioCellBoundaryDivergence_eq_prefix_sub_left
          residual bandOf cellIndex band cell
            (hoccupied band cell hcell)]
      ring

/-- The cell sum of product-flow divergences is the masked internal
residual itself. -/
theorem tangentRatioCellInternalFlow_divergence_cutSum
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex) v =
      ∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell v := by
  unfold tangentRatioCellInternalFlow
  rw [tangentFlowDivergence_finset_sum]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentFlowDivergence_finset_sum]
  apply Finset.sum_congr rfl
  intro cell hcell
  have hcellle : cell <= lastCell band := by
    have := Finset.mem_range.mp hcell
    omega
  exact tangentBalancedProductFlow_divergence_eq
    (tangentRatioCellMaskedInternalResidual
      residual bandOf cellIndex band cell)
    (sum_tangentRatioCellMaskedInternalResidual_eq_zero
      lastCell residual bandOf cellIndex hoccupied band cell hcellle) v

theorem sum_tangentRatioCellMaskedInternalResidual_at_vertex
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (v : V) :
    (∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell v) =
      tangentRatioCellInternalResidual residual bandOf cellIndex v := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · rw [Finset.sum_eq_single (cellIndex v)]
    · simp [tangentRatioCellMaskedInternalResidual]
    · intro cell hcell hne
      have hcellne : cellIndex v ≠ cell := Ne.symm hne
      simp [tangentRatioCellMaskedInternalResidual, hcellne]
    · intro hnotmem
      exact (hnotmem (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (hindex v)))).elim
  · intro band hband
    apply Finset.sum_eq_zero
    intro cell hcell
    have hbandne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellMaskedInternalResidual, hbandne]

theorem tangentRatioCellInternalFlow_divergence_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex) v =
      tangentRatioCellInternalResidual residual bandOf cellIndex v := by
  rw [tangentRatioCellInternalFlow_divergence_cutSum
      lastCell residual bandOf cellIndex hoccupied v,
    sum_tangentRatioCellMaskedInternalResidual_at_vertex
      lastCell residual bandOf cellIndex hindex v]

theorem tangentRatioCellInternalFlow_incident_cutSum
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    (∑ w : V, tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex w v) =
      ∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        |tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell v| := by
  unfold tangentRatioCellInternalFlow
  rw [tangentVertexIncident_finset_sum
    (Finset.univ : Finset Band)
    (fun band source target =>
      ∑ cell ∈ Finset.range (lastCell band + 1),
        tangentBalancedProductFlow
          (tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell) source target) v]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentVertexIncident_finset_sum
    (Finset.range (lastCell band + 1))
    (fun cell source target =>
      tangentBalancedProductFlow
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target) v]
  apply Finset.sum_congr rfl
  intro cell hcell
  have hcellle : cell <= lastCell band := by
    have := Finset.mem_range.mp hcell
    omega
  exact tangentBalancedProductFlow_incident_eq_abs
    (tangentRatioCellMaskedInternalResidual
      residual bandOf cellIndex band cell)
    (sum_tangentRatioCellMaskedInternalResidual_eq_zero
      lastCell residual bandOf cellIndex hoccupied band cell hcellle) v

theorem sum_abs_tangentRatioCellMaskedInternalResidual_at_vertex
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (v : V) :
    (∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        |tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell v|) =
      |tangentRatioCellInternalResidual residual bandOf cellIndex v| := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · rw [Finset.sum_eq_single (cellIndex v)]
    · simp [tangentRatioCellMaskedInternalResidual]
    · intro cell hcell hne
      have hcellne : cellIndex v ≠ cell := Ne.symm hne
      simp [tangentRatioCellMaskedInternalResidual, hcellne]
    · intro hnotmem
      exact (hnotmem (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (hindex v)))).elim
  · intro band hband
    apply Finset.sum_eq_zero
    intro cell hcell
    have hbandne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellMaskedInternalResidual, hbandne]

/-- Internal incident traffic is exactly `|q_p|`. -/
theorem tangentRatioCellInternalFlow_incident_eq_abs
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    (∑ w : V, tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex w v) =
      |tangentRatioCellInternalResidual residual bandOf cellIndex v| := by
  rw [tangentRatioCellInternalFlow_incident_cutSum
      lastCell residual bandOf cellIndex hoccupied v,
    sum_abs_tangentRatioCellMaskedInternalResidual_at_vertex
      lastCell residual bandOf cellIndex hindex v]

theorem tangentRatioCellInternalFlow_traffic_cutSum
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    tangentFlowTraffic
        (tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex) =
      ∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        (∑ v : V,
          |tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell v|) / 2 := by
  unfold tangentRatioCellInternalFlow
  rw [tangentFlowTraffic_finset_sum]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentFlowTraffic_finset_sum]
  apply Finset.sum_congr rfl
  intro cell hcell
  have hcellle : cell <= lastCell band := by
    have := Finset.mem_range.mp hcell
    omega
  exact tangentBalancedProductFlow_traffic_eq_half_sum_abs
    (tangentRatioCellMaskedInternalResidual
      residual bandOf cellIndex band cell)
    (sum_tangentRatioCellMaskedInternalResidual_eq_zero
      lastCell residual bandOf cellIndex hoccupied band cell hcellle)

theorem sum_abs_tangentRatioCellMaskedInternalResidual_partition
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v)) :
    (∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        ∑ v : V,
          |tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell v|) =
      ∑ v : V,
        |tangentRatioCellInternalResidual residual bandOf cellIndex v| := by
  calc
    (∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        ∑ v : V,
          |tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell v|) =
        ∑ band : Band, ∑ v : V,
          ∑ cell ∈ Finset.range (lastCell band + 1),
            |tangentRatioCellMaskedInternalResidual
              residual bandOf cellIndex band cell v| := by
      apply Finset.sum_congr rfl
      intro band _hband
      exact Finset.sum_comm
    _ = ∑ v : V, ∑ band : Band,
          ∑ cell ∈ Finset.range (lastCell band + 1),
            |tangentRatioCellMaskedInternalResidual
              residual bandOf cellIndex band cell v| := by
      exact Finset.sum_comm
    _ = ∑ v : V,
          |tangentRatioCellInternalResidual residual bandOf cellIndex v| := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact sum_abs_tangentRatioCellMaskedInternalResidual_at_vertex
        lastCell residual bandOf cellIndex hindex v

/-- Internal traffic is exactly half the global `ell^1` mass of `q`. -/
theorem tangentRatioCellInternalFlow_traffic_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    tangentFlowTraffic
        (tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex) =
      (∑ v : V,
        |tangentRatioCellInternalResidual residual bandOf cellIndex v|) / 2 := by
  rw [tangentRatioCellInternalFlow_traffic_cutSum
      lastCell residual bandOf cellIndex hoccupied]
  calc
    (∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        (∑ v : V,
          |tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell v|) / 2) =
        ∑ band : Band,
          (∑ cell ∈ Finset.range (lastCell band + 1),
            ∑ v : V,
              |tangentRatioCellMaskedInternalResidual
                residual bandOf cellIndex band cell v|) / 2 := by
      apply Finset.sum_congr rfl
      intro band _hband
      exact (Finset.sum_div
        (Finset.range (lastCell band + 1))
        (fun cell => ∑ v : V,
          |tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell v|) 2).symm
    _ = (∑ band : Band,
          ∑ cell ∈ Finset.range (lastCell band + 1),
            ∑ v : V,
              |tangentRatioCellMaskedInternalResidual
                residual bandOf cellIndex band cell v|) / 2 := by
      exact (Finset.sum_div (Finset.univ : Finset Band)
        (fun band =>
          ∑ cell ∈ Finset.range (lastCell band + 1),
            ∑ v : V,
              |tangentRatioCellMaskedInternalResidual
                residual bandOf cellIndex band cell v|) 2).symm
    _ = (∑ v : V,
          |tangentRatioCellInternalResidual residual bandOf cellIndex v|) /
        2 := by
      rw [sum_abs_tangentRatioCellMaskedInternalResidual_partition
        lastCell residual bandOf cellIndex hindex]

/-! ## Support locality -/

theorem tangentRatioCellBoundaryCutFlow_positive_cells
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    {source target : V}
    (hflow : 0 < tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target) :
    ((bandOf source = band ∧ cellIndex source = cut) ∧
        (bandOf target = band ∧ cellIndex target = cut + 1)) ∨
      ((bandOf source = band ∧ cellIndex source = cut + 1) ∧
        (bandOf target = band ∧ cellIndex target = cut)) := by
  by_cases hsourceLeft : bandOf source = band ∧ cellIndex source = cut
  · by_cases htargetRight :
        bandOf target = band ∧ cellIndex target = cut + 1
    · exact Or.inl ⟨hsourceLeft, htargetRight⟩
    · have hsourceRight :
          ¬(bandOf source = band ∧ cellIndex source = cut + 1) := by
        intro h
        omega
      simp [tangentRatioCellBoundaryCutFlow,
        tangentRatioCellUniformWeight, htargetRight, hsourceRight] at hflow
  · by_cases hsourceRight :
        bandOf source = band ∧ cellIndex source = cut + 1
    · by_cases htargetLeft :
          bandOf target = band ∧ cellIndex target = cut
      · exact Or.inr ⟨hsourceRight, htargetLeft⟩
      · simp [tangentRatioCellBoundaryCutFlow,
          tangentRatioCellUniformWeight, hsourceLeft, htargetLeft] at hflow
    · simp [tangentRatioCellBoundaryCutFlow,
        tangentRatioCellUniformWeight, hsourceLeft, hsourceRight] at hflow

theorem tangentRatioCellBoundaryCutFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    {source target : V}
    (hflow : 0 < tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target) :
    TangentSameOrAdjacentRatioCell bandOf cellIndex source target := by
  rcases tangentRatioCellBoundaryCutFlow_positive_cells
      residual bandOf cellIndex band cut hflow with hforward | hbackward
  · rcases hforward with ⟨⟨hsband, hscell⟩, ⟨htband, htcell⟩⟩
    exact ⟨hsband.trans htband.symm, Or.inr (Or.inl (by omega))⟩
  · rcases hbackward with ⟨⟨hsband, hscell⟩, ⟨htband, htcell⟩⟩
    exact ⟨hsband.trans htband.symm, Or.inr (Or.inr (by omega))⟩

theorem tangentRatioCellBoundaryFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) :
    TangentFlowRespectsRatioCells bandOf cellIndex
      (tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex) := by
  intro source target hflow
  unfold tangentRatioCellBoundaryFlow at hflow
  have houterNonneg : forall band : Band,
      0 <= ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellBoundaryCutFlow
          residual bandOf cellIndex band cut source target := by
    intro band
    exact Finset.sum_nonneg fun cut _hcut =>
      tangentRatioCellBoundaryCutFlow_nonneg
        residual bandOf cellIndex band cut source target
  obtain ⟨band, _hband, hbandPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun band _hband => houterNonneg band)).mp hflow
  obtain ⟨cut, hcut, hcutPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun cut _hcut => tangentRatioCellBoundaryCutFlow_nonneg
        residual bandOf cellIndex band cut source target)).mp hbandPos
  exact tangentRatioCellBoundaryCutFlow_respectsRatioCells
    residual bandOf cellIndex band cut hcutPos

theorem tangentBalancedProductFlow_masked_positive_cells
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cell : Nat)
    {source target : V}
    (hflow : 0 < tangentBalancedProductFlow
      (tangentRatioCellMaskedInternalResidual
        residual bandOf cellIndex band cell) source target) :
    (bandOf source = band ∧ cellIndex source = cell) ∧
      (bandOf target = band ∧ cellIndex target = cell) := by
  by_cases hsource : bandOf source = band ∧ cellIndex source = cell
  · by_cases htarget : bandOf target = band ∧ cellIndex target = cell
    · exact ⟨hsource, htarget⟩
    · simp [tangentBalancedProductFlow,
        tangentRatioCellMaskedInternalResidual, htarget] at hflow
  · simp [tangentBalancedProductFlow,
      tangentRatioCellMaskedInternalResidual, hsource] at hflow

theorem tangentRatioCellInternalFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) :
    TangentFlowRespectsRatioCells bandOf cellIndex
      (tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex) := by
  intro source target hflow
  unfold tangentRatioCellInternalFlow at hflow
  have houterNonneg : forall band : Band,
      0 <= ∑ cell ∈ Finset.range (lastCell band + 1),
        tangentBalancedProductFlow
          (tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell) source target := by
    intro band
    exact Finset.sum_nonneg fun cell _hcell =>
      tangentBalancedProductFlow_nonneg
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target
  obtain ⟨band, _hband, hbandPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun band _hband => houterNonneg band)).mp hflow
  obtain ⟨cell, hcell, hcellPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun cell _hcell => tangentBalancedProductFlow_nonneg
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target)).mp hbandPos
  rcases tangentBalancedProductFlow_masked_positive_cells
      residual bandOf cellIndex band cell hcellPos with
    ⟨⟨hsband, hscell⟩, ⟨htband, htcell⟩⟩
  exact ⟨hsband.trans htband.symm, Or.inl (hscell.trans htcell.symm)⟩

/-! ## The complete explicit earthmover -/



theorem tangentFlowDivergence_add
    {V : Type*} [Fintype V] (flow₁ flow₂ : V -> V -> Real) (v : V) :
    tangentFlowDivergence
        (fun source target => flow₁ source target + flow₂ source target) v =
      tangentFlowDivergence flow₁ v + tangentFlowDivergence flow₂ v := by
  unfold tangentFlowDivergence
  simp_rw [Finset.sum_add_distrib]
  ring

theorem tangentFlowTraffic_add
    {V : Type*} [Fintype V] (flow₁ flow₂ : V -> V -> Real) :
    tangentFlowTraffic
        (fun source target => flow₁ source target + flow₂ source target) =
      tangentFlowTraffic flow₁ + tangentFlowTraffic flow₂ := by
  unfold tangentFlowTraffic
  simp_rw [Finset.sum_add_distrib]

theorem tangentVertexIncident_add
    {V : Type*} [Fintype V] (flow₁ flow₂ : V -> V -> Real) (v : V) :
    (∑ u : V, (flow₁ v u + flow₂ v u)) +
        (∑ u : V, (flow₁ u v + flow₂ u v)) =
      ((∑ u : V, flow₁ v u) + ∑ u : V, flow₁ u v) +
        ((∑ u : V, flow₂ v u) + ∑ u : V, flow₂ u v) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem tangentRatioCellEarthmoverFlow_nonneg
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) :
    0 <= tangentRatioCellEarthmoverFlow
      lastCell residual bandOf cellIndex source target := by
  unfold tangentRatioCellEarthmoverFlow
  exact add_nonneg
    (tangentRatioCellBoundaryFlow_nonneg
      lastCell residual bandOf cellIndex source target)
    (tangentRatioCellInternalFlow_nonneg
      lastCell residual bandOf cellIndex source target)



theorem tangentRatioCellEarthmoverFlow_positive_endpoints_ne
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    {source target : V}
    (hflow : 0 < tangentRatioCellEarthmoverFlow
      lastCell residual bandOf cellIndex source target) :
    source ≠ target := by
  intro hst
  subst target
  rw [tangentRatioCellEarthmoverFlow_self] at hflow
  exact (lt_irrefl 0 hflow).elim

theorem tangentRatioCellEarthmoverFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) :
    TangentFlowRespectsRatioCells bandOf cellIndex
      (tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex) := by
  intro source target hflow
  have hboundaryNonneg := tangentRatioCellBoundaryFlow_nonneg
    lastCell residual bandOf cellIndex source target
  have hinternalNonneg := tangentRatioCellInternalFlow_nonneg
    lastCell residual bandOf cellIndex source target
  unfold tangentRatioCellEarthmoverFlow at hflow
  by_cases hboundary :
      0 < tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex source target
  · exact tangentRatioCellBoundaryFlow_respectsRatioCells
      lastCell residual bandOf cellIndex hboundary
  · have hinternal :
        0 < tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex source target := by
      have hboundaryZero :
          tangentRatioCellBoundaryFlow
            lastCell residual bandOf cellIndex source target = 0 :=
        le_antisymm (le_of_not_gt hboundary) hboundaryNonneg
      linarith
    exact tangentRatioCellInternalFlow_respectsRatioCells
      lastCell residual bandOf cellIndex hinternal

/-- The complete earthmover has divergence exactly the original residual. -/
theorem tangentRatioCellEarthmoverFlow_divergence_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex) v = residual v := by
  unfold tangentRatioCellEarthmoverFlow
  rw [tangentFlowDivergence_add,
    tangentRatioCellBoundaryFlow_divergence_eq
      lastCell residual bandOf cellIndex hindex hoccupied hbalance v,
    tangentRatioCellInternalFlow_divergence_eq
      lastCell residual bandOf cellIndex hindex hoccupied v]
  unfold tangentRatioCellInternalResidual
  ring

/-- The full incoming-plus-outgoing mass of the complete earthmover is the
sum of the boundary port load and `|q_p|`. -/
theorem tangentRatioCellEarthmoverFlow_incident_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    (∑ w : V, tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex w v) =
      tangentRatioCellUniformPortLoad residual bandOf cellIndex v +
        |tangentRatioCellInternalResidual residual bandOf cellIndex v| := by
  unfold tangentRatioCellEarthmoverFlow
  rw [tangentVertexIncident_add,
    tangentRatioCellBoundaryFlow_incident_eq_portLoad
      lastCell residual bandOf cellIndex hindex hoccupied hbalance v,
    tangentRatioCellInternalFlow_incident_eq_abs
      lastCell residual bandOf cellIndex hindex hoccupied v]

/-- Pointwise endpoint ledger required by the collision census. -/
theorem tangentRatioCellEarthmoverFlow_incident_le
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    (∑ w : V, tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex w v) <=
      |residual v| +
        2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  rw [tangentRatioCellEarthmoverFlow_incident_eq
      lastCell residual bandOf cellIndex hindex hoccupied hbalance v]
  simpa only [add_comm] using
    abs_internalResidual_add_portLoad_le residual bandOf cellIndex v

theorem sum_tangentVertexIncident_eq_two_traffic
    {V : Type*} [Fintype V] (flow : V -> V -> Real) :
    (∑ v : V,
        ((∑ w : V, flow v w) + ∑ w : V, flow w v)) =
      2 * tangentFlowTraffic flow := by
  unfold tangentFlowTraffic
  have hin :
      (∑ v : V, ∑ w : V, flow w v) =
        ∑ v : V, ∑ w : V, flow v w := by
    exact Finset.sum_comm
  rw [Finset.sum_add_distrib, hin]
  ring

/-- Globally, the uniform port loads count both endpoints of every cut. -/
theorem sum_tangentRatioCellUniformPortLoad_eq_two_cutTraffic
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0) :
    (∑ v : V,
        tangentRatioCellUniformPortLoad residual bandOf cellIndex v) =
      2 * tangentRatioCellCanonicalCutTraffic
        lastCell residual bandOf cellIndex := by
  calc
    (∑ v : V,
        tangentRatioCellUniformPortLoad residual bandOf cellIndex v) =
        ∑ v : V,
          ((∑ w : V, tangentRatioCellBoundaryFlow
              lastCell residual bandOf cellIndex v w) +
            ∑ w : V, tangentRatioCellBoundaryFlow
              lastCell residual bandOf cellIndex w v) := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [tangentRatioCellBoundaryFlow_incident_eq_portLoad
        lastCell residual bandOf cellIndex hindex hoccupied hbalance v]
    _ = 2 * tangentFlowTraffic
          (tangentRatioCellBoundaryFlow
            lastCell residual bandOf cellIndex) :=
      sum_tangentVertexIncident_eq_two_traffic _
    _ = 2 * tangentRatioCellCanonicalCutTraffic
          lastCell residual bandOf cellIndex := by
      rw [tangentRatioCellBoundaryFlow_traffic_eq
        lastCell residual bandOf cellIndex hoccupied]

/-- The cellwise `q` mass has the exact global bound forced by the boundary
ports. -/
theorem sum_abs_tangentRatioCellInternalResidual_le
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0) :
    (∑ v : V,
        |tangentRatioCellInternalResidual residual bandOf cellIndex v|) <=
      (∑ v : V, |residual v|) +
        2 * tangentRatioCellCanonicalCutTraffic
          lastCell residual bandOf cellIndex := by
  have hpoint :
      (∑ v : V,
        (|tangentRatioCellInternalResidual residual bandOf cellIndex v| +
          tangentRatioCellUniformPortLoad residual bandOf cellIndex v)) <=
        ∑ v : V,
          (|residual v| +
            2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v) := by
    exact Finset.sum_le_sum (fun v _hv =>
      abs_internalResidual_add_portLoad_le residual bandOf cellIndex v)
  simp_rw [Finset.sum_add_distrib] at hpoint
  have hports := sum_tangentRatioCellUniformPortLoad_eq_two_cutTraffic
    lastCell residual bandOf cellIndex hindex hoccupied hbalance
  have htwice :
      (∑ v : V,
          2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v) =
        4 * tangentRatioCellCanonicalCutTraffic
          lastCell residual bandOf cellIndex := by
    rw [← Finset.mul_sum, hports]
    ring
  rw [hports, htwice] at hpoint
  linarith

/-- Exact traffic before applying the `ell^1` estimate. -/
theorem tangentRatioCellEarthmoverFlow_traffic_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    tangentFlowTraffic
        (tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex) =
      tangentRatioCellCanonicalCutTraffic
          lastCell residual bandOf cellIndex +
        (∑ v : V,
          |tangentRatioCellInternalResidual residual bandOf cellIndex v|) / 2 := by
  unfold tangentRatioCellEarthmoverFlow
  rw [tangentFlowTraffic_add,
    tangentRatioCellBoundaryFlow_traffic_eq
      lastCell residual bandOf cellIndex hoccupied,
    tangentRatioCellInternalFlow_traffic_eq
      lastCell residual bandOf cellIndex hindex hoccupied]

/-- The literal paper traffic ledger: half the original residual mass plus
twice the prefix-cut traffic. -/
theorem tangentRatioCellEarthmoverFlow_traffic_le
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0) :
    tangentFlowTraffic
        (tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex) <=
      tangentDistributedTotalTrafficLedger residual
        (tangentRatioCellCanonicalCutTraffic
          lastCell residual bandOf cellIndex) := by
  rw [tangentRatioCellEarthmoverFlow_traffic_eq
      lastCell residual bandOf cellIndex hindex hoccupied]
  unfold tangentDistributedTotalTrafficLedger
  have hq := sum_abs_tangentRatioCellInternalResidual_le
    lastCell residual bandOf cellIndex hindex hoccupied hbalance
  linarith

/-! ## From full vertex incident mass to the positive-support census -/

theorem sum_union_le_add_sum_of_nonneg_real
    {E : Type*} [DecidableEq E] (s t : Finset E)
    (weight : E -> Real) (hweight : forall edge, 0 <= weight edge) :
    (∑ edge ∈ s ∪ t, weight edge) <=
      (∑ edge ∈ s, weight edge) + ∑ edge ∈ t, weight edge := by
  calc
    (∑ edge ∈ s ∪ t, weight edge) =
        ∑ edge ∈ s ∪ (t \ s), weight edge := by
      rw [Finset.union_sdiff_self_eq_union]
    _ = (∑ edge ∈ s, weight edge) +
          ∑ edge ∈ t \ s, weight edge := by
      rw [Finset.sum_union Finset.disjoint_sdiff]
    _ <= (∑ edge ∈ s, weight edge) +
          ∑ edge ∈ t, weight edge := by
      exact add_le_add (le_refl _)
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun edge _hedge _hnew => hweight edge))

theorem sum_source_filter_eq_outgoing
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (v : V) :
    (∑ edge ∈ (Finset.univ : Finset (V × V)).filter
        (fun edge => edge.1 = v), flow edge.1 edge.2) =
      ∑ w : V, flow v w := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single v]
  · simp
  · intro source hsource
    simp [hsource]

theorem sum_target_filter_eq_incoming
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (v : V) :
    (∑ edge ∈ (Finset.univ : Finset (V × V)).filter
        (fun edge => edge.2 = v), flow edge.1 edge.2) =
      ∑ w : V, flow w v := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro source _hsource
  rw [Fintype.sum_eq_single v]
  · simp
  · intro target htarget
    simp [htarget]

/-- A positive-support edge is counted only once by
`tangentIncidentFlowMass`, whereas the full row-plus-column expression may
count a loop twice.  Nonnegativity therefore gives this useful inequality
without needing a no-loop hypothesis. -/
theorem tangentIncidentPositiveFlowMass_le_vertexIncident
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (hflow : forall source target,
      0 <= flow source target)
    (label : V -> Nat) (hlabel : Function.Injective label) (v : V) :
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (fun edge : V × V => flow edge.1 edge.2) (label v) <=
      (∑ w : V, flow v w) + ∑ w : V, flow w v := by
  classical
  let sourceEdges : Finset (V × V) :=
    (Finset.univ : Finset (V × V)).filter (fun edge => edge.1 = v)
  let targetEdges : Finset (V × V) :=
    (Finset.univ : Finset (V × V)).filter (fun edge => edge.2 = v)
  let allIncident : Finset (V × V) := sourceEdges ∪ targetEdges
  have hsubset :
      tangentIncidentEdges
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          (label v) ⊆ allIncident := by
    intro edge hedge
    have hdata := Finset.mem_filter.mp hedge
    have hlabels := hdata.2
    unfold tangentStarEdgeSource tangentStarEdgeTarget at hlabels
    unfold allIncident sourceEdges targetEdges
    rw [Finset.mem_union]
    rcases hlabels with hsource | htarget
    · exact Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hlabel hsource⟩)
    · exact Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hlabel htarget⟩)
  calc
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (fun edge : V × V => flow edge.1 edge.2) (label v) <=
        ∑ edge ∈ allIncident, flow edge.1 edge.2 := by
      unfold tangentIncidentFlowMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun edge _hedge _hnew => hflow edge.1 edge.2)
    _ <= (∑ edge ∈ sourceEdges, flow edge.1 edge.2) +
          ∑ edge ∈ targetEdges, flow edge.1 edge.2 := by
      exact sum_union_le_add_sum_of_nonneg_real
        sourceEdges targetEdges (fun edge => flow edge.1 edge.2)
          (fun edge => hflow edge.1 edge.2)
    _ = (∑ w : V, flow v w) + ∑ w : V, flow w v := by
      rw [show sourceEdges =
          (Finset.univ : Finset (V × V)).filter
            (fun edge => edge.1 = v) by rfl,
        show targetEdges =
          (Finset.univ : Finset (V × V)).filter
            (fun edge => edge.2 = v) by rfl,
        sum_source_filter_eq_outgoing, sum_target_filter_eq_incoming]

/-- The pointwise ledger in exactly the positive-support form consumed by
`TangentDistributedFlowCensus`. -/
theorem tangentRatioCellEarthmoverFlow_positiveIncident_le
    {V Band : Type*} [Fintype V] [DecidableEq V]
    [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (label : V -> Nat) (hlabel : Function.Injective label) (v : V) :
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges
          (tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex))
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (fun edge : V × V => tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex edge.1 edge.2) (label v) <=
      |residual v| +
        2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  calc
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges
          (tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex))
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (fun edge : V × V => tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex edge.1 edge.2) (label v) <=
        (∑ w : V, tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex v w) +
          ∑ w : V, tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex w v :=
      tangentIncidentPositiveFlowMass_le_vertexIncident
        (tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex)
        (tangentRatioCellEarthmoverFlow_nonneg
          lastCell residual bandOf cellIndex) label hlabel v
    _ <= |residual v| +
          2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v :=
      tangentRatioCellEarthmoverFlow_incident_le
        lastCell residual bandOf cellIndex hindex hoccupied hbalance v



/-- One theorem exposing the five construction outputs.  These facts are
kept as theorem conclusions about the visible flow formula, rather than as
fields of a certificate. -/
theorem tangentRatioCellEarthmoverFlow_spec
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0) :
    (forall source target,
      0 <= tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex source target) ∧
      (forall v,
        tangentFlowDivergence
          (tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex) v = residual v) ∧
      TangentFlowRespectsRatioCells bandOf cellIndex
        (tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex) ∧
      tangentFlowTraffic
          (tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex) <=
        tangentDistributedTotalTrafficLedger residual
          (tangentRatioCellCanonicalCutTraffic
            lastCell residual bandOf cellIndex) ∧
      forall v,
        (∑ w : V, tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex v w) +
          (∑ w : V, tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex w v) <=
        |residual v| +
          2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  exact ⟨tangentRatioCellEarthmoverFlow_nonneg
      lastCell residual bandOf cellIndex,
    tangentRatioCellEarthmoverFlow_divergence_eq
      lastCell residual bandOf cellIndex hindex hoccupied hbalance,
    tangentRatioCellEarthmoverFlow_respectsRatioCells
      lastCell residual bandOf cellIndex,
    tangentRatioCellEarthmoverFlow_traffic_le
      lastCell residual bandOf cellIndex hindex hoccupied hbalance,
    tangentRatioCellEarthmoverFlow_incident_le
      lastCell residual bandOf cellIndex hindex hoccupied hbalance⟩



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalDistributedTangentBridge -/
section


/-!
# Canonical selector boundary through a distributed tangent flow

This is the star-free replacement for the boundary portion of
`BankPaperCanonicalTangentResidualBridge`.  A distributed earthmover with
the literal canonical residual has the exact factorization boundary needed
by `tangentUpdate_valuation_eq_target`; equal request splitting preserves it.

No clean-list estimate or final collision conclusion occurs in this module.
The only collision-facing asymptotic recorded here is the unconditional
dense-support ceiling `yNat^3 / n -> 0`.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section













/-! ## Canonical notation for an arbitrary distributed flow -/











/-- Exact canonical request boundary for an arbitrary nonnegative
distributed flow with the literal selector-residual divergence.  This
replaces the star-specific theorem
`bankPaperCanonicalTangentStarSplitRequest_boundary_eq_selectorDeficit` in a
distributed Section 9 assembly. -/
theorem bankPaperCanonicalDistributedSplitRequest_boundary_eq_selectorDeficit
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (x : Nat -> Real)
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall p,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed candidates x)
    (L sigma : Real) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p) ∧
      forall q : Nat,
        (∑ request : TangentSplitRequest
              (tangentPositiveFlowEdges flow) L sigma
                (fun edge :
                    BankPaperCanonicalTangentPrime n W ×
                      BankPaperCanonicalTangentPrime n W =>
                  flow edge.1 edge.2),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource
                    (tangentStarEdgeSource
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real) -
                ((tangentSplitRequestTarget
                    (tangentStarEdgeTarget
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real))) =
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x q := by
  refine ⟨hdivergence, ?_⟩
  intro q
  calc
    (∑ request : TangentSplitRequest
          (tangentPositiveFlowEdges flow) L sigma
            (fun edge :
                BankPaperCanonicalTangentPrime n W ×
                  BankPaperCanonicalTangentPrime n W =>
              flow edge.1 edge.2),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource
                (tangentStarEdgeSource
                  bankPaperCanonicalTangentPrimeLabel)
                request).factorization q : Real) -
            ((tangentSplitRequestTarget
                (tangentStarEdgeTarget
                  bankPaperCanonicalTangentPrimeLabel)
                request).factorization q : Real))) =
      ∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
            R certificate fixed candidates x p *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : Real) :=
      tangentDistributedSplitRequest_factorizationBoundary_eq_residual
        flow bankPaperCanonicalTangentPrimeLabel
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates x)
        hflow hdivergence L sigma q
    _ = bankPaperCanonicalSelectorValuationDeficit
          R certificate fixed candidates x q :=
      sum_bankPaperCanonicalTangentResidual_mul_factorization_eq_deficit
        R certificate fixed candidates x hsupport q

/-- Selector-facing version of the distributed boundary theorem.  Its
selector input is exactly the upstream rounding predicate; no target traffic
or collision condition is accepted here. -/
theorem bankPaperCanonicalRoundedSelector_distributedBoundary
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall p,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p)
    (L sigma : Real) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p) ∧
      forall q : Nat,
        (∑ request : TangentSplitRequest
              (tangentPositiveFlowEdges flow) L sigma
                (fun edge :
                    BankPaperCanonicalTangentPrime n W ×
                      BankPaperCanonicalTangentPrime n W =>
                  flow edge.1 edge.2),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource
                    (tangentStarEdgeSource
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real) -
                ((tangentSplitRequestTarget
                    (tangentStarEdgeTarget
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real))) =
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector q := by
  apply bankPaperCanonicalDistributedSplitRequest_boundary_eq_selectorDeficit
    R certificate fixed candidates selector flow hflow hdivergence
  exact
    (bankPaperCanonicalRoundedSelectorTangentInput_selectorState S).2.2.2



/-! ## Selector bounds converted to the literal cell ledgers -/









/-! ## The explicit ratio-cell flow, rather than a supplied flow -/

/-- The selector predicate supplies band balance; consecutive occupied cell
geometry supplies the only remaining combinatorial hypotheses.  The flow
itself is the visible formula `tangentRatioCellEarthmoverFlow`. -/
theorem bankPaperCanonicalRoundedSelector_ratioCellEarthmover_spec
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (hindex : forall p, cellIndex p <= lastCell (bandOf p))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    (forall source target,
      0 <= tangentRatioCellEarthmoverFlow lastCell
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector)
        bandOf cellIndex source target) ∧
      (forall p,
        tangentFlowDivergence
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) p =
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p) ∧
      TangentFlowRespectsRatioCells bandOf cellIndex
        (tangentRatioCellEarthmoverFlow lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex) ∧
      tangentFlowTraffic
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) <=
        tangentDistributedTotalTrafficLedger
          (V := BankPaperCanonicalTangentPrime n W)
          (bankPaperCanonicalTangentResidual (W := W)
            R certificate fixed candidates selector)
          (tangentRatioCellCanonicalCutTraffic lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) ∧
      forall p,
        (∑ q, tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex p q) +
          (∑ q, tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex q p) <=
        |bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p| +
          2 * tangentRatioCellUniformPortLoad
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex p := by
  apply tangentRatioCellEarthmoverFlow_spec
    lastCell
    (bankPaperCanonicalTangentResidual
      R certificate fixed candidates selector)
    bandOf cellIndex hindex hoccupied
  exact (bankPaperCanonicalRoundedSelectorTangentInput_residualBounds S).1

/-- Positive-support incident form used by the split-request census. -/
theorem bankPaperCanonicalRoundedSelector_ratioCellEarthmover_positiveIncident
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (hindex : forall p, cellIndex p <= lastCell (bandOf p))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (p : BankPaperCanonicalTangentPrime n W) :
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex))
        (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
        (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
        (fun edge => tangentRatioCellEarthmoverFlow lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex edge.1 edge.2)
        (bankPaperCanonicalTangentPrimeLabel p) <=
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| +
        2 * tangentRatioCellUniformPortLoad
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex p := by
  apply tangentRatioCellEarthmoverFlow_positiveIncident_le
    lastCell
    (bankPaperCanonicalTangentResidual
      R certificate fixed candidates selector)
    bandOf cellIndex hindex hoccupied
      (bankPaperCanonicalRoundedSelectorTangentInput_residualBounds S).1
    bankPaperCanonicalTangentPrimeLabel
      bankPaperCanonicalTangentPrimeLabel_injective p

/-- The exact factorization boundary now follows with no arbitrary flow
argument: it is furnished by the explicit ratio-cell earthmover above. -/
theorem bankPaperCanonicalRoundedSelector_ratioCellDistributedBoundary
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (hindex : forall p, cellIndex p <= lastCell (bandOf p))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (L sigma : Real) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      tangentFlowDivergence
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p) ∧
      forall q : Nat,
        (∑ request : TangentSplitRequest
              (tangentPositiveFlowEdges
                (tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex)) L sigma
                (fun edge => tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex edge.1 edge.2),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource
                    (tangentStarEdgeSource
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real) -
                ((tangentSplitRequestTarget
                    (tangentStarEdgeTarget
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real))) =
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector q := by
  have hspec := bankPaperCanonicalRoundedSelector_ratioCellEarthmover_spec
    R certificate fixed candidates lastCell bandOf cellIndex
      pointwiseUpper prefixUpper selector S hindex hoccupied
  exact bankPaperCanonicalRoundedSelector_distributedBoundary
    R certificate fixed candidates bandOf cellIndex
      pointwiseUpper prefixUpper selector S
      (tangentRatioCellEarthmoverFlow lastCell
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector)
        bandOf cellIndex)
      hspec.1 hspec.2.1 L sigma

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalDistributedCandidateSet -/
section


/-!
# Distributed Section 9 on a guarded candidate subset

The original distributed Section 9 API is intentionally retained verbatim:
it works on `roughRawCandidateSet n h K`.  This module adds a parallel,
backward-compatible interface for an arbitrary finite candidate set contained
in that raw universe.

Containment alone does not put the endpoints selected from a clean multiplier
list back into the smaller set.  The generic post-choice theorem therefore
takes selected-endpoint membership, while pre-choice assembly takes clean-list
endpoint closure.  A concrete guarded set obtained by subtracting the
numerical guards is supplied below; its endpoint closure is derived from the
defining set difference and the existing clean-list membership theorem.  No
disjointness conclusion is inferred merely from containment in the raw
candidate set.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## A concrete guarded candidate subset -/









namespace BankPaperRealization

/-! ## Generic deterministic post-choice socket -/



/-! ## Generic finite distributed assembly -/

/-- Assemble the explicit ratio-cell earthmover and collision-free clean
multiplier choice on an arbitrary guarded candidate subset.

All analytic and collision hypotheses are the same as in
`exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets`,
with the selector residual evaluated on `candidates`.  The one additional
pre-choice law is `hendpointClosure`, which says that every multiplier the
collision census is allowed to choose has both numerical endpoints in the
guarded set. -/
theorem exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates
    {c : Real} {depth n W K h X0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixedExceptional fixed candidates : Finset Nat)
    (selector : Nat → Real)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band → Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W → Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W → Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W → Real)
    (prefixUpper : Band → Nat → Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates
        bandOf cellIndex pointwiseUpper prefixUpper selector)
    (density L sigma N : Real)
    (trafficConstant incidentConstant tangentConstant width : Real)
    (trafficError incidentError weightedResidual weightedPort : Real)
    (hn : 0 < n)
    (hdensity : 0 < density) (hL : 0 < L) (hsigma : 0 < sigma)
    (hN : 0 < N) (hscale : L * N = (n : Real))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (hindex : ∀ p, cellIndex p ≤ lastCell (bandOf p))
    (hoccupied : ∀ band cell,
      cell ≤ lastCell band →
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hresidual : ∀ p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
          |bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p| ≤
        weightedResidual)
    (hport : ∀ p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
          tangentRatioCellUniformPortLoad
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex p ≤ weightedPort)
    (htotal : tangentDistributedTotalTrafficLedger
        (V := BankPaperCanonicalTangentPrime n W)
        (bankPaperCanonicalTangentResidual (W := W)
          R certificate fixed candidates selector)
        (tangentRatioCellCanonicalCutTraffic lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex) ≤
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hweightedIncident : weightedResidual + 2 * weightedPort ≤
      incidentConstant * tangentConstant * N * width + incidentError * N)
    (hmain : tangentDistributedPaperMainBudget
        trafficConstant incidentConstant tangentConstant width sigma ≤
      density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
        trafficError incidentError sigma ≤ density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget n (yNat n)
        (tangentDistributedSupportCount
          (BankPaperCanonicalTangentPrime n W)) ≤ density ^ 2 / 96)
    (hlowerPos : ∀ request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) L sigma,
      0 < bankPaperCanonicalDistributedTangentLowerCard
        (density := density) request)
    (hlower : ∀ request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) L sigma,
      bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request ≤
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex))
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex edge.1 edge.2)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card)
    (hlowerScale : ∀ request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) L sigma,
      ∀ side,
        density * n ≤
          (bankPaperCanonicalDistributedTangentLowerCard
            (density := density) request : Real) *
            tangentEndpointLabel
              bankPaperCanonicalDistributedTangentRequestSource
              bankPaperCanonicalDistributedTangentRequestTarget
              side request)
    (hendpointClosure : ∀ request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) L sigma,
      ∀ {common : Nat},
        common ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges
                (tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex))
              (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
              (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
              L sigma
              (fun edge : BankPaperCanonicalTangentPrime n W ×
                  BankPaperCanonicalTangentPrime n W =>
                tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex edge.1 edge.2)
              n K h (roughHeadModulus W) X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request →
          bankPaperCanonicalDistributedTangentRequestSource request *
                common ∈ candidates ∧
            bankPaperCanonicalDistributedTangentRequestTarget request *
                common ∈ candidates)
    (hslack : ∀ request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) L sigma,
      ∀ multiplier,
        multiplier ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges
                (tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex))
              (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
              (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
              L sigma
              (fun edge : BankPaperCanonicalTangentPrime n W ×
                  BankPaperCanonicalTangentPrime n W =>
                tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex edge.1 edge.2)
              n K h (roughHeadModulus W) X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request →
          (sigma / L ≤ selector
                (bankPaperCanonicalDistributedTangentRequestSource request *
                  multiplier) ∧
              selector
                (bankPaperCanonicalDistributedTangentRequestSource request *
                  multiplier) ≤ 1 - sigma / L) ∧
            (sigma / L ≤ selector
                (bankPaperCanonicalDistributedTangentRequestTarget request *
                  multiplier) ∧
              selector
                (bankPaperCanonicalDistributedTangentRequestTarget request *
                  multiplier) ≤ 1 - sigma / L)) :
    ∃ multiplier : BankPaperCanonicalDistributedTangentSplitRequest
        (tangentRatioCellEarthmoverFlow lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex) L sigma → Nat,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges
              (tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed candidates selector)
                bandOf cellIndex))
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (fun edge : BankPaperCanonicalTangentPrime n W ×
                BankPaperCanonicalTangentPrime n W =>
              tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed candidates selector)
                bandOf cellIndex edge.1 edge.2)
            n K h (roughHeadModulus W) X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests
          (tangentPositiveFlowEdges
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex)) L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex edge.1 edge.2))
        bankPaperCanonicalDistributedTangentRequestSource
        bankPaperCanonicalDistributedTangentRequestTarget multiplier ∧
      (∀ p : BankPaperCanonicalTangentPrime n W,
        tangentFlowDivergence
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex) p =
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p) ∧
      (∀ q : Nat,
        (∑ request : BankPaperCanonicalDistributedTangentSplitRequest
              (tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed candidates selector)
                bandOf cellIndex) L sigma,
            tangentSplitRequestWeight request *
              (((bankPaperCanonicalDistributedTangentRequestSource
                    request).factorization q : Real) -
                ((bankPaperCanonicalDistributedTangentRequestTarget
                    request).factorization q : Real))) =
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector q) ∧
      ∃ output : BankPaperCanonicalPostTangentOutput R certificate
          candidates fixed,
        output.selector =
          bankPaperCanonicalDistributedTangentUpdatedSelector
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex) L sigma multiplier selector := by
  let residual := bankPaperCanonicalTangentResidual (W := W)
    R certificate fixed candidates selector
  let portLoad := tangentRatioCellUniformPortLoad residual bandOf cellIndex
  let cutTraffic := tangentRatioCellCanonicalCutTraffic
    lastCell residual bandOf cellIndex
  let flow := tangentRatioCellEarthmoverFlow
    lastCell residual bandOf cellIndex
  let lowerCard : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma → Nat :=
    fun request => bankPaperCanonicalDistributedTangentLowerCard
      (density := density) request
  have hspec := bankPaperCanonicalRoundedSelector_ratioCellEarthmover_spec
    R certificate fixed candidates lastCell bandOf cellIndex
      pointwiseUpper prefixUpper selector S hindex hoccupied
  have hboundary :=
    bankPaperCanonicalRoundedSelector_ratioCellDistributedBoundary
      R certificate fixed candidates lastCell bandOf cellIndex
        pointwiseUpper prefixUpper selector S hindex hoccupied L sigma
  have hpositiveEndpoints : ∀ {source target},
      0 < flow source target → source ≠ target := by
    intro source target hpositive
    exact tangentRatioCellEarthmoverFlow_positive_endpoints_ne
      lastCell residual bandOf cellIndex hpositive
  have hpositiveIncident : ∀ p,
      tangentIncidentFlowMass
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            flow edge.1 edge.2)
          (bankPaperCanonicalTangentPrimeLabel p) ≤
        |residual p| + 2 * portLoad p := by
    intro p
    exact bankPaperCanonicalRoundedSelector_ratioCellEarthmover_positiveIncident
      R certificate fixed candidates lastCell bandOf cellIndex
        pointwiseUpper prefixUpper selector S hindex hoccupied p
  have hyLeNat : yNat n ≤ n := by
    have hthree : 3 * yNat n ≤ n := R.three_mul_yNat_le_n
    omega
  have hyLe : (yNat n : Real) ≤ (n : Real) := by
    exact_mod_cast hyLeNat
  have hySqNat : yNat n * yNat n ≤ n :=
    bankAnchor_yNat_mul_self_le_self hn
  have hySqMul : (yNat n : Real) * (yNat n : Real) ≤ (n : Real) := by
    exact_mod_cast hySqNat
  have hySq : (yNat n : Real) ^ 2 ≤ (n : Real) := by
    simpa only [pow_two] using hySqMul
  have hresidual' : ∀ p,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| ≤
        weightedResidual := by
    simpa only [residual] using hresidual
  have hport' : ∀ p,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * portLoad p ≤
        weightedPort := by
    simpa only [portLoad, residual] using hport
  have htotal' : tangentDistributedTotalTrafficLedger residual cutTraffic ≤
      trafficConstant * tangentConstant * N * width + trafficError * N := by
    simpa only [cutTraffic, residual] using htotal
  have hlowerPos' : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      0 < lowerCard request := by
    simpa only [lowerCard, flow, residual] using hlowerPos
  have hlower' : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W => flow edge.1 edge.2)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card := by
    simpa only [lowerCard, flow, residual] using hlower
  have hlowerScale' : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      ∀ side,
        density * n ≤ (lowerCard request : Real) *
          tangentEndpointLabel
            bankPaperCanonicalDistributedTangentRequestSource
            bankPaperCanonicalDistributedTangentRequestTarget side request := by
    simpa only [lowerCard, flow, residual] using hlowerScale
  have hcensus :=
    R.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus
      certificate fixedExceptional K h (roughHeadModulus W) X0
      bankPaperCanonicalTangentPrimeLabel residual portLoad cutTraffic flow
      hspec.1 hspec.2.1 hpositiveEndpoints hspec.2.2.2.1
      hpositiveIncident bankPaperCanonicalTangentPrimeLabel_injective
      bankPaperCanonicalTangentPrimeLabel_prime
      weightedResidual weightedPort hresidual' hport' (yNat n) density
      hn hdensity bankPaperCanonicalTangentPrimeLabel_le_yNat hyLe hySq
      hL hsigma hN hscale
      trafficConstant incidentConstant tangentConstant width
      trafficError incidentError htotal' hweightedIncident
      hmain herror hceiling lowerCard hlowerPos' hlower' hlowerScale'
  obtain ⟨multiplier, hmultiplierMem, hdistinct⟩ := hcensus.2.2
  have hendpointClosure' : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      ∀ {common : Nat},
        common ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges flow)
              (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
              (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
              L sigma
              (fun edge : BankPaperCanonicalTangentPrime n W ×
                  BankPaperCanonicalTangentPrime n W =>
                flow edge.1 edge.2)
              n K h (roughHeadModulus W) X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request →
          bankPaperCanonicalDistributedTangentRequestSource request * common ∈
              candidates ∧
            bankPaperCanonicalDistributedTangentRequestTarget request * common ∈
              candidates := by
    intro request common hcommon
    simpa only [flow, residual] using
      hendpointClosure request (by
        simpa only [flow, residual] using hcommon)
  have hselectedEndpoints : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request ∈ candidates ∧
        bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request ∈ candidates := by
    intro request
    exact hendpointClosure' request (hmultiplierMem request)
  have hsourceSlack : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) ≤ 1 - sigma / L := by
    intro request
    have h := (hslack request (multiplier request) (by
      simpa only [flow, residual] using
        hmultiplierMem request)).1
    simpa only [flow, residual] using h
  have htargetSlack : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) ≤ 1 - sigma / L := by
    intro request
    have h := (hslack request (multiplier request) (by
      simpa only [flow, residual] using
        hmultiplierMem request)).2
    simpa only [flow, residual] using h
  have hpost :=
    R.exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
      certificate fixedExceptional fixed candidates selector
      bandOf cellIndex pointwiseUpper prefixUpper S flow hspec.1 hspec.2.1
      L sigma hL hsigma hfixedPositive hchargeDvd multiplier
      hmultiplierMem hselectedEndpoints
      hdistinct hsourceSlack htargetSlack
  obtain ⟨output, houtput⟩ := hpost
  refine ⟨multiplier, ?_, ?_, ?_, ?_, output, ?_⟩
  · simpa only [flow, residual] using hmultiplierMem
  · simpa only [flow, residual,
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget] using hdistinct
  · exact hboundary.1
  · simpa only [
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget] using hboundary.2
  · simpa only [flow, residual] using houtput

end BankPaperRealization

end

end Erdos390.WholePaper

end

universe u_1
theorem solution : Erdos390.RemainingAnalyticGoal007_001.{u_1} := by
  exact @Erdos390.WholePaper.BankPaperRealization.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates
