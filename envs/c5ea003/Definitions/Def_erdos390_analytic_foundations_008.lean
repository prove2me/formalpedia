-- Prove2me | Definitions.Def_erdos390_analytic_foundations_008
-- name    : erdos390_analytic_foundations_008
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T15:02:35.058548+00:00
-- url     : https://prove2.me/theorems/8c9ab096-5925-47f8-b0f1-c32a6c8a57ee
-- title:
--   Distributed tangent budgets and actual guarded active-measure data
-- statement:
--   This bundle defines the ratio-cell earthmover and its traffic ledgers, canonical Selberg sieve quantities and clean-list lower bounds, distributed selector updates, actual active-measure/frozen-ledger data, guarded smooth placement and two-zero-head-cell corrections, post-height barycentric targets, and the base-free and Stieltjes forms of the Saias correction.
--
--   For a residual $r$ on finitely many vertices and canonical cut traffic $T_{\rm cut}$, the total traffic ledger is
--   $$T_{\rm total}=\frac12\sum_v|r_v|+2T_{\rm cut}.$$
--   The paper main budget with traffic, incident and tangent constants $C_T,C_I,C_H$, width $w$ and slack parameter $\sigma$ is
--   $$B_{\rm main}=\frac{(16C_T+8C_I)C_Hw}{\sigma},$$
--   with parallel definitions for analytic error and finite-support ceiling budgets. The canonical earthmover is the sum of boundary transport and within-cell residual transport.
--
--   Active seeds are scaled barycentric weights; frozen total and logarithmic masses retain the literal fixed and bank-base contributions. The bundle's constructor, slack, guard-agreement and source-ledger predicates specify the hypotheses joining these quantities. They are used by later closure theorems, rather than claiming that a budget or constructor condition holds automatically.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/TangentDistributedFlowCensus.lean; grouped definitions extracted from multiple source modules at this commit, including Erdos390.WholePaper.TangentDistributedFlowCensus, Erdos390.WholePaper.BankPaperCanonicalPreTangentSelector, Erdos390.WholePaper.TangentBalancedProductFlow, with the remaining originating modules identified by source-module comments in the definition body.

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_007


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

/-- Traffic ledger furnished by the finite-band path construction. -/
def tangentDistributedTotalTrafficLedger
    {V : Type*} [Fintype V]
    (residual : V -> Real) (cutTraffic : Real) : Real :=
  (∑ v : V, |residual v|) / 2 + 2 * cutTraffic

/-- Per-label ledger obtained from pointwise residual mass and the two
adjacent boundary ports.  Injective labels make at most one summand nonzero.
-/
def tangentDistributedLabelIncidentLedger
    {V : Type*} [Fintype V]
    (label : V -> Nat) (residual portLoad : V -> Real) (q : Nat) : Real :=
  ∑ v : V, if label v = q then |residual v| + 2 * portLoad v else 0

/-- Quadratic support is already sufficient at the paper cutoff
`y = n^(2/9)`: the endpoint-weighted ceiling loss is then `O(y^3/n)`. -/
def tangentDistributedSupportCount (V : Type*) [Fintype V] : Nat :=
  Fintype.card V ^ 2

/-- The exact request-collision upper bound after replacing total traffic by
the residual/cut ledger and every weighted incident traffic by the uniform
residual/port ledger. -/
def tangentDistributedResidualCollisionUpper
    {V : Type*} [Fintype V]
    (n labelUpper : Nat) (L sigma : Real)
    (residual : V -> Real) (cutTraffic : Real)
    (weightedResidual weightedPort : Real) : Real :=
  4 *
      (tangentSplitCensusTotalRequestUpper L sigma
          (tangentDistributedTotalTrafficLedger residual cutTraffic)
          (tangentDistributedSupportCount V) /
        n) +
    2 *
      (((4 * L / sigma) * (weightedResidual + 2 * weightedPort) +
          (labelUpper : Real) * tangentDistributedSupportCount V) /
        n)

/-! ## Literal ratio-cell cuts and uniform adjacent-cell ports -/

/-- Two vertices lie in the same exponent band and either the same
multiplicative cell or consecutive cells.  This is the exact combinatorial
support relation used in the paper's finite-band transport. -/
def TangentSameOrAdjacentRatioCell
    {V Band : Type*}
    (bandOf : V -> Band) (cellIndex : V -> Nat) (source target : V) : Prop :=
  bandOf source = bandOf target ∧
    (cellIndex source = cellIndex target ∨
      cellIndex source + 1 = cellIndex target ∨
      cellIndex target + 1 = cellIndex source)

/-- A flow uses only internal-cell or adjacent-cell edges. -/
def TangentFlowRespectsRatioCells
    {V Band : Type*}
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (flow : V -> V -> Real) : Prop :=
  forall {source target}, 0 < flow source target ->
    TangentSameOrAdjacentRatioCell bandOf cellIndex source target

/-- Fixed-ratio geometry for the chosen exponent bands and multiplicative
cells.  For the paper cells this is proved from `rho ^ 3 < r0`. -/
def TangentRatioCellGeometry
    {V Band : Type*}
    (label : V -> Nat) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (ratioUpper : Real) : Prop :=
  forall {source target},
    TangentSameOrAdjacentRatioCell bandOf cellIndex source target ->
      (((max (label source) (label target) : Nat) : Real) /
        ((min (label source) (label target) : Nat) : Real)) <= ratioUpper

/-- Signed prefix load `F_i` at one literal cell boundary. -/
def tangentRatioCellPrefixMass
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cut : Nat) : Real :=
  ∑ v : V,
    if bandOf v = band ∧ cellIndex v <= cut then residual v else 0

/-- The deterministic tail majorant attached to a pointwise residual
bound.  Unlike an independently supplied prefix estimate, this quantity
contains no rounding information: it is just the sum of the declared
pointwise bounds strictly to the right of the cut. -/
def tangentRatioCellTailPointwiseUpper
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (pointwiseUpper : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat) : Real :=
  ∑ v : V,
    if bandOf v = band ∧ cut < cellIndex v then pointwiseUpper v else 0



/-- Number of vertices in one ratio cell. -/
def tangentRatioCellCard
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cell : Nat) : Nat :=
  ((Finset.univ : Finset V).filter
    (fun v => bandOf v = band ∧ cellIndex v = cell)).card

/-- The signed prefix load at the left boundary of a vertex's cell. -/
def tangentRatioCellLeftPrefixMass
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) : Real :=
  if cellIndex v = 0 then 0
  else tangentRatioCellPrefixMass residual bandOf cellIndex
    (bandOf v) (cellIndex v - 1)

/-- Uniform boundary traffic incident to one port, namely
`(|F_{i-1}|+|F_i|)/|Q_i|`. -/
def tangentRatioCellUniformPortLoad
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) : Real :=
  (|tangentRatioCellLeftPrefixMass residual bandOf cellIndex v| +
      |tangentRatioCellPrefixMass residual bandOf cellIndex
        (bandOf v) (cellIndex v)|) /
    tangentRatioCellCard bandOf cellIndex (bandOf v) (cellIndex v)

/-- The two-sided uniform-port majorant obtained only from tail sums of a
pointwise residual bound.  At cell zero there is no left boundary. -/
def tangentRatioCellPointwisePortUpper
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (pointwiseUpper : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (v : V) : Real :=
  ((if cellIndex v = 0 then 0
      else tangentRatioCellTailPointwiseUpper pointwiseUpper bandOf cellIndex
        (bandOf v) (cellIndex v - 1)) +
      tangentRatioCellTailPointwiseUpper pointwiseUpper bandOf cellIndex
        (bandOf v) (cellIndex v)) /
    tangentRatioCellCard bandOf cellIndex (bandOf v) (cellIndex v)

/-- Boundary-flow divergence at one uniformly distributed cell port.  The
right signed load is `F_i` and the left signed load is `F_{i-1}`. -/
def tangentRatioCellBoundaryDivergence
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) : Real :=
  (tangentRatioCellPrefixMass residual bandOf cellIndex
        (bandOf v) (cellIndex v) -
      tangentRatioCellLeftPrefixMass residual bandOf cellIndex v) /
    tangentRatioCellCard bandOf cellIndex (bandOf v) (cellIndex v)

/-- Residual left for the within-cell matching after the two adjacent
boundary transports have been installed. -/
def tangentRatioCellInternalResidual
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) : Real :=
  residual v -
    tangentRatioCellBoundaryDivergence residual bandOf cellIndex v



















/-! ## Visible hypotheses for a distributed construction -/

/- The construction estimates are deliberately *not* bundled into a
structure.  The repository audit discipline forbids hiding a claimed
traffic or incident estimate in a conclusion-bearing certificate.  Every
generic theorem below therefore displays the exact flow property that it
uses. -/

/-! ## Support, locality, and literal traffic consequences -/









/-! ## Boundary preservation for an arbitrary distributed flow -/









/-! ## Weighted per-label port control -/









/-! ## Total and endpoint request counts -/









/-! ## Paper-parameter closure of the collision guard

The three budgets below mirror the actual parameter order in Section 9.
The main term is made small by the fixed band width `w`; the error and
ceiling terms are absorbed only after the mesh is fixed and `n` tends to
infinity.  None of them is a traffic or request-count hypothesis. -/

/-- Paper-scale main contribution to the distributed collision budget. -/
def tangentDistributedPaperMainBudget
    (trafficConstant incidentConstant tangentConstant width sigma : Real) :
    Real :=
  ((16 * trafficConstant + 8 * incidentConstant) *
      tangentConstant * width) / sigma

/-- Paper-scale analytic-error contribution to the distributed collision
budget. -/
def tangentDistributedPaperErrorBudget
    (trafficError incidentError sigma : Real) : Real :=
  (16 * trafficError + 8 * incidentError) / sigma

/-- Paper-scale finite-support ceiling contribution to the distributed
collision budget. -/
def tangentDistributedPaperCeilingBudget
    (n labelUpper supportCount : Nat) : Real :=
  (4 + 2 * (labelUpper : Real)) * supportCount / n









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

/-- Actual rounded selector state and the residual estimates needed before
constructing any tangent flow.

`bandOf` is the fixed exponent-band assignment and `cellIndex` is the
consecutive multiplicative-ratio cell index inside that band.  Thus the last
line is an explicit prefix sum, rather than a target traffic estimate. -/
def BankPaperCanonicalRoundedSelectorTangentInput
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
    (selector : Nat -> Real) : Prop :=
  (∀ a ∈ candidates,
      0 <= selector a ∧ selector a <= 1) ∧
    BankPaperCanonicalSelectorRowIntegral n candidates selector ∧
    BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
      R certificate fixed candidates selector ∧
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
      R certificate fixed candidates selector ∧
    (forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0) ∧
    (forall p : BankPaperCanonicalTangentPrime n W,
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| <= pointwiseUpper p) ∧
    (forall band : Band, forall cut : Nat,
      |tangentRatioCellPrefixMass
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex band cut| <= prefixUpper band cut)



/-! ## Direct projections used by downstream assembly -/





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

/-- Total positive mass of a finite signed vector. -/
def tangentPositiveMass {V : Type*} [Fintype V]
    (q : V -> Real) : Real :=
  ∑ v : V, max (q v) 0

/-- Total absolute value of the negative mass of a finite signed vector. -/
def tangentNegativeMass {V : Type*} [Fintype V]
    (q : V -> Real) : Real :=
  ∑ v : V, max (-q v) 0

/-- The canonical proportional matching of the positive and negative
parts.  Division by zero is harmless: in that case the formula is zero. -/
def tangentBalancedProductFlow {V : Type*} [Fintype V]
    (q : V -> Real) (source target : V) : Real :=
  max (q source) 0 * max (-q target) 0 / tangentPositiveMass q













@[simp]
theorem tangentBalancedProductFlow_self
    {V : Type*} [Fintype V] (q : V -> Real) (v : V) :
    tangentBalancedProductFlow q v v = 0 := by
  by_cases hq : 0 <= q v
  · have hneg : -q v <= 0 := neg_nonpos.mpr hq
    simp [tangentBalancedProductFlow, max_eq_left hq,
      max_eq_right hneg]
  · have hq' : q v <= 0 := le_of_not_ge hq
    have hneg : 0 <= -q v := neg_nonneg.mpr hq'
    simp [tangentBalancedProductFlow, max_eq_right hq',
      max_eq_left hneg]

















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

/-- Uniform probability weight on one ratio cell. -/
def tangentRatioCellUniformWeight
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cell : Nat) (v : V) : Real :=
  if bandOf v = band ∧ cellIndex v = cell then
    1 / tangentRatioCellCard bandOf cellIndex band cell
  else 0











@[simp]
theorem tangentRatioCellUniformWeight_at_vertex
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    tangentRatioCellUniformWeight bandOf cellIndex
        (bandOf v) (cellIndex v) v =
      1 / tangentRatioCellCard bandOf cellIndex
        (bandOf v) (cellIndex v) := by
  simp [tangentRatioCellUniformWeight]

/-- Uniform directed transport attached to one signed prefix cut. -/
def tangentRatioCellBoundaryCutFlow
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (source target : V) : Real :=
  let F := tangentRatioCellPrefixMass residual bandOf cellIndex band cut
  let left := tangentRatioCellUniformWeight bandOf cellIndex band cut
  let right := tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1)
  max F 0 * left source * right target +
    max (-F) 0 * right source * left target







@[simp]
theorem tangentRatioCellBoundaryCutFlow_self
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat) (v : V) :
    tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut v v = 0 := by
  unfold tangentRatioCellBoundaryCutFlow tangentRatioCellUniformWeight
  by_cases hleft : bandOf v = band ∧ cellIndex v = cut
  · simp [hleft]
  · by_cases hright : bandOf v = band ∧ cellIndex v = cut + 1
    · simp [hright]
    · simp [hleft, hright]















/-! ## Finite-sum linearity for flows -/







/-! ## All canonical cuts in one finite band family -/

/-- Literal cut traffic over `0 <= i < lastCell b`. -/
def tangentRatioCellCanonicalCutTraffic
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) : Real :=
  ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
    |tangentRatioCellPrefixMass residual bandOf cellIndex band cut|

/-- Sum of all adjacent-cell uniform cut flows. -/
def tangentRatioCellBoundaryFlow
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) : Real :=
  ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
    tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target



@[simp]
theorem tangentRatioCellBoundaryFlow_self
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    tangentRatioCellBoundaryFlow
      lastCell residual bandOf cellIndex v v = 0 := by
  unfold tangentRatioCellBoundaryFlow
  simp

/-! ## Prefix algebra and exact boundary divergence -/























/-! ## The balanced residual inside each cell -/

/-- The internal residual masked to one literal ratio cell. -/
def tangentRatioCellMaskedInternalResidual
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cell : Nat) (v : V) : Real :=
  if bandOf v = band ∧ cellIndex v = cell then
    tangentRatioCellInternalResidual residual bandOf cellIndex v
  else 0

/-- Sum of the canonical proportional matchings in all cells. -/
def tangentRatioCellInternalFlow
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) : Real :=
  ∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
    tangentBalancedProductFlow
      (tangentRatioCellMaskedInternalResidual
        residual bandOf cellIndex band cell) source target



@[simp]
theorem tangentRatioCellInternalFlow_self
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    tangentRatioCellInternalFlow
      lastCell residual bandOf cellIndex v v = 0 := by
  unfold tangentRatioCellInternalFlow
  simp























/-! ## Support locality -/











/-! ## The complete explicit earthmover -/

/-- Boundary prefix transport plus the balanced within-cell matching. -/
def tangentRatioCellEarthmoverFlow
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) : Real :=
  tangentRatioCellBoundaryFlow
      lastCell residual bandOf cellIndex source target +
    tangentRatioCellInternalFlow
      lastCell residual bandOf cellIndex source target









@[simp]
theorem tangentRatioCellEarthmoverFlow_self
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    tangentRatioCellEarthmoverFlow
      lastCell residual bandOf cellIndex v v = 0 := by
  simp [tangentRatioCellEarthmoverFlow]





















/-! ## From full vertex incident mass to the positive-support census -/

















end

end Erdos390.WholePaper

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

/-- The multiplicative density `nu(d)=1/d`, made total at zero. -/
def tangentReciprocalArithmeticFunction : ArithmeticFunction ℝ :=
  ⟨fun d ↦ if d = 0 then 0 else 1 / (d : ℝ), by simp⟩

theorem tangentReciprocalArithmeticFunction_isMultiplicative :
    tangentReciprocalArithmeticFunction.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [tangentReciprocalArithmeticFunction], ?_⟩
  intro m n hm hn _hcoprime
  simp only [tangentReciprocalArithmeticFunction,
    ArithmeticFunction.coe_mk, hm, hn, mul_ne_zero hm hn, if_false,
    Nat.cast_mul]
  field_simp

@[simp]
theorem tangentReciprocalArithmeticFunction_apply_of_pos
    {d : ℕ} (hd : 0 < d) :
    tangentReciprocalArithmeticFunction d = 1 / (d : ℝ) := by
  simp [tangentReciprocalArithmeticFunction, hd.ne']





/-- The unweighted physical interval `(lo,hi]`, sifted by the squarefree
modulus `P`, with the exact real interval length as total mass. -/
def tangentIntervalReciprocalSieve
    (P lo hi : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := Finset.Ioc lo hi
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := ((hi - lo : ℕ) : ℝ)
  nu := tangentReciprocalArithmeticFunction
  nu_mult := tangentReciprocalArithmeticFunction_isMultiplicative
  nu_pos_of_prime := by
    intro p hp _hpP
    rw [tangentReciprocalArithmeticFunction_apply_of_pos hp.pos]
    exact one_div_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _hpP
    rw [tangentReciprocalArithmeticFunction_apply_of_pos hp.pos]
    have hpReal : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast hp.one_lt
    simpa using
      (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hpReal)





/-! ## The exact endpoint remainder, with constant one -/













/-! ## Exact factorization of exceptional common multipliers -/

/-- The possible positive smooth factors `b`, with the sharper literal
condition `u*b<X0` retained. -/
def tangentExceptionalSmoothIndices (X0 u : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X0).filter (fun b ↦ u * b < X0)









/-- For one smooth factor `b`, the rough labels allowed by the common
multiplier interval.  Coprimality with the head product says exactly that
all prime factors of the label exceed `y`. -/
def tangentExceptionalRoughCandidates
    (n K h y u v b : ℕ) : Finset ℕ :=
  reducedResidueIoc (roughHeadModulus y)
    (n / (v * b)) (tangentBroadUpper n K h / (u * b))

/-- The disjoint union, indexed by the literal smooth factor, of all rough
intervals used in the exceptional-row sieve. -/
def tangentExceptionalSievePairs
    (n K h X0 y u v : ℕ) : Finset (Σ _b : ℕ, ℕ) :=
  (tangentExceptionalSmoothIndices X0 u).sigma
    (tangentExceptionalRoughCandidates n K h y u v)

/-- The exact rough/smooth coordinates attached to a multiplier. -/
def tangentRoughDecompositionIndex (y a : ℕ) : Σ _b : ℕ, ℕ :=
  ⟨completeSmoothPart y a, completeRoughLabel y a⟩







/-! ## Substitution of the verified abstract sieve bound -/

















/-! ## The `delta_* < 1/18`, `y^4=n^(8/9)` remainder arithmetic -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentCleanListCardinalityBridge -/
section


/-!
# Cardinality bridge for the tangent clean common list

This file performs the final finite-cardinality assembly around the tangent
common list.  The head-coprime candidates are the literal reduced residues in
the common-multiplier interval.  Their complement is exactly the already
defined head-bad set, so the head-bad term cancels from the finite-deletion
ledger.

The resulting theorems turn a supplied lower bound for those interval
candidates, supplied upper bounds for the exceptional and remaining deletion
losses, and one explicit natural-number comparison into

`lowerCard ≤ cleanList.card`.

This is the bridge which discharges the `hlower` input of the later
collision-counting terminal when supplied the paper's analytic estimates.
It does not prove any reduced-residue density estimate, exceptional-row
estimate, or final numerical comparison.  Those inputs remain visible in the
statements below.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal head-coprime interval candidates -/

/-- Multipliers in the common interval which survive the fixed head-coprimality
test.  This is just a named presentation of the relevant reduced-residue
interval. -/
def tangentHeadCoprimeCandidates
    (n K h Phead u v : ℕ) : Finset ℕ :=
  (tangentCommonMultiplierInterval n K h u v).filter fun a ↦
    Nat.Coprime a Phead





/-! ## Generic finite-deletion assembly -/



/-! ## Actual-paper sharp specializations -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TangentExceptionalLambdaSquareSieve -/
section


/-!
# Concrete finite Lambda-squared coefficients for the exceptional-row sieve

This file continues the Section 9 Selberg reduction past the abstract
`IsUpperMoebius` interface.  For a finite divisor support

`S(P,R) = {d : d | P, d <= R}`

and real weights `lambda_d`, it defines the literal Lambda-squared
coefficients

`muPlus(q) = sum_{d,e in S(P,R), lcm(d,e)=q} lambda_d lambda_e`.

The divisor sum of these coefficients is proved to be the square

`sum_{q|m} muPlus(q) = (sum_{d in S(P,R), d|m} lambda_d)^2`.

Consequently `lambda_1=1` gives a genuine upper-Moebius sequence.  We also
prove the exact quadratic main-term identity, the level-squared support
bound, and the sharp finite `l1` estimate obtained by partitioning pairs by
their least common multiple.  These yield a concrete interval upper sieve;
no exceptional-cardinality conclusion is assumed.

Finally, the file defines the canonical finite Selberg weights by Mobius
inversion of the diagonal target.  Their normalization `lambda_1=1`, exact
diagonal transform, and optimal quadratic value `1/G(P,R)` are proved here.
The downstream canonical-bounds layer lower-bounds the finite density sum
and upper-bounds the canonical coefficient norm.
-/

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

noncomputable section

/-! ## Finite Lambda-squared coefficients -/

/-- Divisors of `P` retained at Selberg level `R`. -/
def tangentSelbergLambdaSupport (P R : ℕ) : Finset ℕ :=
  P.divisors.filter (fun d ↦ d ≤ R)

@[simp]
theorem mem_tangentSelbergLambdaSupport {P R d : ℕ} :
    d ∈ tangentSelbergLambdaSupport P R ↔
      (d ∣ P ∧ P ≠ 0) ∧ d ≤ R := by
  simp [tangentSelbergLambdaSupport, Nat.mem_divisors]





/-- The divisor-restricted linear form whose square is the Selberg
majorant. -/
def tangentSelbergLambdaLinearForm
    (P R : ℕ) (lambda : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ tangentSelbergLambdaSupport P R,
    if d ∣ m then lambda d else 0

/-- Literal Lambda-squared upper-Moebius coefficient, grouped by the lcm of
the two finite divisor indices. -/
def tangentSelbergLambdaSquareCoefficient
    (P R : ℕ) (lambda : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ d ∈ tangentSelbergLambdaSupport P R,
    ∑ e ∈ tangentSelbergLambdaSupport P R,
      if Nat.lcm d e = q then lambda d * lambda e else 0





/-! ## Level support and exact quadratic moment -/









/-! ## Gcd--totient diagonalization -/





/-- Diagonal coordinate associated with one divisor `r`. -/
def tangentSelbergDiagonalTransform
    (P R : ℕ) (lambda : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ d ∈ tangentSelbergLambdaSupport P R,
    if r ∣ d then lambda d / (d : ℝ) else 0





/-! ## Finite upper-divisibility Mobius inversion -/





/-- The finite diagonal density sum on the level support. -/
def tangentSelbergDensitySum (P R : ℕ) : ℝ :=
  ∑ r ∈ tangentSelbergLambdaSupport P R,
    (ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ)





/-! ## Sharp finite coefficient norm -/



/-! ## A concrete interval upper sieve -/







/-! ## Canonical finite Selberg weights -/

/-- Explicit finite Selberg weight obtained by Mobius-inverting the
diagonal target `mu(r)/(phi(r) G)`. -/
def tangentSelbergCanonicalLambda (P R d : ℕ) : ℝ :=
  if d ∈ tangentSelbergLambdaSupport P R then
    (d : ℝ) / tangentSelbergDensitySum P R *
      ∑ r ∈ tangentSelbergLambdaSupport P R,
        if d ∣ r then
          (ArithmeticFunction.moebius (r / d) : ℝ) *
              (ArithmeticFunction.moebius r : ℝ) /
            (r.totient : ℝ)
        else 0
  else 0



















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

/-- The total arithmetic function `1 / phi(n)`, with value zero at zero. -/
def tangentReciprocalTotientArithmeticFunction : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else 1 / (n.totient : ℝ), by simp⟩



@[simp]
theorem tangentReciprocalTotientArithmeticFunction_apply_of_pos
    {n : ℕ} (hn : 0 < n) :
    tangentReciprocalTotientArithmeticFunction n =
      1 / (n.totient : ℝ) := by
  simp [tangentReciprocalTotientArithmeticFunction, hn.ne']

@[simp]
theorem tangentReciprocalTotientArithmeticFunction_apply_prime
    {p : ℕ} (hp : p.Prime) :
    tangentReciprocalTotientArithmeticFunction p =
      1 / ((p : ℝ) - 1) := by
  rw [tangentReciprocalTotientArithmeticFunction_apply_of_pos hp.pos,
    Nat.totient_prime hp]
  simp only [Nat.cast_sub hp.one_le, Nat.cast_one]

/-- Pointwise `sigma_1(n) / phi(n)`. -/
def tangentSigmaTotientRatioArithmeticFunction : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul
    (((ArithmeticFunction.sigma 1 : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ))
    tangentReciprocalTotientArithmeticFunction



@[simp]
theorem tangentSigmaTotientRatioArithmeticFunction_apply_of_pos
    {n : ℕ} (hn : 0 < n) :
    tangentSigmaTotientRatioArithmeticFunction n =
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
        (n.totient : ℝ) := by
  rw [tangentSigmaTotientRatioArithmeticFunction,
    ArithmeticFunction.pmul_apply,
    tangentReciprocalTotientArithmeticFunction_apply_of_pos hn]
  simp only [ArithmeticFunction.natCoe_apply]
  ring

/-- The nonnegative squarefree-supported multiplicative majorant
`mu(n)^2 prod_{p | n} (4/p)`. -/
def tangentSquarefreeFourOverPrimeArithmeticFunction :
    ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul
    (ArithmeticFunction.pmul
      (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
        ArithmeticFunction ℝ))
      (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
        ArithmeticFunction ℝ)))
    (ArithmeticFunction.prodPrimeFactors
      (fun p ↦ 4 / (p : ℝ)))





@[simp]
theorem tangentSquarefreeFourOverPrimeArithmeticFunction_apply_prime
    {p : ℕ} (hp : p.Prime) :
    tangentSquarefreeFourOverPrimeArithmeticFunction p =
      4 / (p : ℝ) := by
  have hmuZ :=
    ArithmeticFunction.moebius_sq_eq_one_of_squarefree hp.squarefree
  have hmuR : (ArithmeticFunction.moebius p : ℝ) ^ 2 = 1 := by
    exact_mod_cast hmuZ
  simp [tangentSquarefreeFourOverPrimeArithmeticFunction,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply,
    hp.ne_zero, hp]
  simpa only [pow_two] using hmuR



/-- The previous majorant divided pointwise by `n`.  Its Euler factor at a
prime is `4/p^2`. -/
def tangentSquarefreeFourOverSquareArithmeticFunction :
    ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul
    tangentSquarefreeFourOverPrimeArithmeticFunction
    tangentReciprocalArithmeticFunction





@[simp]
theorem tangentSquarefreeFourOverSquareArithmeticFunction_apply_prime
    {p : ℕ} (hp : p.Prime) :
    tangentSquarefreeFourOverSquareArithmeticFunction p =
      4 / (p : ℝ) ^ 2 := by
  rw [tangentSquarefreeFourOverSquareArithmeticFunction,
    ArithmeticFunction.pmul_apply,
    tangentSquarefreeFourOverPrimeArithmeticFunction_apply_prime hp,
    tangentReciprocalArithmeticFunction_apply_of_pos hp.pos]
  ring

/-! ## Full density and logarithmic first moment -/

/-- The untruncated squarefree Selberg density attached to `P`. -/
def tangentSelbergFullDensitySum (P : ℕ) : ℝ :=
  ∑ r ∈ P.divisors, 1 / (r.totient : ℝ)

/-- Its logarithmic first moment. -/
def tangentSelbergFullLogMoment (P : ℕ) : ℝ :=
  ∑ r ∈ P.divisors,
    Real.log (r : ℝ) / (r.totient : ℝ)





/-! A powerset moment inequality.  It is the finite probabilistic estimate
behind the truncation: the first moment of independent nonnegative local
weights is at most their partition function times `sum b_p a_p`. -/





/-! ## Prime sums at the rough-head modulus -/











/-! ## Mertens lower bound for the full Euler product -/

/-- A fixed admissible left endpoint for the verified interval Mertens
estimate. -/
def tangentSelbergMertensBase : ℕ :=
  max fullReciprocalSumUniformCutoff 2





/-- The fixed finite loss obtained by anchoring the verified interval
Mertens estimate at `tangentSelbergMertensBase`. -/
def tangentSelbergMertensLoss : ℝ :=
  |fullReciprocalSum tangentSelbergMertensBase| +
    |Real.log (Real.log (tangentSelbergMertensBase : ℝ))| +
    5 * fullReciprocalSumUniformConstant /
      Real.log (tangentSelbergMertensBase : ℝ) ^ 3











/-! ## Retaining a fixed fraction below level `y^2` -/





/-! ## A universal `exp 4` coefficient-mean bound -/















/-! ## The canonical Lambda norm -/







/-! ## Fixed eventual constants and the closed interval theorem -/

/-- Fixed named main-term constant. -/
def tangentSelbergCanonicalMainConstant : ℝ :=
  10 * Real.exp tangentSelbergMertensLoss

/-- Fixed named canonical-Lambda `l1`-norm constant.  Its square is the
coefficient of the `y^4 / log(y)^2` endpoint term in the final interval
estimate. -/
def tangentSelbergCanonicalLambdaConstant : ℝ :=
  Real.exp 4 * tangentSelbergCanonicalMainConstant















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

/-- The real fixed-head candidate main term, including its exact one-period
endpoint loss. -/
def tangentRoughHeadCandidateMain
    (W n K h u v : ℕ) : ℝ :=
  roughHeadDensity W *
      (((tangentBroadUpper n K h / u - n / v : ℕ) : ℝ)) -
    roughHeadModulus W

/-- A natural lower bound obtained by flooring the nonnegative part of the
literal fixed-head candidate main term. -/
def tangentRoughHeadCandidateLower
    (W n K h u v : ℕ) : ℕ :=
  ⌊max 0 (tangentRoughHeadCandidateMain W n K h u v)⌋₊



/-! ## Assumption-free canonical exceptional upper bound -/

/-- Sum of the literal rough-label interval lengths over the exact smooth
factor index set. -/
def tangentCanonicalExceptionalLengthSum
    (n K h X0 u v : ℕ) : ℝ :=
  ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
    (((tangentBroadUpper n K h / (u * b) - n / (v * b) : ℕ) : ℝ))

/-- Accumulated endpoint remainder in the canonical exceptional-row sieve.
The factor `X0/u` is the exact smooth-index census upper bound. -/
def tangentCanonicalExceptionalRemainder
    (X0 y u : ℕ) : ℝ :=
  ((X0 / u : ℕ) : ℝ) *
    (tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
      Real.log (y : ℝ) ^ 2)

/-- The complete canonical exceptional upper bound: summed interval main
term plus the accumulated `y^4` endpoint remainder. -/
def tangentCanonicalExceptionalUpper
    (n K h X0 y u v : ℕ) : ℝ :=
  tangentCanonicalExceptionalLengthSum n K h X0 u v *
      (tangentSelbergCanonicalMainConstant / Real.log (y : ℝ)) +
    tangentCanonicalExceptionalRemainder X0 y u

/-- Natural ceiling of the canonical exceptional upper bound, in the exact
form consumed by the finite-cardinality bridge. -/
def tangentCanonicalExceptionalNatUpper
    (n K h X0 y u v : ℕ) : ℕ :=
  ⌈tangentCanonicalExceptionalUpper n K h X0 y u v⌉₊







/-! ## Effective lower cards and eventual bridge theorems -/

/-- The lower-card choice suited to the pair-arithmetic scale at the smaller
endpoint label. -/
def tangentEffectiveLowerCard
    (density : ℝ) (n smallerLabel : ℕ) : ℕ :=
  ⌈density * n / smallerLabel⌉₊









namespace BankPaperRealization



end BankPaperRealization

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

abbrev BankPaperCanonicalDistributedTangentSplitRequest
    {n W : Nat}
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (L sigma : Real) :=
  TangentSplitRequest (tangentPositiveFlowEdges flow) L sigma
    (fun edge : BankPaperCanonicalTangentPrime n W ×
        BankPaperCanonicalTangentPrime n W => flow edge.1 edge.2)

def bankPaperCanonicalDistributedTangentRequestSource
    {n W : Nat}
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real} :
    BankPaperCanonicalDistributedTangentSplitRequest flow L sigma -> Nat :=
  tangentSplitRequestSource
    (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)

def bankPaperCanonicalDistributedTangentRequestTarget
    {n W : Nat}
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real} :
    BankPaperCanonicalDistributedTangentSplitRequest flow L sigma -> Nat :=
  tangentSplitRequestTarget
    (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)

def bankPaperCanonicalDistributedTangentLowerCard
    {n W : Nat}
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma density : Real}
    (request : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma) : Nat :=
  tangentEffectiveLowerCard density n
    (min
      (bankPaperCanonicalDistributedTangentRequestSource request)
      (bankPaperCanonicalDistributedTangentRequestTarget request))

/-- The selector update for the distributed request family.  The generic
row-preservation and valuation lemmas for `tangentUpdate` apply unchanged. -/
def bankPaperCanonicalDistributedTangentUpdatedSelector
    {n W : Nat}
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (L sigma : Real)
    (multiplier : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma -> Nat)
    (selector : Nat -> Real) : Nat -> Real :=
  tangentUpdate
    (tangentSplitRequests (tangentPositiveFlowEdges flow) L sigma
      (fun edge : BankPaperCanonicalTangentPrime n W ×
          BankPaperCanonicalTangentPrime n W => flow edge.1 edge.2))
    bankPaperCanonicalDistributedTangentRequestSource
    bankPaperCanonicalDistributedTangentRequestTarget
    multiplier tangentSplitRequestWeight selector







/-! ## Selector bounds converted to the literal cell ledgers -/









/-! ## The explicit ratio-cell flow, rather than a supplied flow -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargeAsymptotic -/
section


/-!
# Negligible small-prime cost of the precharged bank

The precharged base product has valuation at most the global marker budget
times one binary logarithm at each prime.  Summing over all primes at most
`yNat` therefore costs at most

`yNat * bankPaperAnchorMarkerBudget * log₂ (3n)`.

This file proves that literal numerical majorant is little-o of the central
second-order scale.  The analytic core is the identity

`y³ log(n) / (n / log(n)) = log(n)² / n^(1/3)`,

followed by the standard fact that every fixed logarithmic power is
little-o of every positive power.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The cubic endpoint ratio -/

/-- The normalized real model underlying the summed small-prime cost. -/
def bankPaperPrechargeCubicNormalizedCost (n : ℕ) : ℝ :=
  y n ^ 3 * L n / secondOrderScale n







/-! ## Integral cutoffs and the binary logarithm -/







/-! ## The concrete precharge cost -/





/-- Natural-valued version of the same universal majorant. -/
def bankPaperPrechargeSmallPrimeCostMajorant (n : ℕ) : ℕ :=
  yNat n * bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n)





namespace BankPaperRealization









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperPrechargeUniformCapacityAsymptotic -/
section


/-!
# Uniform precharge capacity at every moving small prime

The summed small-prime precharge cost is negligible, but the moving-prime
allocation needs two uniform consequences.  First, the per-prime cost must
fit below an arbitrarily small multiple of `secondOrderScale / (p-1)` for
every prime `p ≤ yNat`.  Second, after adjoining the logarithmic error from
the lower factorial-valuation bound, the total natural cost must fit inside
the actual upper-tail length.

Both statements are derived from the cubic-log majorant proved in
`BankPaperPrechargeAsymptotic`; no new prime-counting input is used here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Uniform per-prime reserve -/



/-! ## Combined moving-prime capacity cost -/

/-- Natural cubic-log term which absorbs the moving logarithmic remainder. -/
def bankPaperPrechargeCubicLogMajorant (n : ℕ) : ℕ :=
  yNat n ^ 3 * Nat.log 2 (3 * n)



/-- A realization-independent majorant for the precharge cost together with
the lower factorial-valuation logarithmic error. -/
def bankPaperPrechargeUniformCapacityMajorant (n : ℕ) : ℕ :=
  bankPaperPrechargeSmallPrimeCostMajorant n +
    2 * bankPaperPrechargeCubicLogMajorant n



/-- The literal cost appearing in the moving-prime lower-cross inequality. -/
def bankPaperPrechargeUniformCapacityCost (c : ℝ) (n : ℕ) : ℕ :=
  yNat n *
    (bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) +
      Nat.log2 (upperTailLength c n) + 1)







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

/-- Remove a finite endpoint-guard set from the literal raw candidates. -/
def bankPaperCanonicalDistributedGuardedCandidates
    (n h K : Nat) (numericalGuards : Finset Nat) : Finset Nat :=
  roughRawCandidateSet n h K \ numericalGuards







namespace BankPaperRealization

/-! ## Generic deterministic post-choice socket -/



/-! ## Generic finite distributed assembly -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalPrefixQuadrature -/
section


/-!
# Harmonic-prime majorants for the canonical prefix adapter

The prefix adapter reduces a signed ratio-cell prefix to the strict tail of
the declared pointwise residual bound.  In the paper that bound is a fixed
nonnegative scale times `1 / p`.  This file performs the remaining analytic
step from literal finite tails to the verified uniform Mertens estimate.

No distribution assertion about the ratio cells is built into the result.
The only geometric input says that every prime in a declared strict tail
lies in an explicit numerical interval `(A,Y]`.  The tail can be an arbitrary
subset of that interval; positivity then permits comparison with the full
prime harmonic sum.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

noncomputable section

/-- The paper pointwise shape after collecting all factors independent of
the prime label into one nonnegative scale.  It includes the specialization
`scale = C_tan * N / L`. -/
def bankPaperCanonicalHarmonicPointwiseUpper
    {n W : Nat} (scale : Real)
    (p : BankPaperCanonicalTangentPrime n W) : Real :=
  scale / (bankPaperCanonicalTangentPrimeLabel p : Real)



/-- The unconditional endpoint majorant obtained from the uniform
reciprocal-prime quadrature theorem. -/
def bankPaperCanonicalHarmonicTailMajorant
    (scale : Real) (A Y : Nat) : Real :=
  scale *
    (Real.log (Real.log (Y : Real)) -
        Real.log (Real.log (A : Real)) +
      5 * fullReciprocalSumUniformConstant /
        Real.log (A : Real) ^ 3)

-- `WholePaper` also has a distinct presentation of `primesUpTo`; the
-- qualification here keeps this set definitionally aligned with
-- `Full.PrimeSums.fullReciprocalSum`.










end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGuardedBridgeConnector -/
section


/-!
# Canonical guarded selector to bridge-fit connector

This module joins the finite objects on the two sides of the Section 8/9
interface without asserting the missing selector theorem.

* `bankPaperCanonicalBridgeData` builds the literal `PaperBridgeFit.BridgeData`
  from an existing guarded structured sample, the canonical barycentric
  baseline, and the canonical regular-mesh partition.
* `BankPaperCanonicalGuardedBridgeSelectorConstructor` is the sole
  existential socket.  Its witness is an actual guarded selector satisfying
  the already defined rounded-selector tangent input and agreeing with the
  bridge baseline on the active structured sample.
* the projection and frozen-layer theorems derive the smooth integer quota,
  feasibility, row integrality, prime-band balance and support, tangent
  balance and pointwise/prefix bounds, the frozen feasibility ledger, and the
  total integer quota.  No one of those conclusions is repeated as a new
  premise.

The active structured sample need only be a subset of the guarded smooth row;
it is not silently identified with the whole row.  All other guarded
coordinates are retained in the frozen layer with their selector weights,
while the fixed exceptional factors have weight one.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open BankPaperRealization

noncomputable section

/-! ## Canonical bridge data -/

/-- The literal bridge data obtained from the canonical barycentric baseline
and the canonical regular-mesh prime partition. -/
def bankPaperCanonicalBridgeData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    BridgeData Head (Fin (M.cellCount + 1)) where
  sampleData := D
  baseline := T.baseline
  partition :=
    Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S
  lowBand := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.lowBand M
  referenceHead := referenceHead
  w := delta + eta
  w_pos := hw
  n_gt_one := hn

@[simp] theorem bankPaperCanonicalBridgeData_sampleData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).sampleData = D :=
  rfl

@[simp] theorem bankPaperCanonicalBridgeData_baseline
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).baseline =
      T.baseline :=
  rfl

@[simp] theorem bankPaperCanonicalBridgeData_partition
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).partition =
          Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition
            M hdelta hn hW S :=
  rfl

@[simp] theorem bankPaperCanonicalBridgeData_lowBand
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).lowBand =
          Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.lowBand M :=
  rfl

@[simp] theorem bankPaperCanonicalBridgeData_w
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).w =
      delta + eta :=
  rfl

@[simp] theorem bankPaperCanonicalBridgeData_q
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).q =
      1 := by
  change T.baseline.totalMass = 1
  exact T.baseline_totalMass

/-! ## Active values and integer row quotas -/

/-- The untagged natural-number support of the structured bridge sample. -/
def bankPaperCanonicalBridgeActiveValues
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) : Finset Nat :=
  Finset.univ.image B.sampleData.value







/-! ## The sole missing constructor and all tangent projections -/





/-! ## Guarded smooth support -/









/-! ## Frozen layer and quota -/























/-! ## Baseline slack and ambient feasibility -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperProposition87ActualDataConnector -/
section


/-!
# Actual paper data at the Proposition 8.7 / guarded-selector interface

The paper does not use the mass-one normalization of the bridge.  Its
literal active weights are the numbers `z_m^0`, and

`q_n = sum_m z_m^0`.

At a clean numerical coordinate the protected frozen layer may overlap the
active layer.  Consequently `q_n` is not, in general, the sum of the whole
guarded selector on the active support.  This module keeps the two layers
separate.  Every guarded candidate is represented by a frozen tag of weight

`preSelector a - activeSeedAmbient a`,

while Proposition 8.7 evolves the active seed.  Thus the protected overlap
is retained exactly and the combined selector at time zero is the supplied
guarded pre-selector.

The single construction still missing from the finite guarded ledger is
named `BankPaperCanonicalActualActiveMeasureConstructor`.  It asks only for
the paper's active-measure realization: the seed has the canonical
barycentric shape, has eventual paper-scale mass at least one, is supported
on the guarded candidates, and is dominated by the already feasible
pre-selector.  Row integrality, target agreement, band balance, support,
pointwise estimates, and prefix estimates are not repeated in this
constructor; they are derived below from the existing guarded selector and
the Proposition 8.7 path.
-/

open Filter Topology Set
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## The literal active mass and its sole construction socket -/

/-- The paper's literal active mass `q_n = sum_m z_m^0`.  The summation is
over the tagged structured sample, before any protected contribution at the
same natural-number coordinate is adjoined. -/
def bankPaperCanonicalLiteralActiveMass
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real) : Real :=
  ∑ m, activeSeed m

/-- The ambient push-forward of the literal active seed.  Collisions are
summed rather than silently discarded; the paper head-simplex data later
make the value map injective. -/
def bankPaperCanonicalActiveSeedAmbientWeight
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (a : Nat) : Real :=
  ∑ m : D.Sample, if D.value m = a then activeSeed m else 0

/-- The one paper-data constructor not supplied by the guarded row ledger.

It is exactly the baseline active-measure realization of Section 8:

* `q_n` is at least one (the eventual consequence of `q_n asymp n/log n`);
* every `z_m^0` has the scaled canonical barycentric form;
* every active coordinate is an actual guarded candidate; and
* the active seed is dominated by the total pre-selector, leaving a
  nonnegative frozen protected remainder.

No quota, row-integrality, prime-target, band, or prefix conclusion occurs
in this predicate. -/
def BankPaperCanonicalActualActiveMeasureConstructor
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real) : Prop :=
  let q := bankPaperCanonicalLiteralActiveMass D activeSeed
  1 <= q ∧
    (forall m : D.Sample,
      activeSeed m = q * T.baseline.baseWeight m) ∧
    (∀ m : D.Sample, D.value m ∈ candidates) ∧
    ∀ a ∈ candidates,
      bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a <=
        preSelector a

/-- The literal mass extracted from the actual active-measure constructor
is at least one. -/
theorem bankPaperCanonicalLiteralActiveMass_one_le
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    1 <= bankPaperCanonicalLiteralActiveMass D activeSeed := by
  exact H.1

/-- In particular, the literal active mass is positive. -/
theorem bankPaperCanonicalLiteralActiveMass_pos
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    0 < bankPaperCanonicalLiteralActiveMass D activeSeed :=
  zero_lt_one.trans_le (bankPaperCanonicalLiteralActiveMass_one_le H)

/-- Projection of the exact scaled barycentric formula for the active seed. -/
theorem bankPaperCanonicalActiveSeed_eq_mass_mul_baseline
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (m : D.Sample) :
    activeSeed m =
      bankPaperCanonicalLiteralActiveMass D activeSeed *
        T.baseline.baseWeight m := by
  exact H.2.1 m







/-- The literal `q_n` associated with a family of actual structured active
seeds. -/
def bankPaperCanonicalLiteralQMass
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (activeSeed : forall n, (D n).Sample -> Real) (n : Nat) : Real :=
  bankPaperCanonicalLiteralActiveMass (D n) (activeSeed n)





/-! ## The actual scaled bridge data -/

/-- Canonical regular-mesh bridge data whose baseline is the paper's actual
active seed and whose total mass is the literal `q_n`. -/
def bankPaperCanonicalActualBridgeData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    BridgeData Head (Fin (M.cellCount + 1)) :=
  bankPaperCanonicalActiveMassBridgeData D T
    (bankPaperCanonicalLiteralActiveMass D activeSeed)
    (bankPaperCanonicalLiteralActiveMass_pos H)
    M hdelta hn hW S referenceHead hw

@[simp] theorem bankPaperCanonicalActualBridgeData_sampleData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalActualBridgeData D T candidates preSelector activeSeed
      H M hdelta hn hW S referenceHead hw).sampleData = D :=
  rfl

@[simp] theorem bankPaperCanonicalActualBridgeData_q
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalActualBridgeData D T candidates preSelector activeSeed
      H M hdelta hn hW S referenceHead hw).q =
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  exact bankPaperCanonicalActiveMassBridgeData_q
    D T (bankPaperCanonicalLiteralActiveMass D activeSeed)
      (bankPaperCanonicalLiteralActiveMass_pos H)
    M hdelta hn hW S referenceHead hw

@[simp] theorem bankPaperCanonicalActualBridgeData_baseWeight
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta)
    (m : D.Sample) :
    (bankPaperCanonicalActualBridgeData D T candidates preSelector activeSeed
      H M hdelta hn hW S referenceHead hw).baseline.baseWeight m =
        activeSeed m := by
  unfold bankPaperCanonicalActualBridgeData
  rw [bankPaperCanonicalActiveMassBridgeData_baseline,
    T.activeMassBaseline_baseWeight]
  exact (bankPaperCanonicalActiveSeed_eq_mass_mul_baseline H m).symm

/-! ## Tagged frozen remainder and exact push-forward -/

/-- Every guarded candidate is retained as a frozen tag.  On an active
coordinate its weight is the protected remainder; away from the active
support it is the whole pre-selector weight. -/
abbrev BankPaperCanonicalActualFrozenIndex (candidates : Finset Nat) :=
  ↑candidates

/-- Natural-number coordinate of an actual frozen candidate tag. -/
def bankPaperCanonicalActualFrozenValue
    {candidates : Finset Nat} :
    BankPaperCanonicalActualFrozenIndex candidates -> Nat :=
  fun a => a.1

/-- Frozen protected remainder on one tagged candidate. -/
def bankPaperCanonicalActualFrozenWeight
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (candidates : Finset Nat)
    (preSelector : Nat -> Real) (activeSeed : D.Sample -> Real)
    (a : BankPaperCanonicalActualFrozenIndex candidates) : Real :=
  preSelector a.1 -
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a.1















/-! ## The initial combined selector -/









/-! ## The literal active marked target and endpoint -/

/-- The active target supplied to Proposition 8.7 is the residual selector
target after subtracting the whole tagged frozen candidate layer. -/
def bankPaperCanonicalActualActiveMarkedTarget
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (p : Nat) : Real :=
  ((certificate.selectorTailTarget R fixed).factorization p : Real) -
    ∑ a : BankPaperCanonicalActualFrozenIndex candidates,
      bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed a *
        valuation p (bankPaperCanonicalActualFrozenValue a)

/-- The actual pushed-forward candidate selector at the Proposition 8.7
endpoint. -/
def bankPaperCanonicalActualP87EndpointSelector
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (path : Real -> B.ParamSpace) : Nat -> Real :=
  bankPaperProposition87EndpointSelector B
    (bankPaperCanonicalActualFrozenValue (candidates := candidates))
    (bankPaperCanonicalActualFrozenWeight
      B.sampleData candidates preSelector activeSeed) path









/-! ## Smooth active support and unchanged complete-rough rows -/























/-! ## Prime support, exact bands, and the derived prefix ledger -/

/-- The literal primewise majorant emitted by Proposition 8.7. -/
def bankPaperCanonicalActualP87PointwiseUpper
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (N Cpost : Real)
    (p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W) : Real :=
  Cpost * N / ((p.1 : Real) * B.L)









/-! ## Complete endpoint handoff -/



/-! ## Direct coupling to the guarded continuation -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstruction -/
section


/-!
# Constructing the actual active measure and isolating its irreducible fit

The paper's baseline realization has two logically different parts.

* Once a normalized barycentric target and its literal active mass `q_n`
  are fixed, the active coordinates are forced:

  `z_m^0 = q_n * T.baseline.baseWeight m`.

  Their sum is definitionally finite and is proved below to be exactly
  `q_n`.  No analytic or selector input is needed for this part.

* For a *previously fixed* guarded pre-selector, one must still know that
  the pre-selector carries this active mass at every active numerical
  coordinate.  Under the already available head-pattern separation and
  candidate feasibility, this reduces exactly to the coordinatewise
  inequality

  `q_n * T.baseline.baseWeight m <= preSelector (D.value m)`.

The latter is named `BankPaperCanonicalActualCoordinateFit`.  It is the
irreducible coupling absent from `BankPaperCanonicalGuardedSectionNineContinuation`:
that continuation records feasibility, row sums, and prime residuals, but
no pointwise relation between its selector and the later active baseline.

The module also gives a completely unconditional self-selector
construction, proves the guarded-support part from the existing geometry,
and shows that the older guarded bridge selector constructor supplies the
coordinate fit whenever it is instantiated with the literal active-mass
baseline.
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

/-! ## The forced finite active seed -/

/-- The paper's coordinate formula
`z_m^0 = q_n * T.baseline.baseWeight m`. -/
def bankPaperCanonicalScaledActiveSeed
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    (q : Real) (m : D.Sample) : Real :=
  q * T.baseline.baseWeight m







/-- The canonical scaled seed has total mass exactly `q`; this is the
finite coordinate realization in the paper's baseline-measure lemma. -/
@[simp] theorem bankPaperCanonicalLiteralActiveMass_scaledActiveSeed
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    (q : Real) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalScaledActiveSeed T q) = q := by
  unfold bankPaperCanonicalLiteralActiveMass
    bankPaperCanonicalScaledActiveSeed
  rw [← Finset.mul_sum, T.baseline.baseWeight_sum,
    T.baseline_totalMass, mul_one]

/-! ## Canonical finite support and a self-selector witness -/

/-- The finite set of numerical coordinates occupied by the structured
active sample, without choosing bridge-band data. -/
def bankPaperCanonicalStructuredActiveValues
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) : Finset Nat :=
  Finset.univ.image D.value

@[simp] theorem mem_bankPaperCanonicalStructuredActiveValues
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} {a : Nat} :
    a ∈ bankPaperCanonicalStructuredActiveValues D ↔
      ∃ m : D.Sample, D.value m = a := by
  simp [bankPaperCanonicalStructuredActiveValues]







/-! ## Exact minimization for a fixed guarded pre-selector -/

/-- Structural support plus full ambient domination for the forced scaled
seed.  This is the literal content left after the barycentric seed formula
has been constructed rather than postulated. -/
def BankPaperCanonicalActualActivePlacement
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) : Prop :=
  (∀ m : D.Sample, D.value m ∈ candidates) ∧
    ∀ a ∈ candidates,
      bankPaperCanonicalActiveSeedAmbientWeight D
          (bankPaperCanonicalScaledActiveSeed T q) a <=
        preSelector a



/-- With numerical head-pattern separation, the ambient seed at the value
of a sample tag is exactly that tag's scaled weight. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hsep : D.HeadPatternsSeparated) (m : D.Sample) :
    bankPaperCanonicalActiveSeedAmbientWeight D
        (bankPaperCanonicalScaledActiveSeed T q) (D.value m) =
      bankPaperCanonicalScaledActiveSeed T q m := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  rw [Finset.sum_eq_single m]
  · simp
  · intro k _hk hkm
    rw [if_neg]
    intro hvalue
    exact hkm (D.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

/-- The irreducible pointwise coupling for an already fixed pre-selector:
each active coordinate must fit under that selector.  No row, target,
band, prefix, or endpoint conclusion is included. -/
def BankPaperCanonicalActualCoordinateFit
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (preSelector : Nat -> Real) (q : Real) : Prop :=
  forall m : D.Sample,
    bankPaperCanonicalScaledActiveSeed T q m <=
      preSelector (D.value m)











/-! ## Guarded geometry and the older bridge-selector constructor -/







/-! ## The literal mass already stored by the paper head simplex -/

/-- Specialization of the forced seed to the repository's explicit paper
head simplex and two-pool physical interpolation data. -/
def bankPaperCanonicalPaperDataActiveSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I) :
    B.sampleData.Sample -> Real :=
  bankPaperCanonicalScaledActiveSeed
    (B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical)
    Rhead.activeMass

/-- The paper-data specialization has literal mass exactly the
`HeadSimplexReserve.activeMass` already present in the repository. -/
@[simp] theorem bankPaperCanonicalLiteralActiveMass_paperDataActiveSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalPaperDataActiveSeed
          B I hlo hhi Rhead Kphysical) = Rhead.activeMass := by
  exact bankPaperCanonicalLiteralActiveMass_scaledActiveSeed
    (B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical)
    Rhead.activeMass

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

/-- The lower half of the paper statement `q_n ≍ n / log n`.

This is strictly weaker than a two-sided comparison and is the minimal
asymptotic fact needed for eventual `1 <= q_n`. -/
def BankPaperCanonicalActiveMassPaperScaleLower
    (q : Nat -> Real) : Prop :=
  exists c : Real, 0 < c ∧
    ∀ᶠ n : Nat in atTop,
      c * secondOrderScale n <= q n



/-! ## Positivity is genuinely insufficient -/

/-- A fully legal head-simplex reserve with positive mass strictly below
one.  The empty head set removes every valuation constraint and makes the
logical gap in `activeMass_pos` explicit. -/
def bankPaperCanonicalSubunitHeadSimplexReserve :
    HeadSimplexReserve (∅ : Finset Nat) where
  exponent := 1
  exponent_pos := by norm_num
  activeMass := 1 / 2
  activeMass_pos := by norm_num
  target := fun p => False.elim (by
    have hnot : ∀ a : Nat, a ∉ (∅ : Finset Nat) :=
      Finset.eq_empty_iff_forall_notMem.mp rfl
    exact hnot p.val p.property)
  margin := 1 / 2
  margin_pos := by norm_num
  vertex_margin := by
    intro p
    exact False.elim (by
      have hnot : ∀ a : Nat, a ∉ (∅ : Finset Nat) :=
        Finset.eq_empty_iff_forall_notMem.mp rfl
      exact hnot p.val p.property)
  zero_margin := by norm_num

@[simp] theorem bankPaperCanonicalSubunitHeadSimplexReserve_activeMass :
    bankPaperCanonicalSubunitHeadSimplexReserve.activeMass = 1 / 2 :=
  rfl





/-! ## All eventual consequences of the minimal input -/











/-! ## The exact `q₀-d` height-centering algebra -/











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











/-! ## The exact missing analytic ledger -/

/-- The smallest Section 8 analytic input not represented by the current
repository constructions.  The first field connects the actual post-guard
smooth mass to the explicit raw base mass; the second is the paper's frozen
height-ledger bound. -/
def BankPaperCanonicalSectionEightAnalyticLedger
    (rawBase qTilde A0 : Nat -> Real) : Prop :=
  (fun n => rawBase n - qTilde n) =o[atTop] secondOrderScale ∧
    A0 =O[atTop] secondOrderScale

/-! ## Nearest-integer initialization preserves the paper scale -/











/-! ## The logarithmically smaller height adjustment -/







/-! ## Full propagation from the minimal missing ledger -/















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedgerReduction -/
section


/-!
# Reduction of the remaining Section 8 analytic ledger

The analytic quota/height bridge deliberately leaves two estimates in
`BankPaperCanonicalSectionEightAnalyticLedger`.  This file separates all
finite and asymptotic algebra around those estimates from the genuinely
missing paper inputs.

For the active mass, the literal intermediate object is the constant
`betaAct / L` layer on the guarded label-one broad pool.  Its difference
from the raw layer is exactly the same constant times the number of deleted
coordinates.  The natural smooth-guard census envelope

`yNat^2 + bankPaperAnchorMarkerBudget`

is already `o(secondOrderScale)`.  Thus only a census bound for the literal
deleted pool and the post-correction identification with the actual
`qTilde` remain.

For the height, the paper first proves the three baseline relations

* `m0 + qTilde = h + O(N/L)`,
* `Lambda0 = m0 L + O(N)`,
* `logY = h L + O(N)`.

Nearest-integer initialization transfers the first relation from `qTilde`
to `q0`; the displayed identity for `A0` then proves `A0 = O(N)`.  Hence the
height half of the old black-box ledger is reduced exactly to those three
named source estimates.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal guarded smooth base -/

/-- The raw label-one base coordinates removed by the exhaustive numerical
guard.  The intersection order agrees with `Finset.card_sdiff`. -/
def bankPaperCanonicalSmoothBaseGuardDeletionPool
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) : Finset Nat :=
  R.roughCanonicalGuardSet certificate deltaStar ∩
    bankPaperCanonicalRawSmoothBasePool W n h K

/-- Exact constant-layer mass on the guarded label-one broad pool. -/
def bankPaperCanonicalGuardedSmoothBaseMass
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) (betaAct : Real) : Real :=
  betaAct / L n *
    ((R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K 1).card : Real)









/-! ### The smooth central-anchor census -/

/-- Promoted residual anchors whose base prime is at most the complete-rough
cutoff.  These are the only central anchors which can have label one. -/
def bankPaperCanonicalSmoothResidualAnchorPool
    (n X y : Nat) : Finset Nat :=
  ((residualCentralPrimes n X).filter fun p => p <= y).image
    (promotedCentralFactor n)



/-- The smooth residual-anchor pool has at most `y` elements. -/
theorem bankPaperCanonicalSmoothResidualAnchorPool_card_le
    (n X y : Nat) :
    (bankPaperCanonicalSmoothResidualAnchorPool n X y).card <= y := by
  let primes := (residualCentralPrimes n X).filter fun p => p <= y
  have hsubset : primes ⊆ Finset.Icc 1 y := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr
      ⟨(residualCentralPrimes_prime hpData.1).pos, hpData.2⟩
  calc
    (bankPaperCanonicalSmoothResidualAnchorPool n X y).card <=
        primes.card := by
      exact Finset.card_image_le
    _ <= (Finset.Icc 1 y).card := Finset.card_le_card hsubset
    _ <= y := by
      rw [Nat.card_Icc]
      omega





/-! ## Honest tail families and their total asymptotic extensions -/

/-- One realized bank together with its correctly indexed guarded anchor
certificate. -/
def BankPaperCanonicalGuardedTailFiber
    (c : Real) (depth n : Nat) : Type :=
  Σ R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)),
    GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)

set_option maxHeartbeats 800000 in
/-- A coherent choice of realized banks and guarded anchor certificates only
on a genuine tail `N ≤ n`.  Unlike a family indexed by every natural number,
this interface is inhabited by the existing eventual construction and does
not request the impossible realization at `n = 0`. -/
structure BankPaperCanonicalGuardedTailFamily
    (c : Real) (depth N : Nat) where
  fiber : ∀ n, N ≤ n →
    BankPaperCanonicalGuardedTailFiber c depth n

/-- The realized bank in an honest tail-family fiber. -/
def BankPaperCanonicalGuardedTailFamily.realization
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (n : Nat) (hn : N ≤ n) :
    BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)) :=
  (BankPaperCanonicalGuardedTailFamily.fiber F n hn).1

/-- The guarded anchor certificate paired with the realized tail bank. -/
def BankPaperCanonicalGuardedTailFamily.certificate
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (n : Nat) (hn : N ≤ n) :
    let R := BankPaperCanonicalGuardedTailFamily.realization F n hn
    GuardedCentralAnchorCertificate c depth n
      (BankPaperRealization.anchorGuardLeftCore R)
      (BankPaperRealization.anchorGuardRightCore R)
      (BankPaperRealization.centralChangedMarkers R depth) :=
  (BankPaperCanonicalGuardedTailFamily.fiber F n hn).2

/-- Total guarded-base extension of a tail family.  Below the tail threshold
it equals the raw base, so the raw-to-guarded deletion identity remains exact
there with zero deleted coordinates. -/
def BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (W K : Nat) (betaAct deltaStar : Real) (n : Nat) : Real :=
  if hn : N ≤ n then
    bankPaperCanonicalGuardedSmoothBaseMass
      (BankPaperCanonicalGuardedTailFamily.realization F n hn)
      (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
        deltaStar W K betaAct
  else
    bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct

/-- Total deletion-cardinality extension of a tail family, with the missing
finite prefix set to zero. -/
def BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (W K : Nat) (deltaStar : Real) (n : Nat) : Real :=
  if hn : N ≤ n then
    ((bankPaperCanonicalSmoothBaseGuardDeletionPool
      (BankPaperCanonicalGuardedTailFamily.realization F n hn)
      (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
        deltaStar W K).card : Real)
  else
    0

/-- Total relevant-anchor-cardinality extension of a tail family, again with
zero on the finite prefix where no realization is requested. -/
def BankPaperCanonicalGuardedTailFamily.extendedAnchorIntersectionCard
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (W K : Nat) (n : Nat) : Real :=
  if hn : N ≤ n then
    (((BankPaperCanonicalGuardedTailFamily.certificate F n hn).anchors ∩
      bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card : Real)
  else
    0

/-! ## The already-small guard census envelope -/

/-- The paper-sized envelope for smooth guard deletions.  The square allows
both the promoted smooth-anchor census and all precharged bank states to be
absorbed without encoding either family into an asymptotic definition. -/
def bankPaperCanonicalSmoothGuardCensusEnvelope (n : Nat) : Real :=
  (yNat n : Real) ^ 2 + (bankPaperAnchorMarkerBudget n : Real)









/-- The smallest finite guard-census input still needed for a chosen family
of actual banks and guarded certificates. -/
def BankPaperCanonicalSmoothGuardDeletionCensus
    (deletedCard : Nat -> Real) : Prop :=
  deletedCard =O[atTop] bankPaperCanonicalSmoothGuardCensusEnvelope







/-- The post-guard correction estimate which is not present in the current
rough-selector API: after literal guard deletion, all precharge and signed
row-correction changes alter the active label-one mass by `o(N)`. -/
def BankPaperCanonicalGuardedSmoothCorrectionEstimate
    (guardedBase qTilde : Nat -> Real) : Prop :=
  (fun n => guardedBase n - qTilde n) =o[atTop]
    secondOrderScale





/-! ## Reduction of the frozen height defect -/

/-- The three source estimates displayed immediately before the definition
of `A0` in Section 8.  Here `m0` is the total frozen mass, distinct from the
smooth-row frozen mass `mFrozen` used in the nearest-integer quota. -/
def BankPaperCanonicalFrozenBaselineSourceLedger
    (h logY Lambda0 m0 qTilde : Nat -> Real) : Prop :=
  (fun n => m0 n + qTilde n - h n) =O[atTop]
      (fun n => secondOrderScale n / L n) ∧
    (fun n => Lambda0 n - m0 n * L n) =O[atTop]
      secondOrderScale ∧
    (fun n => logY n - h n * L n) =O[atTop]
      secondOrderScale









/-! ## The complete reduced source ledger -/

/-- All estimates still absent after the finite and asymptotic reductions
in this file.  The raw-to-guarded identity is deliberately not a field: for
the literal pools it is the unconditional theorem
`bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion`. -/
def BankPaperCanonicalSectionEightAnalyticSourceLedger
    (guardedBase qTilde deletedCard h logY Lambda0 m0 : Nat -> Real) : Prop :=
  BankPaperCanonicalSmoothGuardDeletionCensus deletedCard ∧
    BankPaperCanonicalGuardedSmoothCorrectionEstimate guardedBase qTilde ∧
    BankPaperCanonicalFrozenBaselineSourceLedger
      h logY Lambda0 m0 qTilde









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalValuationFibers -/
section


/-!
# Finite valuation fibres for the literal fixed exceptional factors

This file gives the first finite low-prime bridge for the paper's literal
fixed exceptional set.  The exceptional upper factors are partitioned by
their complete smooth part at the canonical cutoff `yNat n`.  At a prime
`p ≤ yNat n`, the factorization charge is therefore the corresponding
smooth-part valuation times the size of each fibre.

Each actual fibre injects, by its complete rough label, into the physical
reduced-residue interval obtained by dividing `(2n,2n+h]` by that smooth
part.  The last theorem substitutes the already proved canonical finite
Selberg estimate for these candidate intervals.  No smooth-number census,
valuation-sum estimate, or asymptotic exceptional-charge bound is asserted
here.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Canonical smooth fibres and their rough candidates -/

/-- The complete smooth parts which actually occur among the literal
exceptional upper factors. -/
def paperExceptionalSmoothParts
    (n h : ℕ) (deltaStar : ℝ) : Finset ℕ :=
  (paperExceptionalUpperFactors n h deltaStar).image
    (completeSmoothPart (yNat n))

/-- The literal exceptional upper factors having a prescribed complete
smooth part at the canonical rough cutoff. -/
def paperExceptionalSmoothFiber
    (n h : ℕ) (deltaStar : ℝ) (b : ℕ) : Finset ℕ :=
  (paperExceptionalUpperFactors n h deltaStar).filter
    (fun a ↦ completeSmoothPart (yNat n) a = b)

/-- Possible complete rough labels in the physical upper interval once the
smooth part `b` is fixed.  Coprimality to the rough-head modulus is retained
literally, while the exceptional lower cutoff on the rough label is
deliberately discarded, exactly as in the paper's Selberg overcount. -/
def paperExceptionalRoughCandidates
    (n h y b : ℕ) : Finset ℕ :=
  reducedResidueIoc (roughHeadModulus y)
    ((2 * n) / b) ((2 * n + h) / b)

@[simp]
theorem mem_paperExceptionalSmoothParts
    {n h b : ℕ} {deltaStar : ℝ} :
    b ∈ paperExceptionalSmoothParts n h deltaStar ↔
      ∃ a ∈ paperExceptionalUpperFactors n h deltaStar,
        completeSmoothPart (yNat n) a = b := by
  simp only [paperExceptionalSmoothParts, Finset.mem_image]

@[simp]
theorem mem_paperExceptionalSmoothFiber
    {n h a b : ℕ} {deltaStar : ℝ} :
    a ∈ paperExceptionalSmoothFiber n h deltaStar b ↔
      a ∈ paperExceptionalUpperFactors n h deltaStar ∧
        completeSmoothPart (yNat n) a = b := by
  simp only [paperExceptionalSmoothFiber, Finset.mem_filter]

@[simp]
theorem mem_paperExceptionalRoughCandidates
    {n h y b r : ℕ} :
    r ∈ paperExceptionalRoughCandidates n h y b ↔
      (2 * n) / b < r ∧ r ≤ (2 * n + h) / b ∧
        Nat.Coprime r (roughHeadModulus y) := by
  simp only [paperExceptionalRoughCandidates, reducedResidueIoc,
    Finset.mem_filter, Finset.mem_Ioc, and_assoc]



/-! ## Exact low-prime valuation partition -/



/-! ## Injection of each actual fibre into a reduced-residue interval -/







/-! ## The fixed exceptional product -/

namespace BankPaperRealization





end BankPaperRealization

/-! ## Canonical Selberg substitution on each candidate interval -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ExceptionalValuationSums -/
section


/-!
# Elementary finite valuation sums

This file records the two elementary estimates used when a fixed exceptional
integer contributes a factorization-coordinate charge (the `p`-adic charge
when `p` is prime).  The unweighted prefix is exactly the corresponding
factorization coordinate of a factorial.  Discrete summation by parts then
converts the same prefix estimate into a harmonic weighted bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







/-- Real partial valuation sum.  Naming it keeps the finite Abel identity
readable and gives later charge arguments a reusable prefix function. -/
def valuationPrefixReal (p B : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)

@[simp]
theorem valuationPrefixReal_zero (p : ℕ) : valuationPrefixReal p 0 = 0 := by
  simp [valuationPrefixReal]



















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

/-- The least natural exceptional-row cutoff which is at least the paper's
real threshold `X0=n^deltaStar`.  Using the ceiling makes the integral clean
condition a strengthening of the literal real condition, rather than losing
the unit-width boundary band. -/
def tangentPaperExceptionalCutoff (deltaStar : ℝ) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ deltaStar⌉₊

/-- The fixed positive density reserved after the raw head gap and the
canonical exceptional loss have been separated. -/
def tangentPaperHeadGap (W : ℕ) (r0 : ℝ) : ℝ :=
  roughHeadDensity W * (2 - r0)

/-- One sixteenth of the literal fixed-head gap. -/
def tangentPaperCleanListDensity (W : ℕ) (r0 : ℝ) : ℝ :=
  tangentPaperHeadGap W r0 / 16















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

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalChargeAsymptotic -/
section


/-!
# Asymptotic package for the fixed exceptional low-prime charge

This file records the constants and scale arithmetic used after the finite
weighted Selberg decomposition of `G_fix` has been proved.  In the notation
of the paper,

* `paperExceptionalSelbergMainConstant` is `C_S`;
* `paperExceptionalSelbergRemainderConstant` is `C_R`;
* `paperExceptionalChargeConstant c` is `A_exc(c)`;
* `paperExceptionalChargeEpsilon deltaStar n` is the normalized
  endpoint/remainder coefficient.

The finite majorant below is obtained by composing the separate finite
rough/smooth-fibre argument with the elementary valuation-prefix estimates.
Nothing in this file assumes that the actual exceptional charge satisfies
that majorant.  We prove the finite charge bound and its analytic packaging,
together with the independent arithmetic support fact that, under the
displayed paper-range hypotheses, the actual low-prime charge is exactly
zero above twice the paper's literal real exceptional cutoff.  The
corresponding safe integral-cutoff statement is retained as a corollary.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Auditable paper constants -/

/-- The fixed smoothness exponent `theta=2/9`. -/
def paperExceptionalTheta : ℝ :=
  2 / 9

/-- `C_S`, the already verified canonical Selberg main-term constant. -/
def paperExceptionalSelbergMainConstant : ℝ :=
  tangentSelbergCanonicalMainConstant

/-- `C_R`, enlarged once so that it pays both the Lambda-squared endpoint
remainder and a copy of the main-term constant. -/
def paperExceptionalSelbergRemainderConstant : ℝ :=
  tangentSelbergCanonicalLambdaConstant ^ 2 +
    paperExceptionalSelbergMainConstant

/-- The paper's exceptional-charge coefficient
`A_exc(c)=16*c*C_S`; it is positive (and hence nonnegative) when `c>0`. -/
def paperExceptionalChargeConstant (c : ℝ) : ℝ :=
  16 * c * paperExceptionalSelbergMainConstant









/-! ## The finite Selberg output and its normalized remainder -/

/-- The exact canonical finite upper bound which the finite
rough/smooth-fibre theorem must supply.  Its two summands are respectively

`4*C_S*deltaStar*L*h/(p*log Y)` and
`4*C_R*X*Y^4/(p*(log Y)^2)`,

with `h=ceil(c*n/log n)`, `X=ceil(n^deltaStar)`, and
`Y=floor(n^(2/9))`. -/
def paperExceptionalFiniteChargeMajorant
    (c deltaStar : ℝ) (n p : ℕ) : ℝ :=
  4 * paperExceptionalSelbergMainConstant * deltaStar * L n *
        (upperTailLength c n : ℝ) /
      ((p : ℝ) * Real.log (yNat n : ℝ)) +
    4 * paperExceptionalSelbergRemainderConstant *
        (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
        (yNat n : ℝ) ^ 4 /
      ((p : ℝ) * Real.log (yNat n : ℝ) ^ 2)

/-- The normalized endpoint/remainder coefficient.  In the paper range
`0 ≤ deltaStar < 1/18` it is `o(1)`, and in the eventual regime where the
displayed denominators are nonzero, multiplication by `N/(pL)`, where
`N=n/L`, recovers the second summand of
`paperExceptionalFiniteChargeMajorant`. -/
def paperExceptionalChargeEpsilon
    (deltaStar : ℝ) (n : ℕ) : ℝ :=
  4 * paperExceptionalSelbergRemainderConstant *
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
      (yNat n : ℝ) ^ 4 * L n ^ 2 /
    ((n : ℝ) * Real.log (yNat n : ℝ) ^ 2)







/-! ## The endpoint remainder tends to zero -/





/-! ## Uniform packaging of the finite majorant -/









/-! ## Exact support cutoff for the actual fixed charge -/







/-! ## Closing the finite weighted Selberg estimate -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector -/
section


/-!
# Actual-data connector for the Section 8 analytic ledger

The reduced Section 8 ledger still names the actual post-guard active mass
and the exact frozen mass/logarithmic ledgers.  The Proposition 8.7 actual-
data connector already supplies the finite decomposition needed to make
those objects literal: every guarded candidate is split into its active
seed and its frozen remainder.

This file adjoins the frozen integral factors, defines the resulting exact
total frozen mass and logarithmic contribution, and proves

`m0 + qTilde = #fixed + sum candidates preSelector`

whenever the actual active-measure constructor holds.  Consequently the
first frozen-baseline estimate reduces to the rough selector's literal
total-mass estimate.  For the canonical scaled seed, its active mass is
exactly the guarded smooth base.  Exact interval support then centers the
frozen logarithmic contribution, while the complete central-tail product
satisfies `logY = h * L + O(secondOrderScale)` by elementary factor bounds.
The generic interval-geometry theorem exposes the selector total-mass
estimate, and the final constructed-quota theorem proves that estimate from
the rough-stage frozen baseline ledger, nearest-integer construction, and
the existing `d = O(secondOrderScale / L)` theorem.

No abstract `qTilde`, `m0`, or `Lambda0` remains in the final theorem.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

/-! ## Literal frozen mass and logarithmic contribution -/

/-- Exact total frozen mass: integral frozen factors have weight one, and
every guarded fractional candidate contributes its actual protected
remainder after subtracting the active seed. -/
def bankPaperCanonicalActualFrozenTotalMass
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real) : Real :=
  (fixed.card : Real) + (bankBase.card : Real) +
    ∑ a : BankPaperCanonicalActualFrozenIndex candidates,
      bankPaperCanonicalActualFrozenWeight
        D candidates preSelector activeSeed a

/-- Exact ordinary logarithmic contribution of the same frozen data. -/
def bankPaperCanonicalActualFrozenLogMass
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real) : Real :=
  (∑ a ∈ fixed, Real.log (a : Real)) +
    (∑ a ∈ bankBase, Real.log (a : Real)) +
    ∑ a : BankPaperCanonicalActualFrozenIndex candidates,
      bankPaperCanonicalActualFrozenWeight
          D candidates preSelector activeSeed a *
        Real.log (bankPaperCanonicalActualFrozenValue a : Real)





/-! ## Families of literal actual data -/

/-- Varying exact total frozen mass. -/
def bankPaperCanonicalActualFrozenTotalMassFamily
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalActualFrozenTotalMass
    (D n) (fixed n) (bankBase n) (candidates n) (preSelector n)
      (activeSeed n)

/-- Varying exact frozen logarithmic contribution. -/
def bankPaperCanonicalActualFrozenLogMassFamily
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalActualFrozenLogMass
    (D n) (fixed n) (bankBase n) (candidates n) (preSelector n)
      (activeSeed n)

/-! ## Elementary logarithmic geometry of the literal upper tail -/

/-- The paper's literal real-valued upper-tail height. -/
def bankPaperCanonicalUpperTailHeight (c : Real) (n : Nat) : Real :=
  (upperTailLength c n : Real)

/-- The logarithm of the complete central tail product. -/
def bankPaperCanonicalCentralTailLogTarget (c : Real) (n : Nat) : Real :=
  Real.log (centralTailProduct n (upperTailLength c n) : Real)











/-! ## Centering the literal frozen logarithmic ledger -/







/-- Exact finite geometry needed to center the frozen ledger: every fixed or
fractional candidate is an actual factor in the paper interval `(n,2n+h]`.
This is structural data, not an asymptotic estimate. -/
def BankPaperCanonicalActualFrozenIntervalGeometry
    {c : Real} (fixed bankBase candidates : Nat -> Finset Nat) : Prop :=
  ∀ᶠ n : Nat in atTop,
    fixed n ⊆ factorInterval n
        (upperEndpoint n (upperTailLength c n)) ∧
      bankBase n ⊆ factorInterval n
        (upperEndpoint n (upperTailLength c n)) ∧
      candidates n ⊆ factorInterval n
        (upperEndpoint n (upperTailLength c n))

/-- The selector-mass interface used by the generic interval-geometry
adapter.  The constructed smooth-quota theorem below derives it from the
rough-stage frozen baseline source. -/
def BankPaperCanonicalActualSelectorMassEstimate
    (c : Real) (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real) : Prop :=
  (fun n => ((fixed n).card : Real) +
      ((bankBase n).card : Real) + (∑ a ∈ candidates n, preSelector n a) -
        bankPaperCanonicalUpperTailHeight c n) =O[atTop]
    (fun n => secondOrderScale n / L n)



/-- Exact nonsmooth-row state consumed by the charged finite ledger.  This
packages only construction equations; it contains no estimate. -/
def BankPaperCanonicalChargedNonsmoothRowRealization
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (selector : Nat -> Real) : Prop :=
  (∀ label ∈ completeRoughLabelSet (yNat n)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          selector a) =
        R.roughCanonicalPostchargeRowTarget deltaStar label) ∧
  ∀ label ∈ completeRoughLabelSet (yNat n)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
    label ≠ 1 -> RoughCanonicalExceptionalLabel n deltaStar label ->
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          selector a) = 0

/-! ## Exact charged-selector row ledger -/





/-- The finite universe of complete rough labels needed to compare the
literal upper row, fixed exceptional charge, precharge base state, and
guarded flexible selector.  The smooth label is inserted even when all four
finite sets happen to be empty. -/
def bankPaperCanonicalChargedLabelSet
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) : Finset Nat :=
  insert 1
    (((completeRoughLabelSet (yNat n) (roughUpperBlock n h) ∪
        completeRoughLabelSet (yNat n)
          (R.paperFixedExceptionalFactors deltaStar)) ∪
      completeRoughLabelSet (yNat n) R.prechargeBaseState) ∪
      completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K))





























/-! ## The remaining actual analytic sources -/

/-- The exact missing identification for the active side, now tied to the
literal tagged active seed rather than to an abstract function `qTilde`. -/
def BankPaperCanonicalActualGuardedSmoothMassEstimate
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (activeSeed : forall n, (D n).Sample -> Real)
    (guardedBase : Nat -> Real) : Prop :=
  (fun n => guardedBase n -
      bankPaperCanonicalLiteralQMass D activeSeed n) =o[atTop]
    secondOrderScale





/-- The three remaining baseline estimates after using the exact
frozen-plus-active decomposition.  Every function here is literal data. -/
def BankPaperCanonicalActualFrozenBaselineEstimates
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (h logY : Nat -> Real) : Prop :=
  (fun n => ((fixed n).card : Real) +
      ((bankBase n).card : Real) +
      (∑ a ∈ candidates n, preSelector n a) - h n) =O[atTop]
      (fun n => secondOrderScale n / L n) ∧
    (fun n =>
      bankPaperCanonicalActualFrozenLogMassFamily
          D fixed bankBase candidates preSelector activeSeed n -
        bankPaperCanonicalActualFrozenTotalMassFamily
            D fixed bankBase candidates preSelector activeSeed n * L n) =O[atTop]
      secondOrderScale ∧
    (fun n => logY n - h n * L n) =O[atTop]
      secondOrderScale



/-- Complete actual source package.  The constructor is retained because
it is exactly what makes the active/frozen decomposition valid eventually;
all other fields are genuine asymptotic estimates. -/
def BankPaperCanonicalSectionEightActualDataSourceLedger
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (guardedBase h logY : Nat -> Real) : Prop :=
  (∀ᶠ n : Nat in atTop,
    BankPaperCanonicalActualActiveMeasureConstructor
      (D n) (T n) (candidates n) (preSelector n) (activeSeed n)) ∧
    BankPaperCanonicalActualGuardedSmoothMassEstimate
      D activeSeed guardedBase ∧
    BankPaperCanonicalActualFrozenBaselineEstimates
      D fixed bankBase candidates preSelector activeSeed h logY

/-- Smaller source package for the canonical scaled active seed.  Its mass
identification is the unconditional theorem above, so only construction of
the actual placement and the three literal frozen-baseline estimates remain. -/
def BankPaperCanonicalSectionEightScaledActualDataSourceLedger
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (guardedBase h logY : Nat -> Real) : Prop :=
  (∀ᶠ n : Nat in atTop,
    BankPaperCanonicalActualActiveMeasureConstructor
      (D n) (T n) (candidates n) (preSelector n)
        (bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n))) ∧
    BankPaperCanonicalActualFrozenBaselineEstimates
      D fixed bankBase candidates preSelector
        (fun n => bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n))
      h logY



/-! ## Construction of the old Section 8 ledger -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionEightPrechargedLogConnector -/
section


/-!
# Paper-faithful precharged logarithmic target for Section 8

Section 8 removes the guarded central-anchor divisor before it forms the
ordinary-log target used by the smooth height ledger.  Thus the literal
quantity called `log Y` in the paper is

`log (centralTailProduct / centralAnchorDivisor)`,

not the logarithm of the complete central tail.  This file gives that
certificate-dependent target a total extension on an honest guarded tail
family.  On the finite prefix the extension agrees with the complete-tail
logarithm and the anchor log is zero; this convention changes no asymptotic
statement and makes their exact additive identity valid at every index.

The anchor logarithm is `O(secondOrderScale)` without any new analytic
assumption.  Its factorization has fixed support
`primesUpTo (2 * depth + 1)`, and exact divisibility bounds each supported
valuation by the corresponding upper-tail valuation.  The existing
fixed-prime valuation asymptotic then supplies the required finite sum
bound.  Subtracting this anchor log transfers both the centered complete-tail
estimate and any already-constructed Section 8 analytic ledger to the
paper's precharged logarithmic target.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperCanonicalGuardedTailFamily

/-- Total extension of the paper's residual logarithmic target.  Below the
honest tail threshold it is set equal to the complete-tail log, so no
realization or certificate is requested there. -/
def extendedPrechargedTailLogTarget
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (n : Nat) : Real :=
  if hn : N <= n then
    Real.log
      ((BankPaperCanonicalGuardedTailFamily.certificate
        F n hn).prechargedTailTarget : Real)
  else
    bankPaperCanonicalCentralTailLogTarget c n

/-- Total extension of the logarithm of the guarded central-anchor divisor.
The synthetic finite prefix is zero, complementary to
`extendedPrechargedTailLogTarget`. -/
def extendedCentralAnchorDivisorLog
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (n : Nat) : Real :=
  if hn : N <= n then
    Real.log
      (centralAnchorDivisor n (centralAnchorCutoff depth n)
        (BankPaperCanonicalGuardedTailFamily.certificate F n hn).q :
          Real)
  else
    0









end BankPaperCanonicalGuardedTailFamily

namespace GuardedCentralAnchorCertificate





end GuardedCentralAnchorCertificate

/-! ## The fixed-prime asymptotic bound -/



/-- A convenient explicit nonnegative constant for the fixed anchor-log
bound. -/
def bankPaperCanonicalAnchorLogBigOConstant
    (c : Real) (depth : Nat) : Real :=
  ∑ p ∈ primesUpTo (2 * depth + 1),
    (c / ((p - 1 : Nat) : Real) + 1) * Real.log (p : Real)



namespace BankPaperCanonicalGuardedTailFamily





end BankPaperCanonicalGuardedTailFamily

/-! ## Adapter for an already-constructed Section 8 ledger -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCombinedChargeTerminal -/
section


/-!
# The honest combined fixed-factor and precharge terminal

The precharge terminal leaves one twelfth of the `c-C0` valuation reserve
after the base bank has been charged on the fixed anchor support.  The
literal fixed exceptional factors use at most one twenty-fourth of that
reserve for a sufficiently small positive `deltaStar`; hence another
twenty-fourth remains after the complete selector charge.

Away from the fixed anchor support there is no anchor valuation.  For primes
up to `yNat`, the fixed exceptional estimate is combined with the already
proved moving-prime `o(secondOrderScale)` bank/Legendre cost.  Above `yNat`,
the exact donor-backing identity pays the complete selector charge directly
from the literal upper tail.  Thus the conclusion below is actual natural
divisibility, with no divisibility or charge-bound premise.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## An explicit admissible exceptional exponent -/

/-- The numerical range needed by the combined-charge argument.  The first
two clauses are the paper's positivity and endpoint-remainder range.  The
last clause allocates at most one forty-eighth of `c-C0` to the Selberg main
term; the vanishing endpoint remainder eventually uses a second
forty-eighth. -/
def IsPaperCombinedChargeDeltaStar (c deltaStar : ℝ) : Prop :=
  0 < deltaStar ∧
    deltaStar < 1 / 18 ∧
      paperExceptionalChargeConstant c *
          (deltaStar / paperExceptionalTheta) ≤
        (c - C0) / 48

/-- For `C0 < c`, a literal positive choice in the admissible range.  The
minimum keeps the analytic exponent below `1/18`, while the second entry
enforces the combined-charge budget without hiding any parameter-choice
premise. -/
def paperCombinedChargeDeltaStar (c : ℝ) : ℝ :=
  min (1 / 36)
    ((c - C0) * paperExceptionalTheta /
      (48 * paperExceptionalChargeConstant c))







/-! ## Uniform low-prime fixed charge -/



/-! ## Combined terminal -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTangentSlackIntegration -/
section


/-!
# Canonical parameter and endpoint-slack integration for Section 9

This module closes two finite interfaces which occur immediately before the
distributed tangent.

First, it makes one literal choice of `deltaStar` which simultaneously obeys
the complete fixed-factor/precharge budget and the clean-list head-gap
inequality.  Thus the charge terminal and the clean-list theorem no longer
need independently chosen exceptional exponents.

Second, it proves all of the endpoint classification and slack algebra.  A
clean common multiplier puts both endpoints in the guarded broad pool of one
complete rough row, and a nonsmooth such row is active nonexceptional.  On a
nonsmooth row, the displayed absolute bound for the constant correction
density implies the required two-sided selector margin.  On the smooth row,
the protected floor and active ceiling imply the same margin by elementary
addition.

The only construction fact not present in the preceding development is kept
as the explicit proposition
`BankPaperCanonicalGuardedEndpointSlackConstruction`: the actual guarded
selector must agree with the constant broad-row correction off the smooth row,
and its smooth coordinates must have the protected-plus-active decomposition.
No traffic, collision, clean-list cardinality, or final tangent conclusion is
included in that proposition.  The last theorem packages its consequence in
exactly the endpoint-closure and endpoint-slack shape consumed by the
candidate-parametric distributed assembly.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Filter Topology

noncomputable section

/-! ## One exceptional exponent for the charge and tangent arguments -/

/-- The combined admissibility condition used after all fixed choices: the
fixed-factor charge range together with the strict clean-list head-gap
inequality. -/
def IsPaperCombinedTangentDeltaStar
    (c : Real) (W : Nat) (r0 deltaStar : Real) : Prop :=
  IsPaperCombinedChargeDeltaStar c deltaStar ∧
    80 * tangentSelbergCanonicalMainConstant * deltaStar <
      tangentPaperHeadGap W r0

/-- A literal positive exponent small enough for both the combined charge and
the tangent clean-list loss.  The factor `160` leaves half of the fixed head
gap after multiplying by the clean-list constant `80`. -/
def paperCombinedTangentDeltaStar
    (c : Real) (W : Nat) (r0 : Real) : Real :=
  min (paperCombinedChargeDeltaStar c)
    (tangentPaperHeadGap W r0 /
      (160 * tangentSelbergCanonicalMainConstant))









namespace BankPaperRealization

/-! ## The explicit guarded nonsmooth correction -/

/-- Constant correction density on one literal guarded complete-rough row,
with the already proved postcharge quota as target. -/
def roughCanonicalGuardedPostchargeCorrectionDensity
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) (alpha beta L : Real) : Real :=
  bankPaperConstantPoolCorrectionDensity
    (R.roughCanonicalGuardedRow certificate deltaStar K label)
    (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
      W K label)
    (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
      alpha beta L)
    (R.roughCanonicalPostchargeRowTarget deltaStar label)

/-- The literal guarded-row constant correction used on a nonsmooth active
row. -/
def roughCanonicalGuardedPostchargeRowCorrectedWeight
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) (alpha beta L : Real)
    (a : Nat) : Real :=
  bankPaperConstantPoolCorrection
    (R.roughCanonicalGuardedRow certificate deltaStar K label)
    (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
      W K label)
    (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
      alpha beta L)
    (R.roughCanonicalPostchargeRowTarget deltaStar label) a





/-! ## Clean endpoints lie in the appropriate guarded broad pool -/



/-! ## The isolated protected/corrected-selector construction output -/

/-- Exact selector-construction output needed for endpoint slack.

On the smooth broad pool it exposes the frozen protected summand and the
remaining active summand, with their lower floor and upper ceiling.  On every
active nonsmooth row it says that the selector is the explicit constant-pool
correction and records the two numerical density inequalities which leave
`sigma / L` room.  These are precisely the two estimates cited in the paper;
all conversion from them to request-wise tangent slack is proved below. -/
def BankPaperCanonicalGuardedEndpointSlackConstruction
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta L sigma : Real)
    (selector : Nat -> Real) : Prop :=
  (∃ protectedPart active : Nat -> Real,
    ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1,
      selector a = protectedPart a + active a ∧
        sigma / L ≤ protectedPart a ∧
        0 ≤ active a ∧
        protectedPart a + active a ≤ 1 - sigma / L) ∧
  ∀ label,
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
      sigma / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| ≤ beta / L ∧
        beta / L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar W K label alpha beta L| ≤ 1 - sigma / L ∧
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar W K label,
          selector a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar W K label alpha beta L a



/-! ## Adapter to the candidate-parametric distributed tangent -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalProposition87EndpointSlack -/
section


/-!
# Proposition 8.7 endpoint slack on the guarded smooth row

The endpoint emitted by Proposition 8.7 is the literal sum of a frozen
ambient layer and an active exponential-family layer.  This file keeps that
overlap visible and proves the quantitative smooth-row part of the tangent
slack argument.

The active upper bound is not an assumption: it follows from the effective
box in `IsPaperProposition87Path`, the baseline `Cactive / L` ledger, and the
proved density-ratio estimate.  The sole construction datum not currently
present in the guarded-selector development is named
`BankPaperCanonicalGuardedSmoothProtectedWindow`: on every guarded smooth
broad coordinate the actual frozen ambient layer contains the protected
floor and is itself `O(1 / L)`.  This is exactly the finite realization of
the protected summand in the paper's smooth additive decomposition and
tangent endpoint-slack argument;
it does not assume endpoint slack or any tangent conclusion.

After that one window is supplied, the endpoint selector has the required
strict upper reserve, the existing nonsmooth constant-pool correction joins
it to form `BankPaperCanonicalGuardedEndpointSlackConstruction`, and the
existing clean-list candidate adapter applies without any further premise.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Filter

noncomputable section

/-! ## The one missing finite protected-layer estimate -/

/-- The precise protected-layer estimate still required from the literal
guarded smooth-row construction.

It concerns the actual frozen ambient layer used by Proposition 8.7, so it
allows protected tags to occupy the same numerical coordinates as active
sample tags.  The lower inequality is the protected floor.  The upper
inequality is the `O(1 / L)` frozen ledger on the whole guarded smooth broad
pool, including coordinates outside the active structured sub-sample. -/
def BankPaperCanonicalGuardedSmoothProtectedWindow
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (sigma Cfixed : Real) : Prop :=
  ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1,
    sigma / B.L <=
        BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∧
      BridgeData.frozenAmbientWeight fixedValue fixedWeight x <=
        Cfixed / B.L









/-! ## Quantitative active-coordinate bound at the actual P87 endpoint -/









/-! ## Smooth protected floor and strict upper reserve -/



namespace BankPaperRealization

/-! ## Join to the already proved nonsmooth correction -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothProtectedAdditiveRefinement -/
section


/-!
# Additive protected refinement on the guarded smooth broad pool

The literal raw selector already has constant broad weight `beta / L`.
The paper splits `beta = betaProt + betaAct`, freezes the first summand,
and replaces the second by the structured active seed.  The earlier
guarded continuation records only the resulting smooth-row integer quota;
it does not retain this pointwise additive identity.

This file restores that identity by an explicit local refinement.  On the
guarded smooth broad pool it sets

`preSelector = betaProt / L + activeSeedAmbient`,

and away from that pool it leaves an already constructed base selector
unchanged.  Thus nonsmooth corrected rows are untouched, while the actual
frozen remainder is definitionally the protected constant `betaProt / L`.
The existing raw-point theorem proves that this constant is precisely the
protected part of the paper's head-compatible raw broad weight.

This closes the positive-remainder and pre-selector-upper algebra without a
new selector assumption.  It deliberately does not claim that replacing an
arbitrary smooth row preserves its integer quota or prime moments: those are
the separate smooth-ledger/active-measure construction obligations.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The explicit protected layer and additive refinement -/

/-- The frozen protected layer on the literal guarded smooth broad pool. -/
def bankPaperCanonicalGuardedSmoothProtectedLayer
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
    (deltaStar betaProt : Real) (a : Nat) : Real :=
  if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 then
    betaProt / B.L
  else 0

@[simp] theorem bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
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
    {deltaStar betaProt : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
      deltaStar betaProt a = betaProt / B.L := by
  simp [bankPaperCanonicalGuardedSmoothProtectedLayer, ha]

@[simp] theorem bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
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
    {deltaStar betaProt : Real} {a : Nat}
    (ha : a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
      deltaStar betaProt a = 0 := by
  simp [bankPaperCanonicalGuardedSmoothProtectedLayer, ha]







/-- Replace only the guarded smooth broad coordinates by the literal
protected-plus-active sum; retain the supplied selector everywhere else. -/
def bankPaperCanonicalGuardedSmoothAdditiveRefinement
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
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (a : Nat) : Real :=
  if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 then
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
        deltaStar betaProt a +
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData activeSeed a
  else baseSelector a

@[simp] theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
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
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
        deltaStar betaProt baseSelector activeSeed a =
      betaProt / B.L +
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData activeSeed a := by
  simp [bankPaperCanonicalGuardedSmoothAdditiveRefinement,
    bankPaperCanonicalGuardedSmoothProtectedLayer, ha]

@[simp] theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
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
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
        deltaStar betaProt baseSelector activeSeed a = baseSelector a := by
  simp [bankPaperCanonicalGuardedSmoothAdditiveRefinement, ha]









/-! ## Derived active and pre-selector upper bounds -/









/-! ## Exact protected window and actual endpoint -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureAdditiveRefinement -/
section


/-!
# Actual active measure carried by the protected additive refinement

The canonical scaled active seed has exact literal mass `q`.  The protected
additive refinement places its ambient push-forward below the pre-selector
by construction: on every active coordinate it is the active weight plus
the nonnegative protected constant `betaProt / L`.

This file joins those two independent facts.  It proves the minimized
coordinate-fit predicate, candidate nonnegativity, and hence the full
actual-active-measure constructor on the literal guarded candidate set.
The first connector below records the older, stronger hypothesis that all
structured active values lie in the guarded *broad* correction pool.  That
hypothesis is false for the nonzero paper head vertices: the correction pool
is head-free.  The second half of the file therefore gives the literal
paper-faithful placement.  It extends the protected refinement only on the
finite structured active image, which already lies in the guarded smooth
row, and leaves the old refinement unchanged on its whole correction pool.
Its exact capacity predicate is discharged either pointwise or from the
existing cell-density/base-weight bound.

No rounded-selector transport is asserted here.  Replacing a smooth row
can change its integer row sum and prime moments; those equalities are the
separate additive-ledger boundary recorded by the refinement module.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Pointwise fit and feasibility -/





/-! ## Full guarded actual-measure constructor -/



/-! ## Structured placement on the whole guarded smooth row

The broad correction pool is the head-free part of the smooth row, whereas
the structured sample contains the nonzero paper head vertices as well.  The
following selector therefore keeps the protected refinement on its original
pool and, at every remaining structured active value, installs precisely the
active seed (the protected layer is zero there). -/







/-- Extend the protected additive refinement from the head-free correction
pool to the complete finite image of the structured sample.  On an active
value outside the correction pool, the protected layer reduces to zero. -/
def bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
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
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (a : Nat) : Real :=
  if a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData then
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
        deltaStar betaProt a +
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData activeSeed a
  else
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
      deltaStar betaProt baseSelector activeSeed a

@[simp] theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
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
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed a =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
          deltaStar betaProt a +
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData activeSeed a := by
  simp [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector, ha]

@[simp] theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
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
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∉ bankPaperCanonicalStructuredActiveValues B.sampleData) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed a =
      bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
        deltaStar betaProt baseSelector activeSeed a := by
  simp [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector, ha]







/-- Every structured coordinate carries its scaled active seed, whether or
not its head pattern is trivial. -/
@[simp] theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value
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
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (m : B.sampleData.Sample) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q)
          (B.sampleData.value m) =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
          deltaStar betaProt (B.sampleData.value m) +
        bankPaperCanonicalScaledActiveSeed T q m := by
  rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q)
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩),
    bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      B.sampleData T q hsep m]

/-- At a structured head cell outside the head-free correction pool, the
placement selector is exactly the active seed and has no protected summand. -/
@[simp] theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value_of_not_mem_pool
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
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (m : B.sampleData.Sample)
    (hnotPool : B.sampleData.value m ∉
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q)
          (B.sampleData.value m) =
      bankPaperCanonicalScaledActiveSeed T q m := by
  rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value
      (K := K) B R certificate deltaStar betaProt baseSelector T q hsep m,
    bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
      B R certificate hnotPool,
    zero_add]

/-! ## Exact frozen remainder of the corrected placement -/











/-! ## Exact coordinate capacity and selector feasibility -/

/-- Minimal finite capacity needed by the structured placement: the
protected constant fits at inactive correction coordinates, and the exact
protected-plus-seed weight fits at every tagged active coordinate. -/
def BankPaperCanonicalStructuredAdditivePlacementCapacity
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
    (T : BarycentricTarget B.sampleData) (q : Real) : Prop :=
  betaProt / B.L <= 1 ∧
    forall m : B.sampleData.Sample,
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
          deltaStar betaProt (B.sampleData.value m) +
        bankPaperCanonicalScaledActiveSeed T q m <= 1







/-! ## Full guarded constructor with the corrected placement -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSmoothAdditivePlacement -/
section


/-!
# Paper-faithful placement boundary for the guarded smooth refinement

The smooth bridge in the paper does not preserve the medium-prime moments
of an earlier provisional selector.  It freezes the protected layer,
redistributes the active mass while preserving the smooth-row ledger and
the moments outside the tangent band, and then fits the medium-prime band
moments.  Proposition 8.7 supplies that latter fit.

Accordingly, the pre-selector part of the actual endpoint theorem needs
only complete-row integrality and deficit support outside the medium-prime
band.  Its older statement accepted a full rounded-selector tangent input,
although the proof used only those two fields.  This file records the
weaker exact theorem, constructs the minimized ledger from the paper's two
literal zero-head cells, and proves the exact scaled structured head-cell
moments.  It then resolves the support boundary--the nonzero head cells lie
in the smooth row, not in its head-free correction subpool--by transporting
a signed ledger over the whole smooth row for the corrected selector.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization



/-! ## Exact finite algebra for the two zero-head pools -/

/-- A mass increment spread uniformly over one literal structured cell.
The cell is nonempty by `StructuredSampleData.cell_nonempty`, so its
cardinality denominator is nonzero. -/
def bankPaperCanonicalUniformCellIncrement
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (cell : Cell Head)
    (mass : Real) (m : D.Sample) : Real := by
  classical
  exact
    if D.cellOf m = cell then
      mass / Fintype.card (D.SampleAt cell)
    else 0



/-- The paper's two mass changes are made in the two physical copies of
the zero head vertex.  This definition changes no nonzero head cell. -/
def bankPaperCanonicalTwoZeroHeadCellRebalance
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real)
    (m : D.Sample) : Real :=
  seed m +
    bankPaperCanonicalUniformCellIncrement D (none, .minus) minusMass m +
    bankPaperCanonicalUniformCellIncrement D (none, .plus) plusMass m















/-! ## The head-free correction-pool ledger -/







/-- The selector immediately before the two-pool adjustment.  On the
head-free correction pool it consists of the frozen protected layer plus
the old structured active seed; all other coordinates are retained from an
arbitrary already-fixed selector. -/
def bankPaperCanonicalTwoZeroHeadCellSourceSelector
    {P : Finset Nat} {GeoBand : Type*}
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData (PaperHeadSimplex.Tag P) GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (outsideSelector : Nat -> Real) (a : Nat) : Real :=
  if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 then
    betaProt / B.L +
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a
  else outsideSelector a



/-! ## Structured head-cell realization -/



















/-! ## Exact support boundary -/



/-! ## Signed whole-smooth-row placement ledger -/

/-- The signed valuation change of the corrected structured placement on
the complete guarded smooth row.  Unlike the older correction-pool moment,
this sees every structured active coordinate, including the nonzero head
cells which cannot lie in the head-free broad pool. -/
def bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (q : Nat) : Real :=
  ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
    (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed a -
        baseSelector a) * (a.factorization q : Real)

/-- The exact signed ledger needed by the corrected whole-row placement.
It records that the structured image is supported on the guarded smooth
row, that the total smooth-row change is an integer, and that every fixed
head-prime moment is unchanged.  Medium-prime moments are deliberately not
constrained: Proposition 8.7 fits them later. -/
def BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) : Prop :=
  bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 ∧
    (∃ rowChange : Int,
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed a -
          baseSelector a)) = (rowChange : Real)) ∧
    ∀ q : Nat, q.Prime -> q <= B.sampleData.W ->
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q = 0











/-- Minimal selector state consumed before Proposition 8.7.

The structured placement needs only candidate feasibility, complete-rough-row
integrality, and exact selector-target agreement outside the medium-prime
band.  Prime-band balance and tangent residual bounds are deliberately absent:
the subsequent Proposition 8.7 endpoint constructs them. -/
structure BankPaperCanonicalSelectorSourceState
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    (selector : Nat -> Real) : Prop where
  feasible : ∀ a ∈ candidates,
    0 <= selector a ∧ selector a <= 1
  rowIntegral :
    BankPaperCanonicalSelectorRowIntegral n candidates selector
  deficitSupportedOnPrimeBand :
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
      R certificate fixed candidates selector



/-- The corrected whole-row prebridge placement statement: feasibility,
integer complete-row quotas, and exact agreement outside the tangent band.
It contains no medium-prime balance or prefix bound, since those are
produced by Proposition 8.7. -/
def BankPaperCanonicalGuardedStructuredAdditivePlacement
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) : Prop :=
  let placed :=
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
      B R certificate deltaStar betaProt baseSelector activeSeed
  (∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= placed a ∧ placed a <= 1) ∧
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      placed ∧
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      placed















end BankPaperRealization

/-! ## Weaker actual-endpoint preselector interface -/



namespace BankPaperRealization







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetConnector -/
section


/-!
# The finite post-height baseline target

After the integer height `d` has been selected, the paper chooses a fresh
finite baseline.  Its total active mass is

`q_n = q0 - d`,

its unnormalized head-prime moments are the prescribed values
`A_p^act`, and its normalized logarithmic height above `n` is
`A(d) / q_n`.

In the repository, this last statistic is
`BridgeData.physicalScore = log (m/n)`.  The separately named
`BridgeData.ordinaryLogScore` is `log m`, so its unnormalized moment is
`A(d) + q_n L`, not `A(d)`.  Both identities are proved below.

The two-zero-cell rounding placement used to obtain the integer row quota
need not itself have barycentric product form.  Accordingly this module
does not identify that placement with the new baseline.  It instead uses
the paper's actual `HeadSimplexReserve`, `PhysicalInterpolationTarget`, and
`BridgeData.barycentricTargetOfPaperData` constructors to build a new
`BarycentricTarget`, and proves its finite moment identities directly.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## Literal post-height scalar data -/

/-- The final active mass `q_n = q0 - d`. -/
def bankPaperCanonicalSectionNinePostHeightActiveMass
    (q0 : Real) (d : Int) : Real :=
  q0 - (d : Real)

@[simp] theorem bankPaperCanonicalSectionNinePostHeightActiveMass_eq
    (q0 : Real) (d : Int) :
    bankPaperCanonicalSectionNinePostHeightActiveMass q0 d =
      q0 - (d : Real) :=
  rfl

/-- The final unnormalized active logarithmic height above `n`,
`A(d) = A0 + d L`; formally this is the `physicalScore` moment. -/
def bankPaperCanonicalSectionNinePostHeightActiveHeight
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (A0 : Real) (d : Int) : Real :=
  A0 + (d : Real) * B.L

/-- The paper's final normalized logarithmic height above `n`,
`A(d) / q_n`.  This is the mean of `BridgeData.physicalScore = log(m/n)`. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalLogMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (q0 A0 : Real) (d : Int) : Real :=
  bankPaperCanonicalSectionNinePostHeightActiveHeight B A0 d /
    bankPaperCanonicalSectionNinePostHeightActiveMass q0 d



/-- The physical-score target passed to `PhysicalInterpolationTarget`.
The paper's `A(d)` is already the active logarithmic height above `n`, so
no further subtraction of `L` occurs here. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (q0 A0 : Real) (d : Int) : Real :=
  bankPaperCanonicalSectionNinePostHeightPhysicalLogMean B q0 A0 d

/-! ## Genuine reserve and interpolation inputs -/

/-- The finite numerical inputs required to choose the post-height
barycentric target.

The head fields are precisely the coordinatewise interior conditions for
the simplex `{0, E e_p}` at total mass `q0-d`.  The two physical fields say
that the `log(m/n)` target `A(d)/(q0-d)` lies strictly between the two
selected physical pools.  No target, seed, moment, or placement conclusion
is stored in this structure. -/
structure BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (q0 A0 : Real) (d : Int) (exponent : Nat)
    (activeHeadTarget : {p : Nat // p ∈ P} → Real) where
  exponent_pos : 0 < exponent
  activeMass_pos :
    0 < bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  headMargin : Real
  headMargin_pos : 0 < headMargin
  vertex_margin : ∀ p,
    headMargin ≤
      activeHeadTarget p /
        ((exponent : Real) *
          bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
  zero_margin :
    headMargin ≤
      1 - ∑ p : {p : Nat // p ∈ P},
        activeHeadTarget p /
          ((exponent : Real) *
            bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
  physicalEta : Real
  physicalEta_pos : 0 < physicalEta
  minus_below :
    Real.log (I.upper .minus) ≤
      bankPaperCanonicalSectionNinePostHeightPhysicalMean B q0 A0 d -
        physicalEta
  plus_above :
    bankPaperCanonicalSectionNinePostHeightPhysicalMean B q0 A0 d +
        physicalEta ≤
      Real.log (I.lower .plus)

/-! ## Constructed paper data -/

/-- The literal post-height head-simplex reserve. -/
def bankPaperCanonicalSectionNinePostHeightHeadReserve
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData (PaperHeadSimplex.Tag P) Band}
    {I : PhysicalIntervals}
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    HeadSimplexReserve P where
  exponent := exponent
  exponent_pos := H.exponent_pos
  activeMass :=
    bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  activeMass_pos := H.activeMass_pos
  target := activeHeadTarget
  margin := H.headMargin
  margin_pos := H.headMargin_pos
  vertex_margin := H.vertex_margin
  zero_margin := H.zero_margin

/-- The literal post-height physical interpolation target. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalTarget
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData (PaperHeadSimplex.Tag P) Band}
    {I : PhysicalIntervals}
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    PhysicalInterpolationTarget I where
  mu := bankPaperCanonicalSectionNinePostHeightPhysicalMean B q0 A0 d
  eta := H.physicalEta
  eta_pos := H.physicalEta_pos
  minus_below := H.minus_below
  plus_above := H.plus_above

/-- The paper-faithful post-height barycentric target `Tpost`. -/
def bankPaperCanonicalSectionNinePostHeightTarget
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    BarycentricTarget B.sampleData :=
  B.barycentricTargetOfPaperData I hlo hhi
    (bankPaperCanonicalSectionNinePostHeightHeadReserve H)
    (bankPaperCanonicalSectionNinePostHeightPhysicalTarget H)

/-- The scaled post-height seed attached to `Tpost`. -/
def bankPaperCanonicalSectionNinePostHeightActiveSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    B.sampleData.Sample → Real :=
  bankPaperCanonicalScaledActiveSeed
    (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
    (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)

/-! ## Exact mass and head moments -/

/-- The constructed scaled seed has total mass exactly `q_n = q0-d`. -/
@[simp] theorem
    bankPaperCanonicalSectionNinePostHeight_literalActiveMass_activeSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) =
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d := by
  exact
    bankPaperCanonicalLiteralActiveMass_scaledActiveSeed
      (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)



/-! ## Exact ordinary-log moment -/













/-! ## Combined finite target constructor -/



/-! ## Quantitative target margin -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellProducerConnector -/
section


/-!
# Concrete producer and mass choice for the two zero-head cells

This file isolates the two finite facts needed by the structured
prebridge producer.

First, a sample in the zero head cell is coprime to the complete head
modulus.  Hence it belongs to the guarded broad correction pool as soon as
its physical interval lies below the literal broad cutoff and every sample
value is known pointwise to avoid the canonical guard set.  In particular, no
cardinality surplus theorem is used to prove membership.

Second, the height adjustment has a canonical symmetric realization: put
`-d / 2` in each of the two physical zero-head cells.  Its total change is
the integer `-d`, and the exact lower and upper coordinate-capacity
conditions reduce to two scalar inequalities involving the old total cell
mass and the guard-deleted cell cardinality.

The nearest-integer normalization from `qTilde` to `q0` is recorded
separately.  That first change is generally real rather than integral; the
integer prebridge ledger applies to the subsequent height change from
`q0` to `q0 - d`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeSums

noncomputable section

namespace BankPaperRealization

/-! ## The fixed physical intervals eventually lie below the broad cutoff -/





/-! ## The zero head pattern produces head-freeness -/









/-! ## Canonical symmetric mass choices -/

/-- Half of the integer height change, assigned to each physical copy of
the zero head cell. -/
def bankPaperCanonicalSymmetricHeightCellMass (d : Int) : Real :=
  -(d : Real) / 2

@[simp] theorem bankPaperCanonicalSymmetricHeightCellMass_add_self
    (d : Int) :
    bankPaperCanonicalSymmetricHeightCellMass d +
        bankPaperCanonicalSymmetricHeightCellMass d =
      ((-d : Int) : Real) := by
  unfold bankPaperCanonicalSymmetricHeightCellMass
  push_cast
  ring



/-- The symmetric normalization-and-height change relative to the actual
post-guard mass `qTilde`.  Unlike the height-only change, this quantity is
not asserted to be an integer. -/
def bankPaperCanonicalSymmetricInitialAndHeightCellMass
    (mFrozen qTilde : Real) (d : Int) : Real :=
  (bankPaperCanonicalSmoothActiveMassAt mFrozen qTilde d - qTilde) / 2

@[simp] theorem bankPaperCanonicalSymmetricInitialAndHeightCellMass_add_self
    (mFrozen qTilde : Real) (d : Int) :
    bankPaperCanonicalSymmetricInitialAndHeightCellMass
          mFrozen qTilde d +
        bankPaperCanonicalSymmetricInitialAndHeightCellMass
          mFrozen qTilde d =
      bankPaperCanonicalSmoothActiveMassAt mFrozen qTilde d - qTilde := by
  unfold bankPaperCanonicalSymmetricInitialAndHeightCellMass
  ring





/-! ## Exact finite coordinate capacity -/















end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellOuterCapacityConnector -/
section


/-!
# Outer asymptotic capacity for the two zero-head cells

The finite two-cell producer reduces feasibility to one lower and one upper
scalar inequality in each physical sign.  This file supplies those
inequalities from the already constructed paper-scale inputs.

The actual post-guard mass is bounded below and above on the
`secondOrderScale` scale.  The combined nearest-integer and height change is
little-o of that scale.  A uniform positive cell-mass margin therefore
absorbs every removal.  On the other side, `secondOrderScale = o(n)` and the
canonical guard-deleted cell-density theorem leave enough room below the
protected ceiling.

The terminal statements use the same local canonical-data equality and
cell-mass-margin argument as Proposition 8.7.  No new asymptotic predicate or
family-identification assumption is introduced.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Scale and cell-mass preliminaries -/







/-! ## The combined cell change is negligible -/





/-! ## A common positive density for the two zero-head cells -/

/-- A fixed density valid simultaneously for the two physical signs of the
zero-head cell. -/
def bankPaperCanonicalZeroHeadCellDensityFloor
    {P : Finset Nat}
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals) : Real :=
  min
      (paperCellDensity (Phead none)
        (I.lower .minus) (I.upper .minus))
      (paperCellDensity (Phead none)
        (I.lower .plus) (I.upper .plus)) / 4





/-! ## Outer scalar capacity -/



/-! ## Feeding the finite producer -/



end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalBridgeRelevantGuardLedger -/
section


/-!
# The bridge-relevant numerical-guard ledger

The literal rough construction uses the global five-family guard

`anchors ∪ fixedExceptional ∪ donors ∪ baseState ∪ alternateState`.

That global set is not the guard census used by the smooth bridge.  Fixed
exceptional factors and donors lie above `2n`, while the two bank endpoint
states have a prime complete-rough label above `yNat n`.  Hence, on the
positive `yNat n`-smooth values at most `2n` which occur in every bridge
cell, the global guard agrees exactly with the promoted residual anchors
whose base prime is at most `yNat n`.

This file makes that relevant guard literal.  Its cardinality is at most
`yNat n`, so it fits in the promoted part of `GuardSlot`.  We adjoin the
harmless sentinel value `0` before enumerating it.  This avoids a false
nonemptiness requirement on an image of a nonempty slot type; the sentinel
cannot occur in a structured cell.  Two promoted slots per smooth integer
therefore suffice uniformly, and no bank slot is required.

Thus the correct replacement for a global
`ledger.guards = roughCanonicalGuardSet` hypothesis is the eventual local
predicate `BankPaperCanonicalBridgeGuardAgreement`.  A total fixed ledger
family, chosen before any realization or certificate, uses a harmless
zero-valued fallback on the finite prefix where the relevant guard does not
fit.  Once a realization exists the paper census forces the canonical branch,
so this fixed family agrees with the global rough guard on the bridge
universe.  The concrete elimination interfaces below give equality after
deleting guards from a raw cell, equality after restricting deletion to
structured active values, and pointwise avoidance of the full guard.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Enumerating an arbitrary finite guard together with a zero sentinel -/

/-- An embedding of a finite guard-with-sentinel into a large enough guard
slot type. -/
noncomputable def guardFinsetWithZeroEmbedding
    {n Cprom Cbank : Nat} (guards : Finset Nat)
    (hcard :
      (insert 0 guards).card <=
        Fintype.card (GuardSlot n Cprom Cbank)) :
    (insert 0 guards : Finset Nat) ↪ GuardSlot n Cprom Cbank :=
  Classical.choice <| Function.Embedding.nonempty_of_card_le <| by
    simpa only [Fintype.card_coe] using hcard

/-- Enumerate a finite guard in a concrete `Ledger`, padding every unused
slot by the sentinel value zero. -/
noncomputable def ledgerOfFinsetWithZero
    {n Cprom Cbank : Nat} (guards : Finset Nat)
    (hcard :
      (insert 0 guards).card <=
        Fintype.card (GuardSlot n Cprom Cbank)) :
    Ledger n Cprom Cbank where
  value :=
    Function.extend
      (guardFinsetWithZeroEmbedding guards hcard)
      (fun a : (insert 0 guards : Finset Nat) => a.1)
      (fun _ => 0)



/-! ## The literal bridge-relevant subfamily -/

/-- The only numerical guards visible on positive `yNat n`-smooth values
at most `2n`: promoted residual anchors whose base prime is at most the
smooth cutoff. -/
def roughCanonicalBridgeRelevantGuardSet
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (_certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) : Finset Nat :=
  bankPaperCanonicalSmoothResidualAnchorPool n
    (centralAnchorCutoff depth n) (yNat n)

/-- The relevant guard has the paper-sized pointwise census. -/
theorem roughCanonicalBridgeRelevantGuardSet_card_le
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    (roughCanonicalBridgeRelevantGuardSet certificate).card <= yNat n := by
  exact bankPaperCanonicalSmoothResidualAnchorPool_card_le
    n (centralAnchorCutoff depth n) (yNat n)





/-- A realization- and certificate-independent ledger family for the bridge.
When the relevant guard fits in the literal two-promoted-slot census it is
enumerated exactly.  The zero-valued fallback makes the family total on the
irrelevant finite prefix. -/
noncomputable def roughCanonicalBridgeRelevantLedgerFamily
    (depth n : Nat) : Ledger n 2 0 :=
  let guards :=
    bankPaperCanonicalSmoothResidualAnchorPool n
      (centralAnchorCutoff depth n) (yNat n)
  if hcard :
      (insert 0 guards).card <=
        Fintype.card (GuardSlot n 2 0) then
    ledgerOfFinsetWithZero guards hcard
  else
    ⟨fun _ => 0⟩

namespace BankPaperRealization



/-! ## The canonical two-promoted-slot ledger -/

/-- After adjoining the zero sentinel, the relevant guard fits in the
literal two-promoted-slot census. -/
theorem roughCanonicalBridgeRelevantGuardSet_insert_zero_card_le_guardSlot
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    (insert 0
        (roughCanonicalBridgeRelevantGuardSet certificate)).card <=
      Fintype.card (GuardSlot n 2 0) := by
  have hrelevant :=
    roughCanonicalBridgeRelevantGuardSet_card_le certificate
  have hyOne : 1 <= yNat n := by
    have hySix := R.six_le_yNat
    omega
  rw [card_guardSlot]
  calc
    (insert 0
        (roughCanonicalBridgeRelevantGuardSet certificate)).card <=
        (roughCanonicalBridgeRelevantGuardSet certificate).card + 1 :=
      Finset.card_insert_le _ _
    _ <= yNat n + 1 := Nat.add_le_add_right hrelevant 1
    _ <= 2 * yNat n + 0 * yNat n * scaleSlots n * 3 := by omega

/-- The canonical bridge ledger.  It enumerates the relevant guard plus the
zero sentinel in `GuardSlot n 2 0`. -/
noncomputable def roughCanonicalBridgeRelevantLedger
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    Ledger n 2 0 :=
  ledgerOfFinsetWithZero
    (roughCanonicalBridgeRelevantGuardSet certificate)
    (R.roughCanonicalBridgeRelevantGuardSet_insert_zero_card_le_guardSlot
      certificate)





/-- The exact local interface needed by the bridge: its ledger and the
global rough guard agree on all possible structured values. -/
def BankPaperCanonicalBridgeGuardAgreement
    {c : Real} {depth n h Cprom Cbank : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (G : Ledger n Cprom Cbank)
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) : Prop :=
  forall a : Nat, 0 < a -> a <= 2 * n ->
    a ∈ Nat.smoothNumbers (yNat n + 1) ->
      (a ∈ G.guards ↔
        a ∈ R.roughCanonicalGuardSet certificate deltaStar)









/-! ## Equality on raw cells and structured active values -/













end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellMeasureConnector -/
section


/-!
# Actual-measure closure for the two-zero-cell placement

The symmetric Section 8 height change is not, in general, another scaled
`BarycentricTarget` baseline: it changes only the two physical copies of the
zero head cell.  The actual bridge therefore keeps the original scaled seed.

This file proves the missing coordinate fit for that seed.  The height loss
is `o(n / log n)`, whereas either zero-head cell has positive density.  After
uniform spreading, the loss at one tagged coordinate is consequently
absorbed by the existing protected reserve `betaProt / L`.  Every nonzero
head coordinate is unchanged.  These two facts give the literal
`BankPaperCanonicalActualActiveMeasureConstructor`.
-/

open Filter Topology Asymptotics Set
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The protected reserve absorbs a little-o cell loss -/





/-! ## Finite coordinate fit -/













/-! ## Exact baseline seed on the actual-mass bridge -/

/-- The lower-level active-mass bridge can be constructed from `q > 0`
before `Hmeasure` is known, so there is no circularity.  Its baseline weight
is definitionally the original scaled seed, closing the endpoint consumer's
`hseed` argument. -/
@[simp] theorem
    bankPaperCanonicalActiveMassBridgeData_baseWeight_scaledSeed
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta)
    (m : D.Sample) :
    (bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw).baseline.baseWeight m =
        bankPaperCanonicalScaledActiveSeed T q m := by
  rw [bankPaperCanonicalActiveMassBridgeData_baseline,
    T.activeMassBaseline_baseWeight]
  rfl

/-! ## Eventual Section 8 inputs for the finite constructor -/







end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalGlobalCorrectedSourceSelector -/
section


/-!
# Global corrected source selector

The original two-zero-cell source selector uses the protected-plus-active
weight on the smooth guarded broad pool and the old active ambient weight
everywhere else.  That is the right source for the Section 8 moment ledger,
but it is not the selector required by the Section 9 endpoint theorem on a
nonsmooth active row.

This file makes a rowwise compatible global replacement.  Off the smooth
broad pool it keeps the old ambient weight on complete-rough label `1`, and
uses the already constructed postcharge corrected row weight on active
nonexceptional labels, while exceptional labels are zero.  Consequently:

* once structured active values are known to lie in the complete smooth
  row, the source still agrees with the old ambient weight at every such
  coordinate outside the smooth broad pool, so the existing two-zero-cell
  prebridge ledger applies unchanged;
* every active nonsmooth guarded broad coordinate is exactly the explicit
  postcharge corrected row weight; and
* after structured placement, the two exact `hpreNonsmooth` and
  `hpreUpper` interfaces consumed by the endpoint-slack theorem are exposed.

The exact corrected-weight identity uses the literal active-nonexceptional
classification; preservation by structured placement additionally uses
smooth-row support of the structured active values.  The smooth upper theorem
honestly retains the pointwise `O(1 / L)` upper bound for the placement seed.
Existing two-zero-cell capacity only bounds the resulting selector by `1`;
it does not imply this sharper estimate.

On an active nonexceptional complete label, the outside selector intentionally
uses the full corrected-row weight, including its raw-weight branch outside
the guarded broad correction pool.  This is the rowwise selector whose total
is controlled by the postcharge construction, rather than a pointwise-only
patch of the old ambient source.  A rounded-selector input for this global
source remains explicit below; it is not manufactured from local slack.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Arbitrary-seed push-forward -/



/-! ## The global outside selector -/

/-- Off the smooth correction pool, retain the old ambient active weight on
the complete smooth row, vanish on exceptional nonsmooth rows, and use the
explicit corrected weight on active nonexceptional rows. -/
def bankPaperCanonicalGlobalCorrectedOutsideSelector
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

/-- On the complete smooth row, the global outside selector is exactly the
old active ambient weight. -/
@[simp] theorem bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_ambient_of_mem_smoothRow
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
    {deltaStar alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
        B R certificate deltaStar alpha beta oldSeed a =
      bankPaperCanonicalActiveSeedAmbientWeight
        B.sampleData oldSeed a := by
  have hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1 :=
    (mem_completeRoughRowFiber.mp ha).2
  simp [bankPaperCanonicalGlobalCorrectedOutsideSelector, hlabel]

/-- A guarded broad coordinate in a nonsmooth row cannot also lie in the
complete smooth row. -/
theorem roughCanonicalGuardedBroadCorrectionPool_not_mem_smoothRow_of_ne_one
    {c deltaStar : Real} {depth n W K label a : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label) :
    a ∉ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  intro haSmooth
  have haLabel : a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K label :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar W K label ha
  have hsmoothEq := (mem_completeRoughRowFiber.mp haSmooth).2
  have hlabelEq := (mem_completeRoughRowFiber.mp haLabel).2
  exact hlabel (hlabelEq.symm.trans hsmoothEq)

/-- On an active nonexceptional guarded broad pool, the global outside
selector is the explicit postcharge corrected weight for that literal row
label. -/
@[simp] theorem bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_corrected_of_mem_nonsmoothPool
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K label) :
    bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
        B R certificate deltaStar alpha beta oldSeed a =
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar B.sampleData.W K label alpha beta B.L a := by
  have haRow : a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K label :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar B.sampleData.W K label ha
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp haRow).2
  have hnonexceptional :
      ¬ RoughCanonicalExceptionalLabel
        B.sampleData.n deltaStar label :=
    not_lt_of_ge hactive.2
  simp [bankPaperCanonicalGlobalCorrectedOutsideSelector, haLabel,
    hactive.1, hnonexceptional]

/-! ## The global source and its exact rowwise values -/

/-- The protected smooth source joined to the explicit nonsmooth postcharge
correction, while retaining the old ambient source on the remainder of the
complete smooth row. -/
def bankPaperCanonicalGlobalCorrectedSourceSelector
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
      (bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
        B R certificate deltaStar alpha beta oldSeed)

/-- On the guarded smooth broad pool, the global source retains the exact
protected-plus-old-active formula used by the Section 8 ledger. -/
@[simp] theorem bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_smoothPool
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
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a =
      betaProt / B.L +
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
  simp [bankPaperCanonicalGlobalCorrectedSourceSelector,
    bankPaperCanonicalTwoZeroHeadCellSourceSelector, ha]

/-- On every active nonexceptional guarded broad pool, the global source is
exactly the explicit corrected row selector. -/
@[simp] theorem bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_nonsmoothPool
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a =
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar B.sampleData.W K label alpha beta B.L a := by
  have hnotSmoothRow :
      a ∉ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    R.roughCanonicalGuardedBroadCorrectionPool_not_mem_smoothRow_of_ne_one
      certificate hactive.1 ha
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    exact hnotSmoothRow
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth)
  rw [bankPaperCanonicalGlobalCorrectedSourceSelector,
    bankPaperCanonicalTwoZeroHeadCellSourceSelector, if_neg hnotSmoothPool]
  exact
    bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_corrected_of_mem_nonsmoothPool
      B R certificate oldSeed hactive ha

/-! ## Compatibility with the Section 8 prebridge ledger -/



/-! ## Full Section 8 placement with the global source -/







/-! ## Exact endpoint-slack inputs after structured placement -/









end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasStieltjesKernel -/
section


/-!
# The compact Dickman kernel for the de Bruijn signed functional

This file isolates the only nonsmooth point in the integration-by-parts
identification of the Saias normal form.  The repository's finite Dickman
function is `1` to the left of the first face, so its right derivative as a
function of the Stieltjes variable is zero when the logarithmic coordinate
is exactly `1`.  This is different at one point from
`roughSaiasDickmanDerivative`, whose value at `1` is the *Dickman-coordinate*
right limit `-1`.

The open-face representative below has value zero at that corner.  It gives
an honest right derivative for the Stieltjes test function; changing it back
to `roughSaiasDickmanDerivative` later is an almost-everywhere, one-point
change.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-- Zero on the closed initial face, and the Dickman delay derivative on
the open noninitial faces.  In particular its value at `1` is zero. -/
noncomputable def roughSaiasOpenFaceDickmanDerivative (u : ℝ) : ℝ :=
  if u ≤ 1 then 0 else -rho (u - 1) / u

@[simp]
theorem roughSaiasOpenFaceDickmanDerivative_of_le_one
    {u : ℝ} (hu : u ≤ 1) :
    roughSaiasOpenFaceDickmanDerivative u = 0 := by
  simp [roughSaiasOpenFaceDickmanDerivative, hu]



@[simp]
theorem roughSaiasOpenFaceDickmanDerivative_one :
    roughSaiasOpenFaceDickmanDerivative 1 = 0 := by
  simp [roughSaiasOpenFaceDickmanDerivative]









/-! ## Real logarithmic coordinate and Stieltjes test function -/

/-- Logarithmic Dickman coordinate in the real Stieltjes variable. -/
noncomputable def roughSaiasStieltjesCoordinate
    (x y t : ℝ) : ℝ :=
  (Real.log x - Real.log t) / Real.log y

/-- The Abel test function whose integer values are the atoms
`x*rho(log(x/n)/log y)/n`. -/
noncomputable def roughSaiasStieltjesTest
    (x y t : ℝ) : ℝ :=
  x * rho (roughSaiasStieltjesCoordinate x y t) / t

/-- The honest right derivative of `roughSaiasStieltjesTest` on positive
Stieltjes variables. -/
noncomputable def roughSaiasStieltjesTestRightDerivative
    (x y t : ℝ) : ℝ :=
  x * roughSaiasOpenFaceDickmanDerivative
        (roughSaiasStieltjesCoordinate x y t) *
      (-1 / (t * Real.log y)) / t -
    x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2





/-! ## The corner-safe right derivative -/





/-! ## Integrability of the right derivative -/









end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasContinuousBuchstab -/
section


/-!
# The compact base-free functional behind continuous Buchstab

The de Bruijn approximation has a base-free Stieltjes description against

`d (floor t / t)`.

Since `t \mapsto floor t / t` is not monotone, Mathlib's positive
`StieltjesFunction.measure` is not the right primitive here.  On a finite
interval its signed action is instead represented explicitly as

`sum f(n) / n - integral f(t) floor(t) / t^2 dt`.

This file introduces that atom-minus-density functional, together with the
zero extension of the Dickman function which supplies its exact support.
The cutoff is kept as an explicit natural number: in the continuous
Buchstab identity the outer cutoff can then remain fixed while the first
argument changes from `x` to `x / s`.  The support lemmas below show that
this choice is harmless.

The eventual identification with `roughSaiasLambdaNormalForm` is a separate
finite Abel calculation.  In particular, no equality with the Stieltjes
normalization is built into any definition in this file.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The supported Dickman profile -/

/-- The Dickman function with the classical zero extension on the negative
half-line.  The finite project function `rho` itself is deliberately equal
to one to the left of its first face, so this separate wrapper is needed in
the Stieltjes representation. -/
noncomputable def roughSaiasZeroExtendedRho (u : ℝ) : ℝ :=
  if u < 0 then 0 else rho u

@[simp]
theorem roughSaiasZeroExtendedRho_of_neg
    {u : ℝ} (hu : u < 0) :
    roughSaiasZeroExtendedRho u = 0 := by
  simp [roughSaiasZeroExtendedRho, hu]



@[simp]
theorem roughSaiasZeroExtendedRho_zero :
    roughSaiasZeroExtendedRho 0 = 1 := by
  simp [roughSaiasZeroExtendedRho]







/-- The base-free Dickman profile on which the compact Stieltjes functional
acts. -/
noncomputable def roughSaiasStieltjesDickmanProfile
    (x y t : ℝ) : ℝ :=
  x * roughSaiasZeroExtendedRho
    (Real.log (x / t) / Real.log y)





@[simp]
theorem roughSaiasStieltjesDickmanProfile_self
    {x y : ℝ} (hx : x ≠ 0) :
    roughSaiasStieltjesDickmanProfile x y x = x := by
  unfold roughSaiasStieltjesDickmanProfile
  rw [div_self hx, Real.log_one, zero_div,
    roughSaiasZeroExtendedRho_zero, mul_one]









@[simp]
theorem roughSaiasStieltjesTest_self
    {x y : ℝ} (hx : x ≠ 0) :
    roughSaiasStieltjesTest x y x = 1 := by
  unfold roughSaiasStieltjesTest roughSaiasStieltjesCoordinate
  rw [sub_self, zero_div, rho_zero, mul_one, div_self hx]

/-! ## The finite atom-minus-density functional -/

/-- The absolutely continuous density in
`d (floor t / t)`: its sign is subtracted in the functional below. -/
noncomputable def roughSaiasFloorDensity (t : ℝ) : ℝ :=
  ((⌊t⌋₊ : ℕ) : ℝ) / t ^ (2 : ℕ)



/-- Atomic part of the compact signed Stieltjes functional. -/
noncomputable def roughSaiasStieltjesAtomPart
    (R : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 R, f (n : ℝ) / (n : ℝ)

/-- Absolutely continuous part of the compact signed Stieltjes functional. -/
noncomputable def roughSaiasStieltjesDensityPart
    (R : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
    f t * roughSaiasFloorDensity t

/-- The compact realization of integration against
`d (floor t / t)`. -/
noncomputable def roughSaiasFiniteStieltjesFunctional
    (R : ℕ) (f : ℝ → ℝ) : ℝ :=
  roughSaiasStieltjesAtomPart R f -
    roughSaiasStieltjesDensityPart R f

@[simp]
theorem roughSaiasStieltjesAtomPart_zero (R : ℕ) :
    roughSaiasStieltjesAtomPart R (fun _ => 0) = 0 := by
  simp [roughSaiasStieltjesAtomPart]

@[simp]
theorem roughSaiasStieltjesDensityPart_zero (R : ℕ) :
    roughSaiasStieltjesDensityPart R (fun _ => 0) = 0 := by
  simp [roughSaiasStieltjesDensityPart]

@[simp]
theorem roughSaiasFiniteStieltjesFunctional_zero (R : ℕ) :
    roughSaiasFiniteStieltjesFunctional R (fun _ => 0) = 0 := by
  simp [roughSaiasFiniteStieltjesFunctional]









/-! ## Cutoff independence -/







/-! ## A real-base de Bruijn functional -/

/-- The real-base de Bruijn functional with an explicit compact cap. -/
noncomputable def roughSaiasLambdaStieltjesWithCutoff
    (R : ℕ) (x y : ℝ) : ℝ :=
  roughSaiasFiniteStieltjesFunctional R
    (roughSaiasStieltjesDickmanProfile x y)

/-- Canonical real-base version, using the least natural cap above `x`. -/
noncomputable def roughSaiasLambdaStieltjes
    (x y : ℝ) : ℝ :=
  roughSaiasLambdaStieltjesWithCutoff ⌈x⌉₊ x y













@[simp]
theorem roughSaiasLambdaStieltjes_nat
    (X : ℕ) (y : ℝ) :
    roughSaiasLambdaStieltjes (X : ℝ) y =
      roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) y := by
  simp [roughSaiasLambdaStieltjes]

/-- The integrand which appears after applying the continuous Buchstab
identity pointwise under the fixed compact functional. -/
noncomputable def roughSaiasContinuousBuchstabProfile
    (x s t : ℝ) : ℝ :=
  roughSaiasStieltjesDickmanProfile (x / s) s t /
    Real.log s



























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasEndpointApproximation -/
section


/-!
# A closed inverse-log endpoint approximation for the Saias normal form

The repository already proves a uniform compact estimate for
`Psi(X,y) - X*rho(log X/log y)` and proves separately that
`|G_y-rho| <= 1/log y`.  Combining those two closed estimates gives a
concrete witness for `RoughSaiasEndpointApproximationUpToFive` with rate
`(K+1)/log y`.

This is an unconditional endpoint theorem about the already formalized
normal form.  It is deliberately not described as the sharper cited
Hildebrand--Tenenbaum--Saias estimate: its inverse-log rate is too large for
the final paper-scale absorption.  The exact reverse recurrence at the end
of this file isolates the normal-form prime-sum defect whose sharper control
would supply that missing gain.  The final section makes that claim precise:
an inverse-log-square bound for this explicit defect, together with the
already proved prime contraction, conditionally gives the paper-absorbable
endpoint rate `10*C/log(y)^2`.  Thus the coarse closed witness and the sole
sharp analytic input have different names and cannot be confused downstream.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Named witnesses from the closed Dickman endpoint theorem -/











/-! ## Identification with the formal normal form -/



/-! ## Closed endpoint envelope -/





/-! ## Exact reverse recurrence for the normal-form error -/

/-- Failure of the formal normal form to obey the reverse largest-prime
recurrence exactly.  Unlike the endpoint error itself, this is a completely
explicit prime-sum consistency defect. -/
noncomputable def roughSaiasReverseNormalFormDefect
    (X y Z : ℕ) : ℝ :=
  roughSaiasNaturalMain X Z - roughSaiasNaturalMain X y -
    ∑ p ∈ roughReversePrimeInterval y Z,
      roughSaiasNaturalMain (X / p) p





/-! ## The sole sharp analytic input and its endpoint consequence -/

/-- The inverse-log-square defect estimate needed for the paper-strength
endpoint envelope.  This proposition contains only the explicit normal form
`M(X,y)=X*G_y(log X/log y)` and a finite prime sum; in particular it contains
no friable count and no endpoint error. -/
def RoughSaiasReverseNormalFormDefectInvLogSqBound
    (C : ℝ) (Y₀ : ℕ) : Prop :=
  ∀ {X y : ℕ}, Y₀ ≤ y → 2 ≤ y → y < X →
    Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
    |roughSaiasReverseNormalFormDefect X y X| ≤
      C * (X : ℝ) / Real.log (y : ℝ) ^ 2

/-- A fixed threshold for the already proved reciprocal-log prime
contraction. -/
noncomputable def roughSaiasPrimeInvLogContractionCutoff : ℕ :=
  Classical.choose
    FriableAsymptotic.exists_primeInvLogSum_contraction_threshold



/-- The extra reciprocal logarithm that appears in an inverse-log-square
endpoint induction. -/
noncomputable def roughSaiasPrimeInvLogSqSum (y X : ℕ) : ℝ :=
  ∑ p ∈ roughReversePrimeInterval y X,
    1 / ((p : ℝ) * Real.log (p : ℝ) ^ 2)



/-- The explicit inverse-log-square endpoint rate obtained from the sharp
normal-form defect. -/
noncomputable def roughSaiasInvLogSqEndpointRate
    (C : ℝ) (y : ℕ) : ℝ :=
  10 * C / Real.log (y : ℝ) ^ 2

/-- The original defect threshold enlarged only by the already closed prime
contraction threshold. -/
noncomputable def roughSaiasInvLogSqEndpointCutoff (Y₀ : ℕ) : ℕ :=
  max Y₀ roughSaiasPrimeInvLogContractionCutoff





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSignedFractionalAbel -/
section


/-!
# Signed fractional correction and finite Abel decomposition for the Saias defect

This file goes one level below
`RoughSaiasReverseNormalFormDefectInvLogSqBound`.  It never assumes a bound
for that defect.  Instead it keeps the quotient fractional correction with
its sign, separates the reverse defect into a continuous normal-form prime
sum and that signed correction, and applies the project's existing finite
theta Abel identity to the continuous prime sum.

The resulting quantitative theorem assumes only a cumulative theta-error
bound.  Its right side is the explicit endpoint-plus-variation ledger for the
Saias theta weight.  Thus the remaining inverse-log-square problem is a
deterministic estimate for the displayed signed Abel center, not a renamed
copy of the original defect bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-! ## One quotient: retain the fractional correction with its sign -/

/-- The formal normal form evaluated at the real quotient `X/m`, before the
quotient is replaced by its natural-number floor. -/
noncomputable def roughSaiasContinuousPrimeNormalForm
    (X m : ℕ) : ℝ :=
  roughSaiasLambdaNormalForm ((X : ℝ) / (m : ℝ)) m

/-- Signed discrepancy between the real-quotient normal form and the
natural-quotient main term. -/
noncomputable def roughSaiasSignedPrimeFloorCorrection
    (X m : ℕ) : ℝ :=
  roughSaiasContinuousPrimeNormalForm X m -
    roughSaiasNaturalMain (X / m) m

/-- The signed fractional correction after expanding
`LambdaNormalForm(X/m,m)`.  The first summand is the displacement of `G_m`;
the second is the exact cancellation contributed by `-fract(X/m)`. -/
noncomputable def roughSaiasSignedFractionalCorrectionTerm
    (X m : ℕ) : ℝ :=
  ((X / m : ℕ) : ℝ) *
      (roughSaiasG m
          (Real.log ((X : ℝ) / (m : ℝ)) /
            Real.log (m : ℝ)) -
        roughSaiasG m (FriableAsymptotic.dickmanU (X / m) m)) +
    Int.fract ((X : ℝ) / (m : ℝ)) *
      (roughSaiasG m
          (Real.log ((X : ℝ) / (m : ℝ)) /
            Real.log (m : ℝ)) - 1)





/-! ## The reverse defect as continuous part plus signed correction -/







/-! ## Exact finite theta Abel identity -/

/-- Test weight whose theta mass at a prime is the continuous real-quotient
normal form. -/
noncomputable def roughSaiasNormalFormThetaWeight
    (X m : ℕ) : ℝ :=
  roughSaiasContinuousPrimeNormalForm X m / Real.log (m : ℝ)



/-- Difference between the natural main-term endpoints and the integer Abel
main term for the continuous Saias weight. -/
noncomputable def roughSaiasIntegerAbelConsistencyDefect
    (X y Z : ℕ) : ℝ :=
  roughSaiasNaturalMain X Z - roughSaiasNaturalMain X y -
    FriableAsymptotic.integerAbelMain
      (roughSaiasNormalFormThetaWeight X) y Z











/-! ## The floor/frac-paired natural theta weight -/

/-- Theta weight with the natural quotient retained.  Its discrete
variation contains the quotient-floor jumps and the base variation of `G_m`
in one object. -/
noncomputable def roughSaiasNaturalQuotientThetaWeight
    (X m : ℕ) : ℝ :=
  roughSaiasNaturalMain (X / m) m / Real.log (m : ℝ)

/-- Theta weight of the signed fractional correction. -/
noncomputable def roughSaiasFractionalCorrectionThetaWeight
    (X m : ℕ) : ℝ :=
  roughSaiasSignedFractionalCorrectionTerm X m /
    Real.log (m : ℝ)











/-- Integer Abel consistency term for the floor/frac-paired natural weight. -/
noncomputable def roughSaiasNaturalIntegerAbelConsistencyDefect
    (X y Z : ℕ) : ℝ :=
  roughSaiasNaturalMain X Z - roughSaiasNaturalMain X y -
    FriableAsymptotic.integerAbelMain
      (roughSaiasNaturalQuotientThetaWeight X) y Z

/-- Theta-error transfer for the paired natural weight. -/
noncomputable def roughSaiasNaturalThetaErrorTransfer
    (X y Z : ℕ) : ℝ :=
  FriableAsymptotic.primeThetaWeightedInterval
      (roughSaiasNaturalQuotientThetaWeight X) y Z -
    FriableAsymptotic.integerAbelMain
      (roughSaiasNaturalQuotientThetaWeight X) y Z









/-! ## Quantitative theta transfer, without a defect-bound premise -/





/-- The corresponding PNT ledger for the floor/frac-paired natural weight. -/
noncomputable def roughSaiasNaturalThetaPNTLedger
    (A C : ℝ) (X y Z : ℕ) : ℝ :=
  |roughSaiasNaturalQuotientThetaWeight X Z| *
      (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ A)) +
    |roughSaiasNaturalQuotientThetaWeight X (y + 1)| *
      (C * ((y : ℝ) / Real.log (y : ℝ) ^ A)) +
    ∑ m ∈ Finset.Ioc y (Z - 1),
      |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
        (C * ((m : ℝ) / Real.log (m : ℝ) ^ A))







/-! ## Closed fourth-power theta specialization -/

/-- A named constant from the already proved theta PNT with fourth-power
logarithmic saving. -/
noncomputable def roughSaiasThetaFourthPowerConstant : ℝ :=
  Classical.choose
    (FriableAsymptotic.exists_primeLogSumUpTo_error_bound (4 : ℝ))



noncomputable def roughSaiasThetaFourthPowerCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      (FriableAsymptotic.exists_primeLogSumUpTo_error_bound (4 : ℝ))).2







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasBaseChange -/
section


/-!
# Base-free sawtooth coordinates for the Saias correction

The difficult base variation in `roughSaiasG m` contains
`fract(m^v) * m^(-v)`.  This file records the exact substitution `t=m^v`
before any absolute value is taken.  After multiplication by the Jacobian,
the sawtooth is `fract(t)`, independent of `m`; all base dependence is left
in the logarithmic Dickman kernel and the factor `1 / log m`.

This is an exact identity for the finite `[0,5]` integral.  The one-variable
Jacobian theorem is used because its monotone form permits the discontinuous
fractional-part integrand.
-/

open scoped Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-- Dickman coordinate after `t=m^v`. -/
noncomputable def roughSaiasBaseFreeDickmanCoordinate
    (q m : ℕ) (t : ℝ) : ℝ :=
  Real.log (q : ℝ) / Real.log (m : ℝ) -
    Real.log t / Real.log (m : ℝ)

/-- The base-dependent part of the transformed kernel. -/
noncomputable def roughSaiasScaledDickmanKernel
    (q m : ℕ) (t : ℝ) : ℝ :=
  roughSaiasDickmanDerivative
      (roughSaiasBaseFreeDickmanCoordinate q m t) /
    Real.log (m : ℝ)

/-- The Saias fractional kernel after the exact change of variables
`t=m^v`.  In particular, its sawtooth factor `fract(t)` is base-free. -/
noncomputable def roughSaiasBaseFreeFractionalKernel
    (q m : ℕ) (t : ℝ) : ℝ :=
  roughSaiasDickmanDerivative
      (Real.log (q : ℝ) / Real.log (m : ℝ) -
        Real.log t / Real.log (m : ℝ)) *
    Int.fract t /
      (Real.log (m : ℝ) * t ^ (2 : ℕ))

























/-- The transformed finite correction integral. -/
noncomputable def roughSaiasBaseFreeFractionalIntegral
    (q m : ℕ) : ℝ :=
  ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
    roughSaiasBaseFreeFractionalKernel q m t

















/-! ## Exact floor/base pairing in the transformed coordinate -/



/-- The natural theta weight in base-free sawtooth coordinates.  The
quotient parameter is explicit, so it can be held fixed on a hyperbola
block while the base varies. -/
noncomputable def roughSaiasBaseFreeNaturalThetaWeight
    (q m : ℕ) : ℝ :=
  ((q : ℝ) *
      (rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
        roughSaiasBaseFreeFractionalIntegral q m)) /
    Real.log (m : ℝ)







/-! ## The signed center as a base-free quotient-block sum -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasStieltjesNormalForm -/
section


/-!
# Identification of the finite signed functional with the Saias normal form

This file performs the finite integration-by-parts calculation that was
deliberately absent from `RoughSaiasNormalization`.  The atom part is
handled by the corner-safe right-derivative Abel theorem.  Its density term
cancels the quotient-rule part of that derivative before any estimate is
taken.  What remains splits exactly as

* a smooth Dickman FTC term, and
* the signed base-free fractional correction already formalized in
  `RoughSaiasBaseChange`.

Thus the explicit atom-minus-density functional is identified with the
existing normal form at a positive natural endpoint without assuming any
defect or endpoint estimate.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The exact density cancellation -/

/-- The single floor kernel left after the Abel derivative and the
absolutely continuous Stieltjes density are combined. -/
noncomputable def roughSaiasStieltjesFloorCorrection
    (X : ℕ) (y t : ℝ) : ℝ :=
  (X : ℝ) * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
    (((⌊t⌋₊ : ℕ) : ℝ)) /
      (t ^ 2 * Real.log y)

/-- Its smooth part, obtained by replacing `floor t` by `t`. -/
noncomputable def roughSaiasStieltjesSmoothCorrection
    (X : ℕ) (y t : ℝ) : ℝ :=
  (X : ℝ) * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate (X : ℝ) y t) /
    (t * Real.log y)

/-- Its signed fractional part.  This is subtracted from the smooth part. -/
noncomputable def roughSaiasStieltjesFractionalCorrection
    (X : ℕ) (y t : ℝ) : ℝ :=
  (X : ℝ) * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
    Int.fract t / (t ^ 2 * Real.log y)















/-! ## Evaluation of the smooth part -/













/-! ## Identification of the signed fractional part -/











/-! ## Final natural-endpoint identification -/





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasRealBaseChange -/
section


/-!
# Base-free Saias substitution at a real endpoint

`RoughSaiasBaseChange` carries a natural quotient because that is what the
hyperbola blocks need.  The continuous Buchstab functional also evaluates
the same normal form at real endpoints such as `X/p`.  This file records the
identical monotone substitution with a real first argument.
-/

open scoped Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full

noncomputable section

noncomputable def roughSaiasRealBaseFreeFractionalKernel
    (x : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  roughSaiasDickmanDerivative
      ((Real.log x - Real.log t) / Real.log (m : ℝ)) *
    Int.fract t /
      (Real.log (m : ℝ) * t ^ (2 : ℕ))

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasRealStieltjesNormalForm -/
section


/-!
# Real-endpoint identification of the Stieltjes and Saias normal forms

The natural-endpoint calculation in `RoughSaiasStieltjesNormalForm` is
extended here to every real outer endpoint `x ≥ 1`.  Abel summation now
produces `floor x`, and the elementary identity

`floor x = x - fract x`

supplies exactly the terminal sawtooth in `roughSaiasLambdaNormalForm`.
This real version is needed in continuous Buchstab at the inner endpoints
`x/s`.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Real floor-correction kernels -/

noncomputable def roughSaiasRealStieltjesFloorCorrection
    (x y t : ℝ) : ℝ :=
  x * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate x y t) *
    (((⌊t⌋₊ : ℕ) : ℝ)) /
      (t ^ 2 * Real.log y)

noncomputable def roughSaiasRealStieltjesSmoothCorrection
    (x y t : ℝ) : ℝ :=
  x * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate x y t) /
    (t * Real.log y)

noncomputable def roughSaiasRealStieltjesFractionalCorrection
    (x y t : ℝ) : ℝ :=
  x * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate x y t) *
    Int.fract t / (t ^ 2 * Real.log y)





/-! ## Real compact integrability -/







/-! ## Abel summation at a real endpoint -/









/-! ## Smooth real contribution -/









/-! ## Fractional real contribution -/







/-! ## Exact real-endpoint identification -/



end

end Erdos390.WholePaper

end


