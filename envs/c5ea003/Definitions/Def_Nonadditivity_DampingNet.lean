-- Prove2me | Definitions.Def_Nonadditivity_DampingNet
-- name    : Nonadditivity_DampingNet
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:35:38.110368+00:00
-- url     : https://prove2.me/theorems/b71acf56-cebc-48da-8897-829050ba5311
-- title:
--   From finite observable nets to a damped-channel certificate
-- statement:
--   Let $T$ be a finite Kraus channel, and let $F$ be a Hermitian input matrix with $I-F^2\succeq0$. Fix $a>1$, $c\ge0$, and a finite $\delta$-net of unit traceless Hermitian output observables in Hilbert–Schmidt norm, with $\delta=(a-1)/(a+1)$. If every net point $Y$ satisfies $\|F T^*(Y)F\|\le(1+\delta)c$, then the associated damped channel $T_F$ satisfies
--   $$\|T_F^*(A)\|\le ac\|A\|_{\rm HS}$$
--   for every traceless Hermitian output matrix $A$, where $\|\cdot\|$ is the Euclidean operator norm. The bundle also proves that for $0\le r<1$, $M\ge0$, and $\eta>0$, some integer $p\ge1$ satisfies $2Mr^{2p}<\eta$. Together these results convert finitely many high-moment compression tests into a uniform channel bound.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/DampingNet.lean#L19-L51

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_DampedChannel
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! Finite observable tests and the elementary moment choice for deterministic damping. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Nonadditivity.DampingNet
open Channels Channels.KrausChannel AdjointPurity FiniteRealization
open Filter Topology
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- A fixed finite number of normalized even moments can be made arbitrarily small. -/
theorem exists_even_moment_small {r η : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (M : ℕ) (hη : 0 < η) :
    ∃ p : ℕ, 1 ≤ p ∧ 2 * (M : ℝ) * r ^ (2*p) < η := by
  have hr2 : r^2 < 1 := by nlinarith
  have ht : Tendsto (fun p : ℕ => 2 * (M : ℝ) * (r^2)^p) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg r) hr2).const_mul
      (2 * (M : ℝ))
  have hs : ∀ᶠ p : ℕ in atTop, 2 * (M : ℝ) * (r^2)^p < η :=
    ht.eventually (gt_mem_nhds hη)
  obtain ⟨p, hp, hsmall⟩ := ((eventually_ge_atTop 1).and hs).exists
  exact ⟨p, hp, by simpa only [pow_mul] using hsmall⟩

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Nonempty ο] [Fintype κ]

/-- Compression bounds on a finite net give the full actual damped-channel certificate. -/
theorem damped_certificate (T : KrausChannel ι ο κ) (F : Matrix ι ι ℂ)
    (hF : F.IsHermitian) (hres : (1-F*F).PosSemidef)
    {tests : Finset (ObservableSpace ο)} {a c : ℝ}
    (ha : 1 < a) (hc : 0 ≤ c)
    (hnet : UnitSphereNet tests ((a-1)/(a+1)))
    (htests : ∀ y ∈ tests,
      ‖F * T.adjointMap (observableMatrix y) * F‖ ≤ (1+(a-1)/(a+1))*c) :
    ∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace=0 →
      ‖(DampedChannel.damped T F hF hres).adjointMap A‖ ≤ a*c*hsLength A := by
  apply matrix_certificate_of_observable_bound
  apply kappa_net_certificate _ ha hc hnet
  intro y hy
  change ‖(DampedChannel.damped T F hF hres).adjointMap (observableMatrix y)‖ ≤ _
  rw [DampedChannel.damped_adjointMap_traceless _ _ _ _ _
    (observableMatrix_trace_zero y)]
  exact htests y hy

end Nonadditivity.DampingNet


