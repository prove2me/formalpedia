-- Prove2me | Definitions.Def_AT260939824_RealizedBottomCombing
-- name    : AT260939824_RealizedBottomCombing
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:19:17.949656+00:00
-- url     : https://prove2.me/theorems/629d23e6-212f-41e7-b78d-34e7d1c7fc02
-- title:
--   The bottom combing as a map into the carrier realization
-- statement:
--   Let $m,R\in\mathbb N$ with $m\ge2$ and $R>0$, and set $K=\lfloor\log_mR\rfloor$. The digit-splice bottom combing produces a mass vector $B(x,t)$ on the finite height-$K$ interval carrier over $[0,R]$, for $x\in\mathbb R$ and $t\in[0,1]$. Its previously established carrier-membership property defines the realized map
--   $$\widehat B:\mathbb R\times[0,1]\longrightarrow |C_{m,K}[0,R]|.$$
--   The value $\widehat B(x,t)$ is the unique carrier point with mass coordinates $B(x,t)$, via the ambient realization equivalence. This packages the same homotopy with its geometric codomain. Its mass coordinates agree exactly with $B$. At time zero it is the base vertex $\delta_{(0,0)}$ for every $x$; at time one its masses give the bottom map, affine between consecutive bottom vertices and constant outside $[0,R]$. At horizontal coordinate $x=0$, the entire path remains at that base vertex.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RealizedBottomCombing.lean, selected declaration lines 9-12, 14-17, 43-52, 54-56, 58-67; SHA-256 2e4a8eb313cb416967555023117a687c4b5e044334f9d0f54f19974d43e010ab. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_BottomIntervalMap
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierCharts
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedCarrierWalks
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitBottomCombing
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

/-! The logarithmic-speed bottom combing takes values in the actual carrier. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

def realizedBottomCombing (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (z : ℝ × unitInterval) : Realization m (Nat.log m R) 0 R :=
  (ambientEquiv m (Nat.log m R) 0 R).symm
    ⟨bottomCombing m hm R z,bottomCombing_mem m hm R hR z⟩

@[simp] theorem realizedBottomCombing_mass (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (z : ℝ × unitInterval) : (realizedBottomCombing m hm R hR z).1.mass =
      bottomCombing m hm R z :=
  congrArg Subtype.val ((ambientEquiv m (Nat.log m R) 0 R).apply_symm_apply _)







@[simp] theorem realizedBottomCombing_source (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (x : ℝ) : realizedBottomCombing m hm R hR (x,0) = point (carrierBase (Nat.log m R) R) := by
  apply Subtype.ext
  apply Probability.ext
  rw [realizedBottomCombing_mass,bottomCombing_source m hm R hR,bottomMass_eq _ R 0 (by omega)]
  have he : bottomVertex (Nat.log m R) R 0 (by omega) = carrierBase (Nat.log m R) R := by
    apply Subtype.ext
    rfl
  rw [he]
  rfl

@[simp] theorem realizedBottomCombing_target_mass (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (x : ℝ) : (realizedBottomCombing m hm R hR (x,1)).1.mass = bottomMap (Nat.log m R) R x := by
  rw [realizedBottomCombing_mass,bottomCombing_target m hm R hR]

@[simp] theorem realizedBottomCombing_base (m : ℕ) (hm : 2 ≤ m) (R : ℕ) (hR : 0 < R)
    (u : unitInterval) : realizedBottomCombing m hm R hR (0,u) = point (carrierBase (Nat.log m R) R) := by
  apply Subtype.ext
  apply Probability.ext
  rw [realizedBottomCombing_mass,bottomCombing_base m hm R hR,bottomMass_eq _ R 0 (by omega)]
  have he : bottomVertex (Nat.log m R) R 0 (by omega) = carrierBase (Nat.log m R) R := by
    apply Subtype.ext
    rfl
  rw [he]
  rfl

end
end AbelianTargets.IntervalCarriers


