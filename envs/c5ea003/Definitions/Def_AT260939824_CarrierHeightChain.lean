-- Prove2me | Definitions.Def_AT260939824_CarrierHeightChain
-- name    : AT260939824_CarrierHeightChain
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:19:58.265134+00:00
-- url     : https://prove2.me/theorems/07d0fbae-97cc-4189-854a-5fd1b8fb53d9
-- title:
--   Sequential height-reduction chains
-- statement:
--   For a carrier with base $m$ and height $K$, a height chain consists of time families $H_n$ with matching seams. It begins at the identity, reaches support of height zero after $K$ stages, and is stationary thereafter. Each time track has Lipschitz bound $m+2$, each stage has a finite joint bound, and all bottom-supported points remain fixed.
--
--   The chain record retains the data needed to assemble one global height deformation.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierHeightChain.lean, selected declaration lines 13-21, 23-102, 104-105; SHA-256 518ebbbed5a4b87001c0bc70a58d20f8abd29ce376189733ff9368eba7c63438. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierNesting
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_OneHeightDeformation
import Definitions.Def_AT260939824_OneHeightRetraction
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UpperCarrierCollapse
import Definitions.Def_AT260939824_VerticalCarrierCollapse
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
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

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-! Actual height-by-height deformation curves in one fixed carrier. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

structure HeightChain (m K : ℕ) (A B : ℤ) where
  curve : ℕ → Realization m K A B × unitInterval → Realization m K A B
  initial : ∀ p, curve 0 (p,0) = p
  seam : ∀ n p, curve n (p,1) = curve (n+1) (p,0)
  terminal : ∀ p v, 0 < (curve K (p,0)).1.mass v → v.1.2 = 0
  tail : ∀ n, K ≤ n → ∀ p t, curve n (p,t) = curve K (p,0)
  track : ∀ n p, LipschitzWith ((m+2 : ℕ) : ℝ≥0) (fun t => curve n (p,t))
  joint : ∀ n, ∃ J : ℝ≥0, LipschitzWith J (curve n)
  fixes_bottom : ∀ p, (∀ v, 0 < p.1.mass v → v.1.2 = 0) → ∀ n t, curve n (p,t) = p

theorem exists_heightChain {m : ℕ} (hm : 1 ≤ m) (K : ℕ) (A B : ℤ) : Nonempty (HeightChain m K A B) := by
  induction K with
  | zero =>
    refine ⟨{
      curve := fun _ z => z.1
      initial := fun _ => rfl
      seam := fun _ _ => rfl
      terminal := ?_
      tail := fun _ _ _ _ => rfl
      track := ?_
      joint := fun _ => ⟨1,LipschitzWith.prod_fst⟩
      fixes_bottom := fun _ _ _ _ => rfl }⟩
    · intro p v hv
      have hh := (mem_carrierVertices.mp v.2).2.2
      omega
    · intro n p
      exact (LipschitzWith.const p).weaken (by positivity)
  | succ K ih =>
    obtain ⟨G⟩ := ih
    let r : Realization m (K+1) A B → Realization m K A B := oneHeightRetraction hm
    let e : Realization m K A B → Realization m (K+1) A B := carrierInclude (by omega)
    let H : ℕ → Realization m (K+1) A B × unitInterval → Realization m (K+1) A B
      | 0 => fun z => oneHeightHomotopy hm z.1 z.2
      | n+1 => fun z => e (G.curve n (r z.1,z.2))
    refine ⟨{
      curve := H
      initial := ?_
      seam := ?_
      terminal := ?_
      tail := ?_
      track := ?_
      joint := ?_
      fixes_bottom := ?_ }⟩
    · intro p
      exact oneHeightHomotopy_zero hm p
    · intro n p
      cases n with
      | zero =>
        change oneHeightHomotopy hm p 1 = e (G.curve 0 (r p,0))
        rw [G.initial]
        exact (include_oneHeightRetraction hm p).symm
      | succ n =>
        change e (G.curve n (r p,1)) = e (G.curve (n+1) (r p,0))
        rw [G.seam]
    · intro p v hv
      change 0 < (Probability.push (vertexInclude (by omega)) (G.curve K (r p,0)).1).mass v at hv
      obtain ⟨u,hu,hup⟩ := (Probability.push_pos_iff (vertexInclude (by omega)) _ v).mp hv
      rw [←hu]
      exact G.terminal (r p) u hup
    · intro n hn p t
      cases n with
      | zero => omega
      | succ n =>
        change e (G.curve n (r p,t)) = e (G.curve K (r p,0))
        rw [G.tail n (by omega)]
    · intro n p
      cases n with
      | zero => exact oneHeightHomotopy_track hm p
      | succ n =>
        simpa only [H,Function.comp_def,one_mul] using
          (isometry_include (m := m) (A := A) (B := B) (by omega : K ≤ K+1)).lipschitz.comp (G.track n (r p))
    · intro n
      cases n with
      | zero => exact oneHeightHomotopy_joint hm
      | succ n =>
        obtain ⟨Jr,hJr⟩ := oneHeightRetraction_joint (K := K) (A := A) (B := B) hm
        obtain ⟨Jg,hJg⟩ := G.joint n
        have hp := (hJr.comp LipschitzWith.prod_fst).prodMk
          (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : Realization m (K+1) A B × unitInterval → unitInterval))
        refine ⟨Jg * max (Jr * 1) 1,?_⟩
        simpa only [H,r,e,Function.comp_def,one_mul] using
          (isometry_include (m := m) (A := A) (B := B) (by omega : K ≤ K+1)).lipschitz.comp (hJg.comp hp)
    · intro p hp n t
      have hpl : ∀ v, 0 < p.1.mass v → v.1.2 ≤ K := fun v hv => by rw [hp v hv]; exact Nat.zero_le _
      cases n with
      | zero => exact oneHeightHomotopy_fixes_lower hm p hpl t
      | succ n =>
        change e (G.curve n (r p,t)) = p
        rw [G.fixes_bottom (r p) (oneHeightRetraction_preserves_bottom hm p hp) n t]
        exact (include_oneHeightRetraction hm p).trans (oneHeightHomotopy_fixes_lower hm p hpl 1)

def heightChain {m : ℕ} (hm : 1 ≤ m) (K : ℕ) (A B : ℤ) : HeightChain m K A B :=
  Classical.choice (exists_heightChain hm K A B)

end
end AbelianTargets.IntervalCarriers


