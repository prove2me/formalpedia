-- Prove2me | Definitions.Def_AT260939824_VerticalCarrierFaces
-- name    : AT260939824_VerticalCarrierFaces
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:11:56.855016+00:00
-- url     : https://prove2.me/theorems/7fc2fb7c-d1e8-4f5d-af6b-9062061d88ad
-- title:
--   Terminal fan faces containing a top vertex are vertical
-- statement:
--   Define the vertical pair at horizontal coordinate $r$ and height $K$ by
--   $$V(r,K)=\{(r,K),(r,K+1)\}.$$
--   After all selected upper and fan diagonals have been removed, the terminal admissible face system excludes every top horizontal edge. For $m\ge1$, any original carrier face $s$ still admissible in that terminal system and containing a vertex $v$ at height $K+1$ satisfies
--   $$s\subseteq V(v_1,K).$$
--   The selected graph-edge and triangle classifications prove this confinement and ensure that replacing a top vertex by its floor remains inside an allowed vertical edge.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/VerticalCarrierFaces.lean, selected declaration lines 7, 9-10, 12-27, 29-68, 70-150; SHA-256 62c5e6b0f93b94df506cce4a811c3d320f1da9a45e17519bd339bf9b12d437ef. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UpperCarrierCollapse
import Definitions.Def_AT260939824_UpperCarrierFaces
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

/-! Terminal polygon fans consist of lower faces and vertical edges. -/

namespace AbelianTargets.IntervalCarriers

def verticalPair (r : ℤ) (K : ℕ) : Finset Vertex := {(r,K),(r,K+1)}

theorem mem_verticalPair_top (v : Vertex) {K : ℕ} (htop : v.2 = K+1) : v ∈ verticalPair v.1 K := by
  simp [verticalPair,←htop]

theorem horizontal_top_forbidden {m K : ℕ} {A B : ℤ} {s : Finset Vertex} {x y : Vertex}
    (hx : x ∈ carrierVertices (K+1) A B) (hy : y ∈ carrierVertices (K+1) A B)
    (htop : x.2 = K+1) (hhor : HorizontalStep m x y)
    (hs : FanAdmissible m K A B 0 s) : ¬(x ∈ s ∧ y ∈ s) := by
  obtain ⟨hxA,hxB,hxK⟩ := mem_carrierVertices.mp hx
  obtain ⟨hyA,hyB,hyK⟩ := mem_carrierVertices.mp hy
  have hy' : y = (x.1+(m:ℤ)^(K+1),K+1) := by simpa only [HorizontalStep,htop] using hhor
  have hc : (x.1,K) ∈ topCells m K A B := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨mem_carrierVertices.mpr ⟨hxA,hxB,by omega⟩,by omega,?_⟩,rfl⟩
    simpa only [hy'] using hyB
  have h := hs.1 ⟨(x.1,K),hc⟩
  change ¬((x.1,K+1) ∈ s ∧ (x.1+(m:ℤ)^(K+1),K+1) ∈ s) at h
  have hx' : (x.1,K+1) = x := Prod.ext rfl htop.symm
  rw [hx',←hy'] at h
  exact h

theorem top_graph_face_vertical {m K : ℕ} {A B : ℤ} {s : Finset Vertex} {x y : Vertex}
    (hx : x ∈ carrierVertices (K+1) A B) (hy : y ∈ carrierVertices (K+1) A B)
    (htop : x.2 = K+1) (he : (graph m).Adj x y) (hxy : s ⊆ {x,y}) (hxs : x ∈ s)
    (hs : FanAdmissible m K A B 0 s) : s ⊆ verticalPair x.1 K := by
  have hsingle (hyn : y ∉ s) : s ⊆ verticalPair x.1 K := by
    intro v hv
    have h := hxy hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with h | h
    · subst v; simp [verticalPair,←htop,Prod.eta]
    · exact (hyn (by simpa only [h] using hv)).elim
  obtain ⟨hne,hrel | hrel⟩ := he
  · rcases hrel with hhor | hver
    · apply hsingle
      intro hys
      exact horizontal_top_forbidden hx hy htop hhor hs ⟨hxs,hys⟩
    · have hyK := (mem_carrierVertices.mp hy).2.2
      have he := congrArg Prod.snd hver
      dsimp [VerticalStep] at he
      omega
  · rcases hrel with hhor | hver
    · have hyheight : y.2 = K+1 := by
        have hh := congrArg Prod.snd hhor
        dsimp [HorizontalStep] at hh
        omega
      apply hsingle
      intro hys
      exact horizontal_top_forbidden hy hx hyheight hhor hs ⟨hys,hxs⟩
    · have hyx := congrArg Prod.fst hver
      have hyheight : y.2 = K := by
        have hh := congrArg Prod.snd hver
        dsimp [VerticalStep] at hh
        omega
      have hy' : y = (x.1,K) := Prod.ext hyx.symm hyheight
      intro v hv
      have h := hxy hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with h | h
      · subst v; simp [verticalPair,←htop,Prod.eta]
      · subst v; simp [verticalPair,hy']

theorem top_face_vertical {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) {s : Finset Vertex}
    (hs : CarrierFace m (K+1) A B s) (hallowed : FanAdmissible m K A B 0 s)
    {v : Vertex} (hv : v ∈ s) (htop : v.2 = K+1) : s ⊆ verticalPair v.1 K := by
  have hverts := hs.vertices
  rcases hs with ⟨x,hx,hs⟩ | ⟨x,hx,y,hy,he,hs⟩ | ⟨t,ht,hs⟩
  · have hvx := Finset.mem_singleton.mp (hs hv)
    intro w hw
    have hwx := Finset.mem_singleton.mp (hs hw)
    have hwv := hwx.trans hvx.symm
    simpa only [hwv] using mem_verticalPair_top v htop
  · have hv' := hs hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv'
    rcases hv' with h | h
    · subst v; exact top_graph_face_vertical hx hy htop he hs hv hallowed
    · subst v
      exact top_graph_face_vertical hy hx htop he.symm
        (by simpa only [Finset.pair_comm] using hs) hv hallowed
  · obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · subst t
      have hv' := top_mem_upperTriangle hc (hs hv) htop
      have hcHeight : c.2 = K := by
        rcases hv' with h | h <;> have hh := congrArg Prod.snd h <;>
          dsimp [upperLeft,upperRight] at hh <;> omega
      have hcTop : c ∈ topCells m K A B := Finset.mem_filter.mpr ⟨hc,hcHeight⟩
      have hup := hallowed.1 ⟨c,hcTop⟩
      have hlow := hallowed.2 ⟨c,hcTop⟩ (m-1) (by omega) (by omega)
      change ¬(upperLeft c.1 c.2 ∈ s ∧ upperRight m c.1 c.2 ∈ s) at hup
      change ¬(upperLeft c.1 c.2 ∈ s ∧ lowerVertex m c.1 c.2 (m-1+1) ∈ s) at hlow
      have hmm : m-1+1 = m := by omega
      rw [hmm] at hlow
      rcases hv' with hva | hvb
      · have has : upperLeft c.1 c.2 ∈ s := by simpa only [hva] using hv
        intro w hw
        have hw' := hs hw
        simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hw'
        rcases hw' with h | h | h
        · have hwv := h.trans hva.symm
          simpa only [hwv] using mem_verticalPair_top v htop
        · exact (hlow ⟨has,by simpa only [h] using hw⟩).elim
        · exact (hup ⟨has,by simpa only [h] using hw⟩).elim
      · have hbs : upperRight m c.1 c.2 ∈ s := by simpa only [hvb] using hv
        intro w hw
        have hw' := hs hw
        simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hw'
        rcases hw' with h | h | h
        · exact (hup ⟨by simpa only [h] using hw,hbs⟩).elim
        · have he : lowerVertex m c.1 c.2 m = (v.1,K) := by
            rw [hvb]
            apply Prod.ext
            · dsimp [lowerVertex,upperRight]; rw [pow_succ]; ring
            · exact hcHeight
          simp [verticalPair,h,he]
        · have hwv := h.trans hvb.symm
          simpa only [hwv] using mem_verticalPair_top v htop
    · obtain ⟨n,hn,ht⟩ := Finset.mem_image.mp ht
      subst t
      have hv' := top_mem_lowerTriangle hc (hs hv) htop
      have hcHeight : c.2 = K := by have hh := congrArg Prod.snd hv'; dsimp [upperLeft] at hh; omega
      have hcTop : c ∈ topCells m K A B := Finset.mem_filter.mpr ⟨hc,hcHeight⟩
      have has : upperLeft c.1 c.2 ∈ s := by simpa only [hv'] using hv
      intro w hw
      have hw' := hs hw
      simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hw'
      rcases hw' with h | h | h
      · have hwv := h.trans hv'.symm
        simpa only [hwv] using mem_verticalPair_top v htop
      · by_cases hn0 : n = 0
        · subst n
          have he : lowerVertex m c.1 c.2 0 = (v.1,K) := by
            rw [hv']; apply Prod.ext
            · simp [lowerVertex,upperLeft]
            · exact hcHeight
          simp [verticalPair,h,he]
        · have hlow := hallowed.2 ⟨c,hcTop⟩ (n-1) (by omega) (by have hn' := Finset.mem_range.mp hn; omega)
          change ¬(upperLeft c.1 c.2 ∈ s ∧ lowerVertex m c.1 c.2 (n-1+1) ∈ s) at hlow
          have hnn : n-1+1 = n := by omega
          rw [hnn] at hlow
          exact (hlow ⟨has,by simpa only [h] using hw⟩).elim
      · have hlow := hallowed.2 ⟨c,hcTop⟩ n (by omega) (Finset.mem_range.mp hn)
        exact (hlow ⟨has,by simpa only [h] using hw⟩).elim

end AbelianTargets.IntervalCarriers


