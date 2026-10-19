-- Prove2me | Definitions.Def_AT260939824_LowerCarrierFaces
-- name    : AT260939824_LowerCarrierFaces
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:09:29.728419+00:00
-- url     : https://prove2.me/theorems/521a3904-7c33-40c7-9c0f-ff0f625f5d3c
-- title:
--   Free diagonals in a presentation-polygon fan
-- statement:
--   The lower vertices of a presentation polygon are injectively indexed under the stated positive-base hypotheses. At each fan stage, a face containing the designated free edge must lie in the corresponding triangle. The bundle also records the face-containment reduction needed when dropping the third vertex. These combinatorial certificates justify the simultaneous lower-fan collapse maps.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/LowerCarrierFaces.lean, selected declaration lines 7-15, 17-25, 27-127; SHA-256 9dae4c594484cb426991b3c0c9d2c92549cd7d0847d12ac2ab6fadbab420ff7c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
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

/-! The successive free diagonals of a presentation-polygon fan. -/

namespace AbelianTargets.IntervalCarriers

theorem lowerVertex_injective {m : ℕ} (hm : 1 ≤ m) (r : ℤ) (j : ℕ) :
    Function.Injective (lowerVertex m r j) := by
  intro n k h
  have he := congrArg Prod.fst h
  dsimp [lowerVertex] at he
  have hp : 0 < (m : ℤ)^j := pow_pos (by exact_mod_cast (show 0 < m by omega)) _
  have he' : (n : ℤ)*(m : ℤ)^j = (k : ℤ)*(m : ℤ)^j := by linarith
  have hn := mul_right_cancel₀ (ne_of_gt hp) he'
  exact_mod_cast hn

theorem subset_drop_third {V : Type*} [DecidableEq V] {s : Finset V} {a b c : V}
    (hs : s ⊆ {a,b,c}) (ha : a ∈ s) (hforbid : ¬(a ∈ s ∧ c ∈ s)) : s ⊆ {a,b} := by
  intro v hv
  have hv' := hs hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv' ⊢
  rcases hv' with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hforbid ⟨ha,by simpa only [h] using hv⟩).elim

theorem lower_edge_free {m K n : ℕ} {A B r : ℤ} (hm : 1 ≤ m) (hn : n < m)
    {s : Finset Vertex} (hs : CarrierFace m (K+1) A B s)
    (ha : upperLeft r K ∈ s) (hb : lowerVertex m r K (n+1) ∈ s)
    (hupper : ∀ c : TopCell m K A B,
      ¬(upperLeft c.1.1 c.1.2 ∈ s ∧ upperRight m c.1.1 c.1.2 ∈ s))
    (hnext : n+1 < m → ∀ c : TopCell m K A B,
      ¬(upperLeft c.1.1 c.1.2 ∈ s ∧ lowerVertex m c.1.1 c.1.2 (n+2) ∈ s)) :
    s ⊆ lowerTriangle m (r,K) n := by
  have hab : upperLeft r K ≠ lowerVertex m r K (n+1) := by
    intro h; have he := congrArg Prod.snd h; dsimp [upperLeft,lowerVertex] at he; omega
  rcases hs with ⟨v,hv,hs⟩ | ⟨u,hu,v,hv,he,hs⟩ | ⟨t,ht,hs⟩
  · have ha' := Finset.mem_singleton.mp (hs ha)
    have hb' := Finset.mem_singleton.mp (hs hb)
    exact (hab (ha'.trans hb'.symm)).elim
  · have ha' := hs ha
    have hb' := hs hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha' hb'
    rcases ha' with hau | hav <;> rcases hb' with hbu | hbv
    · exact (hab (hau.trans hbu.symm)).elim
    · rw [←hau,←hbv] at hs
      apply hs.trans
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [lowerTriangle]
    · rw [←hav,←hbu] at hs
      apply hs.trans
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [lowerTriangle]
    · exact (hab (hav.trans hbv.symm)).elim
  · obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · subst t
      have ha' := top_mem_upperTriangle hc (hs ha) (by rfl)
      have hb' : lowerVertex m r K (n+1) = lowerVertex m c.1 c.2 m := by
        have hmem := hs hb
        simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hmem
        rcases hmem with h | h | h
        · have he := congrArg Prod.snd h; dsimp [lowerVertex,upperLeft] at he
          have he' := congrArg Prod.snd (ha'.resolve_right (by
            intro h'; have hh := congrArg Prod.snd h'; dsimp [upperLeft,upperRight] at hh; omega))
          dsimp [upperLeft] at he'; omega
        · exact h
        · have hh := congrArg Prod.snd h; dsimp [lowerVertex,upperRight] at hh
          rcases ha' with he | he <;> have he' := congrArg Prod.snd he <;>
            dsimp [upperLeft,upperRight] at he' <;> omega
      rcases ha' with hau | hav
      · have hr : r = c.1 := congrArg Prod.fst hau
        have hj : K = c.2 := by have hh := congrArg Prod.snd hau; dsimp [upperLeft] at hh; omega
        have hc' : c = (r,K) := Prod.ext hr.symm hj.symm
        have hcTop : c ∈ topCells m K A B := Finset.mem_filter.mpr ⟨hc,hj.symm⟩
        have hforbid := hupper ⟨c,hcTop⟩
        change ¬(upperLeft c.1 c.2 ∈ s ∧ upperRight m c.1 c.2 ∈ s) at hforbid
        rw [hc'] at hs hb' hforbid
        have hnm : n+1 = m := lowerVertex_injective hm r K hb'
        have hsmall := subset_drop_third hs ha hforbid
        apply hsmall.trans
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl | h
        · simp [lowerTriangle]
        · change v = lowerVertex m r K m at h
          have hv' : v = lowerVertex m r K (n+1) := h.trans (congrArg (lowerVertex m r K) hnm.symm)
          simp [lowerTriangle,hv']
      · have hj : K = c.2 := by have hh := congrArg Prod.snd hav; dsimp [upperLeft,upperRight] at hh; omega
        have h1 := congrArg Prod.fst hav
        have h2 := congrArg Prod.fst hb'
        dsimp [upperLeft,upperRight,lowerVertex] at h1 h2
        rw [←hj,pow_succ,mul_comm] at h1
        rw [←hj] at h2
        have hp : 0 < (m : ℤ)^K := pow_pos (by exact_mod_cast (show 0 < m by omega)) _
        have hnpos : 0 < ((n+1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos n
        have hp' := mul_pos hnpos hp
        push_cast at hp'
        linarith
    · obtain ⟨k,hk,ht⟩ := Finset.mem_image.mp ht
      subst t
      have hau := top_mem_lowerTriangle hc (hs ha) (by rfl)
      have hr : r = c.1 := congrArg Prod.fst hau
      have hj : K = c.2 := by have hh := congrArg Prod.snd hau; dsimp [upperLeft] at hh; omega
      have hc' : c = (r,K) := Prod.ext hr.symm hj.symm
      have hcTop : c ∈ topCells m K A B := Finset.mem_filter.mpr ⟨hc,hj.symm⟩
      rw [hc'] at hs
      have hb' := hs hb
      simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hb'
      rcases hb' with h | h | h
      · exact (hab h.symm).elim
      · have hnk : n+1 = k := lowerVertex_injective hm r K h
        subst k
        have hforbid := hnext (Finset.mem_range.mp hk) ⟨c,hcTop⟩
        change ¬(upperLeft c.1 c.2 ∈ s ∧ lowerVertex m c.1 c.2 (n+2) ∈ s) at hforbid
        rw [hc'] at hforbid
        have hsmall := subset_drop_third hs ha hforbid
        apply hsmall.trans
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> simp [lowerTriangle]
      · have hnk : n+1 = k+1 := lowerVertex_injective hm r K h
        have hnk' : n = k := by omega
        subst k
        exact hs

end AbelianTargets.IntervalCarriers


