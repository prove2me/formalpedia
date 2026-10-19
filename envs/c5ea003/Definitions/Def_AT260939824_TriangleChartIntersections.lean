-- Prove2me | Definitions.Def_AT260939824_TriangleChartIntersections
-- name    : AT260939824_TriangleChartIntersections
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:20:08.635446+00:00
-- url     : https://prove2.me/theorems/64855b49-18ef-437b-acb7-6a9c5f45b608
-- title:
--   Intersections of distinct presentation-cell fan triangulations
-- statement:
--   For $m\ge1$, a presentation-cell fan based at $c=(r,h)$ consists of its upper triangle and its lower triangles indexed by $0\le n<m$. A finite set is a fan triangle when it equals one of these triangles. Any pair of distinct vertices in such a triangle is either an edge of the presentation graph or one of that fan's interior diagonals. If triangles come from distinct fan origins, every pair of shared distinct vertices is a graph edge. Thus a nonempty shared face contained in the finite interval-carrier vertices lies in a singleton or in an actual graph edge:
--   $$u\subseteq s\cap t,\ c_s\ne c_t\quad\Longrightarrow\quad
--   u\subseteq\{v\}\ \text{or}\ u\subseteq\{v,w\},\ v\sim w.$$
--   The selected edge classifications identify exactly which edges are horizontal or vertical, supporting agreement of different cell charts.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/TriangleChartIntersections.lean, selected declaration lines 6-7, 9-17, 19-21, 23-25, 27-41, 43-57, 59-65, 67-77, 79-88, 90-99, 101-109, 111-156, 158-176, 178-190, 192-210, 212-228; SHA-256 06ff0bc94affa2a157e5c62fedea204f2ba3bb246a65851a6d85434bfef36e4f. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
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

/-! Non-skeleton diagonals belong to one literal relation polygon. -/
namespace AbelianTargets.IntervalCarriers

def IsFanTriangle (m : ℕ) (c : Vertex) (s : Finset Vertex) : Prop :=
  s=upperTriangle m c ∨ ∃ n, n<m ∧ s=lowerTriangle m c n

theorem fanTriangle_of_carrierTriangle {m K : ℕ} {A B : ℤ} {s : Finset Vertex}
    (hs : s∈carrierTriangles m K A B) :
    ∃ c∈carrierCells m K A B, IsFanTriangle m c s := by
  obtain ⟨c,hc,hs⟩ := Finset.mem_biUnion.mp hs
  refine ⟨c,hc,?_⟩
  rcases Finset.mem_insert.mp hs with h | h
  · exact Or.inl h
  · obtain ⟨n,hn,he⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨n,Finset.mem_range.mp hn,he.symm⟩

 theorem upper_horizontal (m : ℕ) (r : ℤ) (j : ℕ) (hm : 1≤m) :
    (graph m).Adj (upperLeft r j) (upperRight m r j) :=
  horizontal_adj hm rfl

 theorem upper_vertical (m : ℕ) (r : ℤ) (j : ℕ) :
    (graph m).Adj (lowerVertex m r j m) (upperRight m r j) :=
  vertical_adj (lowerVertex_upper m r j)

theorem lowerTriangle_pair {m : ℕ} (hm : 1≤m) (c : Vertex) (n : ℕ) {u v : Vertex}
    (hu : u∈lowerTriangle m c n) (hv : v∈lowerTriangle m c n) (hne : u≠v) :
    (graph m).Adj u v ∨
      (u.2=v.2+1 ∧ c=(u.1,v.2)) ∨ (v.2=u.2+1 ∧ c=(v.1,u.2)) := by
  simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · exact Or.inr (Or.inl ⟨rfl,Prod.eta _⟩)
  · exact Or.inr (Or.inl ⟨rfl,Prod.eta _⟩)
  · exact Or.inr (Or.inr ⟨rfl,Prod.eta _⟩)
  · exact False.elim (hne rfl)
  · exact Or.inl (horizontal_adj hm (lowerVertex_step m c.1 c.2 n))
  · exact Or.inr (Or.inr ⟨rfl,Prod.eta _⟩)
  · exact Or.inl (horizontal_adj hm (lowerVertex_step m c.1 c.2 n)).symm
  · exact False.elim (hne rfl)

theorem upperTriangle_pair {m : ℕ} (hm : 1≤m) (c : Vertex) {u v : Vertex}
    (hu : u∈upperTriangle m c) (hv : v∈upperTriangle m c) (hne : u≠v) :
    (graph m).Adj u v ∨
      (u.2=v.2+1 ∧ c=(u.1,v.2)) ∨ (v.2=u.2+1 ∧ c=(v.1,u.2)) := by
  simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · exact Or.inr (Or.inl ⟨rfl,Prod.eta _⟩)
  · exact Or.inl (upper_horizontal m c.1 c.2 hm)
  · exact Or.inr (Or.inr ⟨rfl,Prod.eta _⟩)
  · exact False.elim (hne rfl)
  · exact Or.inl (upper_vertical m c.1 c.2)
  · exact Or.inl (upper_horizontal m c.1 c.2 hm).symm
  · exact Or.inl (upper_vertical m c.1 c.2).symm
  · exact False.elim (hne rfl)

theorem IsFanTriangle.pair {m : ℕ} (hm : 1≤m) {c : Vertex} {s : Finset Vertex}
    (hs : IsFanTriangle m c s) {u v : Vertex} (hu : u∈s) (hv : v∈s) (hne : u≠v) :
    (graph m).Adj u v ∨
      (u.2=v.2+1 ∧ c=(u.1,v.2)) ∨ (v.2=u.2+1 ∧ c=(v.1,u.2)) := by
  rcases hs with rfl | ⟨n,hn,rfl⟩
  · exact upperTriangle_pair hm _ hu hv hne
  · exact lowerTriangle_pair hm _ _ hu hv hne

theorem different_fan_origins_intersection_adj {m : ℕ} (hm : 1≤m)
    {c d : Vertex} {s t : Finset Vertex} (hs : IsFanTriangle m c s) (ht : IsFanTriangle m d t)
    (hcd : c≠d) {u v : Vertex} (hus : u∈s) (hvs : v∈s) (hut : u∈t) (hvt : v∈t)
    (hne : u≠v) : (graph m).Adj u v := by
  by_contra he
  rcases (hs.pair hm hus hvs hne).resolve_left he with hc | hc <;>
    rcases (ht.pair hm hut hvt hne).resolve_left he with hd | hd
  · exact hcd (hc.2.trans hd.2.symm)
  · omega
  · omega
  · exact hcd (hc.2.trans hd.2.symm)

theorem graph_adj_equal_first_of_ne_height {m : ℕ} {u v : Vertex}
    (h : (graph m).Adj u v) (hne : u.2≠v.2) : u.1=v.1 := by
  rcases h with ⟨_,hh | hh⟩ <;> rcases hh with hh | hh
  · have he := congrArg Prod.snd hh
    exact False.elim (hne (by simpa only [HorizontalStep] using he.symm))
  · exact (congrArg Prod.fst hh).symm
  · have he := congrArg Prod.snd hh
    exact False.elim (hne (by simpa only [HorizontalStep] using he))
  · change u=(v.1,v.2+1) at hh
    simpa only using congrArg (fun w : Vertex => w.1) hh

theorem lowerTriangle_forbidden_pair {m : ℕ} (hm : 1≤m) (c : Vertex) (n : ℕ) :
    ¬(graph m).Adj (upperLeft c.1 c.2) (lowerVertex m c.1 c.2 (n+1)) := by
  intro h
  have he := graph_adj_equal_first_of_ne_height h (by dsimp [upperLeft,lowerVertex]; omega)
  have hp : 0<(m : ℤ)^c.2 := pow_pos (by exact_mod_cast (show 0<m by omega)) _
  have hn : 0<((n+1 : ℕ) : ℤ) := by positivity
  have hp' := mul_pos hn hp
  dsimp [upperLeft,lowerVertex] at he
  simp only [Nat.cast_add,Nat.cast_one] at hp' he
  omega

theorem upperTriangle_forbidden_pair {m : ℕ} (hm : 1≤m) (c : Vertex) :
    ¬(graph m).Adj (upperLeft c.1 c.2) (lowerVertex m c.1 c.2 m) := by
  intro h
  have he := graph_adj_equal_first_of_ne_height h (by dsimp [upperLeft,lowerVertex]; omega)
  have hp : 0<(m : ℤ)^c.2 := pow_pos (by exact_mod_cast (show 0<m by omega)) _
  have hn : 0<(m : ℤ) := by exact_mod_cast (show 0<m by omega)
  have hp' := mul_pos hn hp
  dsimp [upperLeft,lowerVertex] at he
  omega

theorem fan_clique_card_le_two {m : ℕ} (hm : 1≤m) {c : Vertex} {s t : Finset Vertex}
    (ht : IsFanTriangle m c t) (hst : s⊆t)
    (hclique : ∀ u∈s,∀ v∈s,u≠v→(graph m).Adj u v) : s.card≤2 := by
  rcases ht with rfl | ⟨n,hn,rfl⟩
  · by_cases hu : upperLeft c.1 c.2∈s
    · have hl : lowerVertex m c.1 c.2 m∉s := by
        intro hl
        apply upperTriangle_forbidden_pair hm c
        exact hclique _ hu _ hl (by intro he; have hh:=congrArg Prod.snd he; dsimp [upperLeft,lowerVertex] at hh; omega)
      apply (Finset.card_le_card (show s⊆{upperLeft c.1 c.2,upperRight m c.1 c.2} from ?_)).trans Finset.card_le_two
      intro v hv
      have hh := hst hv
      simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hh ⊢
      rcases hh with hh | hh | hh
      · exact Or.inl hh
      · exact False.elim (hl (hh ▸ hv))
      · exact Or.inr hh
    · apply (Finset.card_le_card (show s⊆{lowerVertex m c.1 c.2 m,upperRight m c.1 c.2} from ?_)).trans Finset.card_le_two
      intro v hv
      have hh := hst hv
      simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hh ⊢
      rcases hh with hh | hh | hh
      · exact False.elim (hu (hh ▸ hv))
      · exact Or.inl hh
      · exact Or.inr hh
  · by_cases hu : upperLeft c.1 c.2∈s
    · have hl : lowerVertex m c.1 c.2 (n+1)∉s := by
        intro hl
        apply lowerTriangle_forbidden_pair hm c n
        exact hclique _ hu _ hl (by intro he; have hh:=congrArg Prod.snd he; dsimp [upperLeft,lowerVertex] at hh; omega)
      apply (Finset.card_le_card (show s⊆{upperLeft c.1 c.2,lowerVertex m c.1 c.2 n} from ?_)).trans Finset.card_le_two
      intro v hv
      have hh := hst hv
      simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hh ⊢
      rcases hh with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr hh
      · exact False.elim (hl (hh ▸ hv))
    · apply (Finset.card_le_card (show s⊆{lowerVertex m c.1 c.2 n,lowerVertex m c.1 c.2 (n+1)} from ?_)).trans Finset.card_le_two
      intro v hv
      have hh := hst hv
      simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hh ⊢
      rcases hh with hh | hh | hh
      · exact False.elim (hu (hh ▸ hv))
      · exact Or.inl hh
      · exact Or.inr hh

theorem different_fan_origins_shared_face {m K : ℕ} {A B : ℤ} (hm : 1≤m)
    {c d : Vertex} {s t u : Finset Vertex} (hs : IsFanTriangle m c s) (ht : IsFanTriangle m d t)
    (hcd : c≠d) (hus : u⊆s) (hut : u⊆t) (hne : u.Nonempty)
    (hvertices : u⊆carrierVertices K A B) :
    (∃ v∈carrierVertices K A B,u⊆{v}) ∨
      ∃ v∈carrierVertices K A B,∃ w∈carrierVertices K A B,(graph m).Adj v w ∧ u⊆{v,w} := by
  have hclique : ∀ v∈u,∀ w∈u,v≠w→(graph m).Adj v w := fun v hv w hw hne =>
    different_fan_origins_intersection_adj hm hs ht hcd (hus hv) (hus hw) (hut hv) (hut hw) hne
  have hcard := fan_clique_card_le_two hm hs hus hclique
  by_cases hc : u.card≤1
  · obtain ⟨v,hv⟩ := hne
    refine Or.inl ⟨v,hvertices hv,?_⟩
    intro w hw
    exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hc) w hw v hv)
  · have hc' : u.card=2 := by omega
    obtain ⟨v,w,hvw,he⟩ := Finset.card_eq_two.mp hc'
    have hv : v∈u := by simp [he]
    have hw : w∈u := by simp [he]
    exact Or.inr ⟨v,hvertices hv,w,hvertices hw,hclique v hv w hw hvw,by rw [he]⟩

theorem upperLeft_lower_adj_iff {m : ℕ} (hm : 1≤m) (c : Vertex) (n : ℕ) :
    (graph m).Adj (upperLeft c.1 c.2) (lowerVertex m c.1 c.2 n) ↔ n=0 := by
  constructor
  · intro h
    have he := graph_adj_equal_first_of_ne_height h (by dsimp [upperLeft,lowerVertex]; omega)
    have hp : 0<(m : ℤ)^c.2 := pow_pos (by exact_mod_cast (show 0<m by omega)) _
    have he' : (n : ℤ)*(m : ℤ)^c.2=0 := by dsimp [upperLeft,lowerVertex] at he; omega
    rcases mul_eq_zero.mp he' with hn | hn
    · exact_mod_cast hn
    · exact False.elim (hp.ne' hn)
  · rintro rfl
    exact (vertical_adj (x := lowerVertex m c.1 c.2 0) (y := upperLeft c.1 c.2)
      (by simp [VerticalStep,lowerVertex,upperLeft])).symm

theorem lowerTriangle_skeleton_edge {m : ℕ} (hm : 1≤m) (c : Vertex) (n : ℕ)
    {u v : Vertex} (hu : u∈lowerTriangle m c n) (hv : v∈lowerTriangle m c n)
    (hadj : (graph m).Adj u v) :
    ({u,v} : Finset Vertex)={lowerVertex m c.1 c.2 n,lowerVertex m c.1 c.2 (n+1)} ∨
      (n=0 ∧ ({u,v} : Finset Vertex)={upperLeft c.1 c.2,lowerVertex m c.1 c.2 0}) := by
  have hne := hadj.ne
  simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · have hn := (upperLeft_lower_adj_iff hm c n).mp hadj
    exact Or.inr ⟨hn,by rw [hn]⟩
  · exact False.elim (lowerTriangle_forbidden_pair hm c n hadj)
  · have hn := (upperLeft_lower_adj_iff hm c n).mp hadj.symm
    exact Or.inr ⟨hn,by rw [hn]; exact Finset.pair_comm _ _⟩
  · exact False.elim (hne rfl)
  · exact Or.inl rfl
  · exact False.elim (lowerTriangle_forbidden_pair hm c n hadj.symm)
  · exact Or.inl (Finset.pair_comm _ _)
  · exact False.elim (hne rfl)

theorem upperTriangle_skeleton_edge {m : ℕ} (hm : 1≤m) (c : Vertex)
    {u v : Vertex} (hu : u∈upperTriangle m c) (hv : v∈upperTriangle m c)
    (hadj : (graph m).Adj u v) :
    ({u,v} : Finset Vertex)={upperLeft c.1 c.2,upperRight m c.1 c.2} ∨
      ({u,v} : Finset Vertex)={lowerVertex m c.1 c.2 m,upperRight m c.1 c.2} := by
  have hne := hadj.ne
  simp only [upperTriangle,Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · exact False.elim (upperTriangle_forbidden_pair hm c hadj)
  · exact Or.inl rfl
  · exact False.elim (upperTriangle_forbidden_pair hm c hadj.symm)
  · exact False.elim (hne rfl)
  · exact Or.inr rfl
  · exact Or.inl (Finset.pair_comm _ _)
  · exact Or.inr (Finset.pair_comm _ _)
  · exact False.elim (hne rfl)

end AbelianTargets.IntervalCarriers


