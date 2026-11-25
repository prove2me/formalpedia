-- Prove2me | solution 1 for LocalHirschHyperfinite.theorem1_1
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-11-25T16:16:55.7758+00:00
-- url     : https://prove2.me/submissions/0234569d-e379-4b48-aa4b-c9a7365ed6a6

import Definitions.Def_LocalHirsch20261125
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Logic.Relation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Bases
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Piecewise

-- BEGIN COMPLETE MODULE HirschProof.Near
section
                                                       
                             
                                    
                               

set_option autoImplicit false

namespace LocalHirschHyperfinite

open Set

/-- An integer-valued extended orbit metric, encoded by its closed balls.
The maps enumerate possible displacements. Uniform finiteness of each ball
is kept separate from this countable enumeration. -/
structure BorelNear (X : Type*) [MeasurableSpace X] where
  near : ℕ → X → X → Prop
  refl : ∀ r x, near r x x
  symm : ∀ r {x y}, near r x y → near r y x
  mono : ∀ {r s}, r ≤ s → ∀ {x y}, near r x y → near s x y
  triangle : ∀ {r s x y z}, near r x y → near s y z → near (r+s) x z
  zero : ∀ {x y}, near 0 x y → x = y
  borel : ∀ r, MeasurableSet {p : X × X | near r p.1 p.2}
  moves : ℕ → X → X
  measurable_moves : ∀ i, Measurable (moves i)
  moves_cover : ∀ {r x y}, near r x y → ∃ i, moves i x = y
  uniformly_finite : ∀ r, ∃ N : ℕ, ∀ x, ∃ t : Finset X, t.card ≤ N ∧
    ∀ y, near r x y → y ∈ t

namespace BorelNear

variable {X : Type*} [MeasurableSpace X] (D : BorelNear X)

def bounded (A : Set X) (r : ℕ) : Prop :=
  ∀ ⦃x y⦄, x ∈ A → y ∈ A → D.near r x y

def ball (x : X) (r : ℕ) : Set X := {y | D.near r x y}

def thicken (A : Set X) (r : ℕ) : Set X :=
  {x | ∃ y ∈ A, D.near r x y}

theorem subset_thicken (A : Set X) (r : ℕ) : A ⊆ D.thicken A r :=
  fun x hx => ⟨x,hx,D.refl r x⟩

theorem thicken_mono_set {A B : Set X} (h : A ⊆ B) (r : ℕ) :
    D.thicken A r ⊆ D.thicken B r :=
  fun _ ⟨y,hy,hxy⟩ => ⟨y,h hy,hxy⟩

theorem thicken_mono_radius (A : Set X) {r s : ℕ} (h : r ≤ s) :
    D.thicken A r ⊆ D.thicken A s :=
  fun _ ⟨y,hy,hxy⟩ => ⟨y,hy,D.mono h hxy⟩

theorem thicken_thicken (A : Set X) (r s : ℕ) :
    D.thicken (D.thicken A r) s ⊆ D.thicken A (s+r) := by
  rintro x ⟨y,⟨z,hz,hyz⟩,hxy⟩
  exact ⟨z,hz,D.triangle hxy hyz⟩

def edge (r : ℕ) (A : Set X) (x y : X) : Prop :=
  x ∈ A ∧ y ∈ A ∧ D.near r x y

/-- Reachability by finitely many radius-r steps internal to A. -/
def comp (r : ℕ) (A : Set X) (x y : X) : Prop :=
  x ∈ A ∧ Relation.ReflTransGen (D.edge r A) x y

theorem comp_start {r : ℕ} {A : Set X} {x y : X} (h : D.comp r A x y) : x ∈ A :=
  h.1

theorem comp_end {r : ℕ} {A : Set X} {x y : X} (h : D.comp r A x y) : y ∈ A := by
  rcases h with ⟨hx,h⟩
  cases h
  · exact hx
  · exact ‹D.edge r A _ _›.2.1

theorem comp_refl {r : ℕ} {A : Set X} {x : X} (h : x ∈ A) : D.comp r A x x :=
  ⟨h,.refl⟩

theorem comp_single {r : ℕ} {A : Set X} {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) (h : D.near r x y) : D.comp r A x y :=
  ⟨hx,.single ⟨hx,hy,h⟩⟩

theorem comp_trans {r : ℕ} {A : Set X} {x y z : X}
    (h : D.comp r A x y) (h' : D.comp r A y z) : D.comp r A x z :=
  ⟨h.1,h.2.trans h'.2⟩

theorem comp_symm {r : ℕ} {A : Set X} {x y : X}
    (h : D.comp r A x y) : D.comp r A y x := by
  refine ⟨D.comp_end h,?_⟩
  rcases h with ⟨_,h⟩
  induction h with
  | refl => exact .refl
  | tail h e ih => exact (Relation.ReflTransGen.single ⟨e.2.1,e.1,D.symm r e.2.2⟩).trans ih

theorem comp_map {Y : Type*} [MeasurableSpace Y] {B : BorelNear Y}
    {A : Set X} {U : Set Y} {r s : ℕ} (f : X → Y) (hf : MapsTo f A U)
    (hstep : ∀ ⦃x y⦄, x ∈ A → y ∈ A → D.near r x y → B.near s (f x) (f y))
    {x y : X} (h : D.comp r A x y) : B.comp s U (f x) (f y) := by
  refine ⟨hf h.1,?_⟩
  rcases h with ⟨_,h⟩
  induction h with
  | refl => exact .refl
  | tail h e ih => exact ih.tail ⟨hf e.1,hf e.2.1,hstep e.1 e.2.1 e.2.2⟩

theorem comp_mono {A B : Set X} {r s : ℕ} (h : A ⊆ B) (hrs : r ≤ s)
    {x y : X} (hp : D.comp r A x y) : D.comp s B x y := by
  apply D.comp_map (id : X → X) h _ hp
  intro u v _ _ huv
  exact D.mono hrs huv

def boundComp (A : Set X) (r b : ℕ) : Prop :=
  ∀ ⦃x y⦄, D.comp r A x y → D.near b x y

theorem boundComp_mono {A B : Set X} {r s b c : ℕ}
    (hAB : A ⊆ B) (hrs : r ≤ s) (hbc : b ≤ c) (h : D.boundComp B s b) :
    D.boundComp A r c := by
  intro x y hxy
  exact D.mono hbc (h (D.comp_mono hAB hrs hxy))

theorem exists_near_of_comp {A : Set X} {r : ℕ} {x y : X} (h : D.comp r A x y) :
    ∃ n, D.near n x y := by
  rcases h with ⟨_,h⟩
  induction h with
  | refl => exact ⟨0,D.refl 0 x⟩
  | tail h e ih =>
    obtain ⟨k,hk⟩ := ih
    exact ⟨k+r,D.triangle hk e.2.2⟩

theorem ball_finite (r : ℕ) (x : X) : (D.ball x r).Finite := by
  obtain ⟨_,h⟩ := D.uniformly_finite r
  obtain ⟨t,_,ht⟩ := h x
  exact t.finite_toSet.subset (fun y hy => ht y hy)

theorem measurableSet_ball (r : ℕ) (x : X) : MeasurableSet (D.ball x r) :=
  (D.borel r).preimage (measurable_const.prodMk measurable_id)

theorem measurableSet_thicken {A : Set X} (hA : MeasurableSet A) (r : ℕ) :
    MeasurableSet (D.thicken A r) := by
  have heq : D.thicken A r = ⋃ i : ℕ,
      {x | D.moves i x ∈ A ∧ D.near r x (D.moves i x)} := by
    ext x
    simp only [thicken,mem_setOf_eq,mem_iUnion]
    constructor
    · rintro ⟨y,hy,hxy⟩
      obtain ⟨i,rfl⟩ := D.moves_cover hxy
      exact ⟨i,hy,hxy⟩
    · rintro ⟨i,hi,hxy⟩
      exact ⟨D.moves i x,hi,hxy⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  exact (hA.preimage (D.measurable_moves i)).inter
    ((D.borel r).preimage (measurable_id.prodMk (D.measurable_moves i)))

private def traceEnd (D : BorelNear X) : List ℕ → X → X
  | [], x => x
  | i :: w, x => traceEnd D w (D.moves i x)

private def traceGood (D : BorelNear X) (r : ℕ) (A : Set X) : List ℕ → X → Prop
  | [], x => x ∈ A
  | i :: w, x => x ∈ A ∧ D.near r x (D.moves i x) ∧ traceGood D r A w (D.moves i x)

private theorem measurable_traceEnd (w : List ℕ) : Measurable (D.traceEnd w) := by
  induction w with
  | nil => exact measurable_id
  | cons i w ih => exact ih.comp (D.measurable_moves i)

private theorem measurableSet_traceGood {A : Set X} (hA : MeasurableSet A)
    (r : ℕ) (w : List ℕ) : MeasurableSet {x | D.traceGood r A w x} := by
  induction w with
  | nil => exact hA
  | cons i w ih =>
    exact hA.inter (((D.borel r).preimage (measurable_id.prodMk (D.measurable_moves i))).inter
      (ih.preimage (D.measurable_moves i)))

private theorem traceGood_start {r : ℕ} {A : Set X} {w : List ℕ} {x : X}
    (h : D.traceGood r A w x) : x ∈ A := by
  cases w with
  | nil => exact h
  | cons => exact h.1

private theorem comp_of_traceGood {r : ℕ} {A : Set X} {w : List ℕ} {x : X}
    (h : D.traceGood r A w x) : D.comp r A x (D.traceEnd w x) := by
  induction w generalizing x with
  | nil => exact D.comp_refl h
  | cons i w ih =>
    exact D.comp_trans (D.comp_single h.1 (D.traceGood_start h.2.2) h.2.1) (ih h.2.2)

private theorem exists_trace_of_comp {r : ℕ} {A : Set X} {x y : X}
    (h : D.comp r A x y) :
    ∃ w : List ℕ, D.traceGood r A w x ∧ D.traceEnd w x = y := by
  rcases h with ⟨hx,h⟩
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[],hx,rfl⟩
  | head e h ih =>
    have hh : _ := e.2.1
    obtain ⟨w,hw,he⟩ := ih hh
    obtain ⟨i,hi⟩ := D.moves_cover e.2.2
    refine ⟨i::w,⟨e.1,?_,?_⟩,?_⟩
    · rw [hi]; exact e.2.2
    · rw [hi]; exact hw
    · simp only [traceEnd,hi]; exact he

theorem comp_iff_trace {r : ℕ} {A : Set X} {x y : X} :
    D.comp r A x y ↔ ∃ w : List ℕ, D.traceGood r A w x ∧ D.traceEnd w x = y := by
  refine ⟨D.exists_trace_of_comp,?_⟩
  rintro ⟨w,hw,rfl⟩
  exact D.comp_of_traceGood hw

theorem measurableSet_comp [MeasurableEq X]
    {A : Set X} (hA : MeasurableSet A) (r : ℕ) :
    MeasurableSet {p : X×X | D.comp r A p.1 p.2} := by
  have heq : {p : X×X | D.comp r A p.1 p.2} = ⋃ w : List ℕ,
      {p : X×X | D.traceGood r A w p.1 ∧ D.traceEnd w p.1 = p.2} := by
    ext p
    simp only [mem_setOf_eq,mem_iUnion, D.comp_iff_trace]
  rw [heq]
  exact MeasurableSet.iUnion fun w =>
    ((D.measurableSet_traceGood hA r w).preimage measurable_fst).inter
      (measurableSet_eq_fun ((D.measurable_traceEnd w).comp measurable_fst) measurable_snd)

/-- The points whose component inside A meets U. -/
def saturate (r : ℕ) (A U : Set X) : Set X :=
  {x | ∃ y ∈ U, D.comp r A x y}

theorem measurableSet_saturate {A U : Set X} (hA : MeasurableSet A)
    (hU : MeasurableSet U) (r : ℕ) : MeasurableSet (D.saturate r A U) := by
  have heq : D.saturate r A U = ⋃ w : List ℕ,
      {x | D.traceGood r A w x ∧ D.traceEnd w x ∈ U} := by
    ext x
    simp only [saturate,mem_setOf_eq,mem_iUnion,D.comp_iff_trace]
    constructor
    · rintro ⟨y,hy,w,hw,rfl⟩; exact ⟨w,hw,hy⟩
    · rintro ⟨w,hw,hy⟩; exact ⟨D.traceEnd w x,hy,w,hw,rfl⟩
  rw [heq]
  exact MeasurableSet.iUnion fun w =>
    (D.measurableSet_traceGood hA r w).inter (hU.preimage (D.measurable_traceEnd w))

end BorelNear

variable {X : Type*} [MeasurableSpace X]

/-- Finite Borel covers at every radius, with uniformly bounded components.
A measurable coloring is equivalent to such a cover by selecting its first set. -/
def BorelAsdimLE (D : BorelNear X) (b : ℕ) (A : Set X) : Prop :=
  ∀ r : ℕ, ∃ U : Fin (b+1) → Set X, ∃ R : ℕ,
    (∀ i, U i ⊆ A) ∧ (∀ i, MeasurableSet (U i)) ∧
    (∀ x ∈ A, ∃ i, x ∈ U i) ∧ ∀ i, D.boundComp (U i) r R

def HasCoreExhaustion (D : BorelNear X) : Prop :=
  ∃ b : ℕ, ∃ K : ℕ → Set X, Monotone K ∧ (∀ j, MeasurableSet (K j)) ∧
    (∀ x, ∃ j, x ∈ K j) ∧ ∀ j, BorelAsdimLE D b (K j)

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.Near

-- BEGIN COMPLETE MODULE HirschProof.NearGeometry
section
                       
                                              

set_option autoImplicit false

namespace LocalHirschHyperfinite.BorelNear
open Set
variable {X : Type*} [MeasurableSpace X] (D : BorelNear X)

theorem mixed_bound_of_thicken {A U : Set X} {r a b : ℕ}
    (hAU : A ⊆ D.thicken U a) (h : D.boundComp U (a+r+a) b) :
    D.boundComp A (r) (a+b+a) := by
  classical
  let f : X → X := fun x => if hx : x ∈ A then Classical.choose (hAU hx) else x
  have hf {x : X} (hx : x ∈ A) : f x ∈ U ∧ D.near a x (f x) := by
    simp only [f,dif_pos hx]
    exact Classical.choose_spec (hAU hx)
  intro x y hxy
  have hx := hf (D.comp_start hxy)
  have hy := hf (D.comp_end hxy)
  have hc : D.comp (a+r+a) U (f x) (f y) := by
    apply D.comp_map f (fun _ hz => (hf hz).1) _ hxy
    intro u v hu hv huv
    exact D.triangle (D.triangle (D.symm a (hf hu).2) huv) (hf hv).2
  exact D.triangle (D.triangle hx.2 (h hc)) (D.symm a hy.2)

theorem boundComp_thicken {U : Set X} {r a b : ℕ}
    (h : D.boundComp U (a+r+a) b) : D.boundComp (D.thicken U a) r (a+b+a) :=
  D.mixed_bound_of_thicken Subset.rfl h

theorem asdim_thicken {U : Set X} {b a : ℕ} (h : BorelAsdimLE D b U) :
    BorelAsdimLE D b (D.thicken U a) := by
  intro r
  obtain ⟨V,R,hV,hVm,hcov,hB⟩ := h (a+r+a)
  refine ⟨fun i => D.thicken (V i) a,a+R+a,
    fun i => D.thicken_mono_set (hV i) a,
    fun i => D.measurableSet_thicken (hVm i) a,?_,fun i => D.boundComp_thicken (hB i)⟩
  rintro x ⟨y,hy,hxy⟩
  obtain ⟨i,hi⟩ := hcov y hy
  exact ⟨i,y,hi,hxy⟩

theorem asdim_restrict {U A : Set X} {b : ℕ} (hU : BorelAsdimLE D b U)
    (hA : MeasurableSet A) (hAU : A ⊆ U) : BorelAsdimLE D b A := by
  intro r
  obtain ⟨V,R,hV,hVm,hcov,hB⟩ := hU r
  refine ⟨fun i => V i ∩ A,R, fun _ => inter_subset_right,
    fun i => (hVm i).inter hA,?_,fun i => D.boundComp_mono inter_subset_left le_rfl le_rfl (hB i)⟩
  intro x hx
  obtain ⟨i,hi⟩ := hcov x (hAU hx)
  exact ⟨i,hi,hx⟩

theorem comp_mono_near (D' : BorelNear X) {A : Set X} {r s : ℕ}
    (ht : ∀ ⦃x y⦄, x ∈ A → y ∈ A → D.near r x y → D'.near s x y)
    {x y : X} (h : D.comp r A x y) : D'.comp s A x y := by
  exact D.comp_map id (fun _ ha => ha) ht h

private def subgraph (r : ℕ) (t : Finset X) : SimpleGraph (↑t : Type _) where
  Adj x y := D.near r x.val y.val ∧ x ≠ y
  symm := fun _ _ h => ⟨D.symm r h.1,h.2.symm⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

private theorem walk_near {r : ℕ} {t : Finset X} {u v : (↑t : Type _)}
    (p : (D.subgraph r t).Walk u v) : D.near (r*p.length) u.val v.val := by
  induction p with
  | nil => exact D.refl _ _
  | cons hu p ih =>
    simpa [SimpleGraph.Walk.length_cons,Nat.mul_add,Nat.add_comm] using D.triangle hu.1 ih

theorem near_mul_card_of_comp {r : ℕ} {A : Set X} {x y : X}
    (h : D.comp r A x y) (t : Finset X) (ht : ∀ z, D.comp r A x z → z ∈ t) :
    D.near (r*t.card) x y := by
  classical
  have hx := h.1
  have hxt := ht x (D.comp_refl hx)
  let u : (↑t : Type _) := ⟨x,hxt⟩
  have hw {z : X} (hz : Relation.ReflTransGen (D.edge r A) x z) :
      Nonempty ((D.subgraph r t).Walk u ⟨z,ht z ⟨hx,hz⟩⟩) := by
    induction hz with
    | refl => exact ⟨.nil⟩
    | @tail b c hb hbc ih =>
      by_cases he : b = c
      · subst c; exact ih
      · obtain ⟨p⟩ := ih
        exact ⟨p.concat ⟨hbc.2.2,fun hbc' => he (congrArg Subtype.val hbc')⟩⟩
  obtain ⟨p⟩ := hw h.2
  have hlen : p.bypass.length ≤ t.card := by
    have hlt := p.bypass_isPath.length_lt
    simpa using hlt.le
  exact D.mono (Nat.mul_le_mul_left r hlen) (D.walk_near p.bypass)

/-- A uniform cardinality bound on the components converts to a diameter bound. -/
theorem boundComp_of_small {A : Set X} {r N : ℕ}
    (h : ∀ x, ∃ t : Finset X, t.card ≤ N ∧ ∀ y, D.comp r A x y → y ∈ t) :
    D.boundComp A r (r*N) := by
  intro x y hxy
  obtain ⟨t,ht,hxt⟩ := h x
  exact D.mono (Nat.mul_le_mul_left r ht) (D.near_mul_card_of_comp hxy t hxt)

theorem boundComp_of_comparison (D' : BorelNear X) {A : Set X} {r s R : ℕ}
    (hstep : ∀ ⦃x y⦄, x ∈ A → y ∈ A → D.near r x y → D'.near s x y)
    (h : D'.boundComp A s R) : ∃ L, D.boundComp A r L := by
  obtain ⟨N,hN⟩ := D'.uniformly_finite R
  refine ⟨r*N,D.boundComp_of_small (fun x => ?_)⟩
  obtain ⟨t,ht,hxt⟩ := hN x
  exact ⟨t,ht,fun _ hxy => hxt _ (h (D.comp_mono_near D' hstep hxy))⟩

end LocalHirschHyperfinite.BorelNear

end
-- END COMPLETE MODULE HirschProof.NearGeometry

-- BEGIN COMPLETE MODULE HirschProof.OrthogonalCovers
section
                               

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

variable {X : Type*} [MeasurableSpace X]

/-- A finite Borel cover with a common bound on its same-set components. -/
structure ScaleCover (D : BorelNear X) (d r : ℕ) where
  sites : Fin (d+1) → Set X
  measurable_sites : ∀ i, MeasurableSet (sites i)
  covers : ∀ x, ∃ i, x ∈ sites i
  bound : ℕ
  bounded_sites : ∀ i, D.boundComp (sites i) r bound

def Divides (A B : Set X) : Prop :=
  (∃ x ∈ B, x ∈ A) ∧ (∃ y ∈ B, y ∉ A)

theorem Divides.mono_right {A B C : Set X} (h : Divides A B) (hBC : B ⊆ C) :
    Divides A C := by
  obtain ⟨⟨x,hx,hx'⟩,⟨y,hy,hy'⟩⟩ := h
  exact ⟨⟨x,hBC hx,hx'⟩,⟨y,hBC hy,hy'⟩⟩

namespace BorelNear

variable (D : BorelNear X)

private def enlarge (r : ℕ) (A U : Set X) := U ∪ D.saturate r A U

private theorem subset_enlarge (r : ℕ) (A U : Set X) : U ⊆ D.enlarge r A U :=
  subset_union_left

private theorem measurableSet_enlarge {r : ℕ} {A U : Set X}
    (hA : MeasurableSet A) (hU : MeasurableSet U) :
    MeasurableSet (D.enlarge r A U) :=
  hU.union (D.measurableSet_saturate hA hU _)

private theorem enlarge_subset_thicken {r b : ℕ} {A U : Set X}
    (h : D.boundComp A r b) : D.enlarge r A U ⊆ D.thicken U b := by
  rintro x (hx | ⟨y,hy,hxy⟩)
  · exact D.subset_thicken U b hx
  · exact ⟨y,hy,h hxy⟩

private def foldEnlarge (S : ℕ → Set X → Set X) (k : ℕ) :
    ℕ → Set X → Set X
  | 0, U => U
  | n+1, U => S k (foldEnlarge S (k+1) n U)

private theorem foldEnlarge_append (S : ℕ → Set X → Set X) (k n m : ℕ) (U : Set X) :
    foldEnlarge S k (n+m) U =
      foldEnlarge S k n (foldEnlarge S (k+n) m U) := by
  induction n generalizing k with
  | zero => simp [foldEnlarge]
  | succ n ih =>
    rw [show n+1+m = n+m+1 by omega,foldEnlarge,ih,foldEnlarge]
    rw [show k+1+n = k+(n+1) by omega]

private theorem subset_foldEnlarge {S : ℕ → Set X → Set X}
    (hS : ∀ k U, U ⊆ S k U) (k n : ℕ) (U : Set X) :
    U ⊆ foldEnlarge S k n U := by
  induction n generalizing k with
  | zero => exact Subset.rfl
  | succ n ih => exact (ih (k+1)).trans (hS k _)

private theorem measurableSet_foldEnlarge {S : ℕ → Set X → Set X}
    (hS : ∀ k U, MeasurableSet U → MeasurableSet (S k U))
    (k n : ℕ) {U : Set X} (hU : MeasurableSet U) :
    MeasurableSet (foldEnlarge S k n U) := by
  induction n generalizing k with
  | zero => exact hU
  | succ n ih => exact hS k _ (ih (k+1))

private theorem foldEnlarge_subset_thicken {S : ℕ → Set X → Set X}
    {off c : ℕ → ℕ} (hoff : ∀ k, off (k+1) = off k + c k)
    (hS : ∀ k U, S k U ⊆ D.thicken U (c k))
    (k n : ℕ) (U : Set X) :
    foldEnlarge S k n U ⊆ D.thicken U (off (k+n) - off k) := by
  have hmono : Monotone off := monotone_nat_of_le_succ (by intro i; rw [hoff]; omega)
  induction n generalizing k with
  | zero => exact D.subset_thicken U _
  | succ n ih =>
    have hle := hmono (show k+1 ≤ k+1+n by omega)
    have he : c k + (off (k+1+n)-off (k+1)) = off (k+(n+1))-off k := by
      rw [show k+1+n = k+(n+1) by omega] at *
      have := hoff k
      omega
    rw [← he]
    exact (hS k _).trans ((D.thicken_mono_set (ih (k+1)) _).trans (D.thicken_thicken _ _ _))

private def offset (r s : ℕ) (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 =>
    let t := offset r s b n
    let a := max s (2*r) + t
    t + (4*a + b a)

/-- Orthogonal covers on a fixed metric. One coordinate of a fixed ball is
split by at most one cover. This is the integer-metric form of Corollary 7.2
of Conley–Jackson–Marks–Seward–Tucker-Drob. -/
theorem exists_orthogonal_covers {d : ℕ} (hd : BorelAsdimLE D d univ) (r s : ℕ) :
    ∃ U : ℕ → ScaleCover D d s,
      ∀ ⦃n m : ℕ⦄, n < m → ∀ (i : Fin (d+1)) (x : X),
        Divides ((U n).sites i) (D.ball x r) →
        ¬ Divides ((U m).sites i) (D.ball x r) := by
  classical
  choose V b _ hVm hVcov hVb using fun t => hd (6*t)
  let off := offset r s b
  let a (n : ℕ) := max s (2*r) + off n
  let T (i : Fin (d+1)) (n : ℕ) := D.thicken (V (a n) i) (2*a n)
  let S (i : Fin (d+1)) (n : ℕ) := D.enlarge (2*a n) (T i n)
  let W (n : ℕ) (i : Fin (d+1)) := foldEnlarge (S i) 0 n (V (a n) i)
  have hsub (i : Fin (d+1)) (n : ℕ) (U : Set X) : U ⊆ S i n U :=
    D.subset_enlarge _ _ _
  have hmeas (i : Fin (d+1)) (n : ℕ) (U : Set X) (hU : MeasurableSet U) :
      MeasurableSet (S i n U) :=
    D.measurableSet_enlarge (D.measurableSet_thicken (hVm (a n) i) _) hU
  have hcost (i : Fin (d+1)) (n : ℕ) (U : Set X) :
      S i n U ⊆ D.thicken U (4*a n + b (a n)) := by
    apply D.enlarge_subset_thicken
    have he : 2*a n + 2*a n + 2*a n = 6*a n := by omega
    have hc := D.boundComp_thicken (U := V (a n) i) (r := 2*a n) (a := 2*a n)
      (b := b (a n)) (he.symm ▸ hVb (a n) i)
    apply D.boundComp_mono Subset.rfl le_rfl _ hc
    omega
  have hfold (i : Fin (d+1)) (n : ℕ) (U : Set X) :
      foldEnlarge (S i) 0 n U ⊆ D.thicken U (off n) := by
    simpa [show off 0 = 0 by rfl] using
      D.foldEnlarge_subset_thicken (off := off) (c := fun k => 4*a k + b (a k))
        (fun _ => rfl) (hcost i) 0 n U
  let cover (n : ℕ) : ScaleCover D d s := {
    sites := W n
    measurable_sites := fun i => measurableSet_foldEnlarge (hmeas i) 0 n (hVm (a n) i)
    covers := by
      intro x
      obtain ⟨i,hi⟩ := hVcov (a n) x (mem_univ x)
      exact ⟨i,subset_foldEnlarge (hsub i) 0 n _ hi⟩
    bound := off n + b (a n) + off n
    bounded_sites := by
      intro i
      apply D.mixed_bound_of_thicken (hfold i n _)
      apply D.boundComp_mono Subset.rfl _ le_rfl (hVb (a n) i)
      simp only [a]
      omega }
  refine ⟨cover,?_⟩
  intro n m hnm i x hdiv hbad
  obtain ⟨u,hxu,hu⟩ := hdiv.1
  obtain ⟨v,hv,huv⟩ := hfold i n _ hu
  obtain ⟨z,hxz,hz⟩ := hbad.1
  obtain ⟨w,hxw,hw⟩ := hbad.2
  change z ∈ W m i at hz
  change w ∉ W m i at hw
  let Y := foldEnlarge (S i) (n+1) (m-(n+1)) (V (a m) i)
  have heq : W m i = foldEnlarge (S i) 0 n (S i n Y) := by
    calc
      W m i = foldEnlarge (S i) 0 (n + ((m-(n+1))+1)) (V (a m) i) := by
        rw [show n + ((m-(n+1))+1) = m by omega]
      _ = foldEnlarge (S i) 0 n (S i n Y) := by
        rw [foldEnlarge_append]
        simp [foldEnlarge,Y]
  have huxz : D.near (2*r) u z := by
    have h : D.near (r+r) u z := D.triangle (D.symm r hxu) hxz
    exact D.mono (by omega) h
  rw [heq] at hz
  obtain ⟨q,hq,hzq⟩ := hfold i n (S i n Y) hz
  have huq : D.near (a n) u q := by
    change D.near (max s (2*r) + off n) u q
    exact D.mono (Nat.add_le_add_right (le_max_right _ _) _) (D.triangle huxz hzq)
  have huw : D.near (a n) u w := by
    change D.near (max s (2*r) + off n) u w
    exact D.mono (by omega) (D.triangle (D.symm r hxu) hxw)
  have hball {p : X} (hp : D.near (a n) u p) : p ∈ T i n := by
    have hle : a n + off n ≤ 2*a n := by simp only [a]; omega
    exact ⟨v,hv,D.mono hle (D.triangle (D.symm _ hp) huv)⟩
  have hwq : D.comp (2*a n) (T i n) w q := by
    apply D.comp_single (hball huw) (hball huq)
    exact D.mono (by omega) (D.triangle (D.symm _ huw) huq)
  have hwS : w ∈ S i n Y := by
    rcases hq with hq | ⟨p,hp,hqp⟩
    · exact Or.inr ⟨q,hq,hwq⟩
    · exact Or.inr ⟨p,hp,D.comp_trans hwq hqp⟩
  apply hw
  rw [heq]
  exact subset_foldEnlarge (hsub i) 0 n _ hwS

end BorelNear
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.OrthogonalCovers

-- BEGIN COMPLETE MODULE HirschProof.CarryCovers
section
                                   
                                       
                                                          

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set
open scoped BigOperators

variable {X : Type*} [MeasurableSpace X]

noncomputable def countTrue {I : Type*} [Fintype I] (P : I → Prop) : ℕ := by
  classical exact (Finset.univ.filter P).card

theorem countTrue_true {I : Type*} [Fintype I] : countTrue (fun _ : I => True) = Fintype.card I := by
  classical simp [countTrue]

theorem countTrue_fin_succ {m : ℕ} (P : Fin (m+1) → Prop) : by
    classical exact countTrue P = (if P 0 then 1 else 0) + countTrue (P ∘ Fin.succ) := by
  classical
  simp only [countTrue,Finset.card_filter,Fin.sum_univ_succ,Function.comp_def]

theorem countTrue_le_of_pick {I J : Type*} [Fintype I] [Fintype J]
    {P : I → Prop} {Q : J → Prop} {W : I → J → Prop}
    (hpick : ∀ i, P i → ∃ j, Q j ∧ W i j)
    (hsep : ∀ i i' j, W i j → W i' j → i=i') : countTrue P ≤ countTrue Q := by
  classical
  let f (i : {i : I // P i}) : {j : J // Q j} :=
    ⟨Classical.choose (hpick i.val i.property),
      (Classical.choose_spec (hpick i.val i.property)).1⟩
  have hf : Function.Injective f := by
    intro i i' h
    apply Subtype.ext
    have hi : W i.val (f i).val := (Classical.choose_spec (hpick i.val i.property)).2
    have hi' : W i'.val (f i').val := (Classical.choose_spec (hpick i'.val i'.property)).2
    rw [← h] at hi'
    exact hsep _ _ _ hi hi'
  simpa only [countTrue,Fintype.card_subtype] using Fintype.card_le_of_injective f hf

def ScaleCover.splits {D : BorelNear X} {d r : ℕ}
    (C : ScaleCover D d r) (A : Set X) : Prop :=
  ∃ i, Divides (C.sites i) A

namespace MetricCarry

variable (D : ℕ → BorelNear X) (d : ℕ → ℕ)

/-- One permanent cover, marked by index zero, and a finite reserve of
auxiliary covers. A later stage can consume an auxiliary cover's splits. -/
structure Batch (n : ℕ) where
  radius : ℕ
  stage_le : n ≤ radius
  covers : Fin (d (n+1)+2) → ScaleCover (D n) (d n) (2*radius)

variable {D d}

def Batch.main {n : ℕ} (P : Batch D d n) := P.covers 0

def Batch.spare {n : ℕ} (P : Batch D d n) (i : Fin (d (n+1)+1)) := P.covers i.succ

private def growSite {n : ℕ} (P : Batch D d n) (i : Fin (d (n+1)+1))
    (U : Set X) : Set X :=
  ⋃ j : Fin (d n+1), (D n).saturate (2*P.radius) ((P.spare i).sites j) U

private theorem measurableSet_growSite {n : ℕ} (P : Batch D d n) (i : Fin (d (n+1)+1))
    {U : Set X} (hU : MeasurableSet U) : MeasurableSet (growSite P i U) :=
  MeasurableSet.iUnion fun j =>
    (D n).measurableSet_saturate ((P.spare i).measurable_sites j) hU _

private theorem subset_growSite {n : ℕ} (P : Batch D d n) (i : Fin (d (n+1)+1))
    (U : Set X) : U ⊆ growSite P i U := by
  intro x hx
  obtain ⟨j,hj⟩ := (P.spare i).covers x
  exact mem_iUnion.mpr ⟨j,x,hx,(D n).comp_refl hj⟩

private theorem growSite_subset_thicken {n r : ℕ} (P : Batch D d n)
    (i : Fin (d (n+1)+1)) (U : Set X)
    (hmono : ∀ ⦃r x y⦄, (D n).near r x y → (D (n+1)).near r x y)
    (hb : (P.spare i).bound ≤ r) :
    growSite P i U ⊆ (D (n+1)).thicken U r := by
  intro x hx
  obtain ⟨j,y,hy,hxy⟩ := mem_iUnion.mp hx
  exact ⟨y,hy,(D (n+1)).mono hb (hmono ((P.spare i).bounded_sites j hxy))⟩

private theorem divides_of_growSite_subset {n r : ℕ} (P : Batch D d n)
    (i : Fin (d (n+1)+1)) {U A : Set X} {x : X}
    (hmono : ∀ ⦃r x y⦄, (D n).near r x y → (D (n+1)).near r x y)
    (hb : (P.spare i).bound ≤ r)
    (hA : A ⊆ (D (n+1)).ball x r)
    (h : Divides (growSite P i U) A) :
    Divides U ((D (n+1)).ball x (2*r)) := by
  obtain ⟨⟨y,hy,hyU⟩,⟨z,hz,hzU⟩⟩ := h
  obtain ⟨w,hw,hyw⟩ := growSite_subset_thicken P i U hmono hb hyU
  have hsum : r+r = 2*r := by omega
  exact ⟨⟨w,hsum ▸ (D (n+1)).triangle (hA hy) hyw,hw⟩,
    ⟨z,(D (n+1)).mono (by omega) (hA hz),fun hz' => hzU (subset_growSite P i U hz')⟩⟩

private theorem divides_previous_of_growSite {n : ℕ} (P : Batch D d n)
    (i : Fin (d (n+1)+1)) {U A : Set X} {x : X}
    (hA : A ⊆ (D n).ball x P.radius) (h : Divides (growSite P i U) A) :
    (P.spare i).splits A := by
  obtain ⟨⟨y,hy,hyU⟩,⟨z,hz,hzU⟩⟩ := h
  obtain ⟨j,u,hu,hyu⟩ := mem_iUnion.mp hyU
  refine ⟨j,⟨y,hy,(D n).comp_start hyu⟩,⟨z,hz,?_⟩⟩
  intro hzj
  have hyz : (D n).near (2*P.radius) z y := by
    exact (D n).mono (by omega) ((D n).triangle ((D n).symm _ (hA hz)) (hA hy))
  have hzy := (D n).comp_single hzj ((D n).comp_start hyu) hyz
  exact hzU (mem_iUnion.mpr ⟨j,u,hu,(D n).comp_trans hzy hyu⟩)

private theorem grow_cover {n r : ℕ} (P : Batch D d n)
    (hmono : ∀ ⦃a x y⦄, (D n).near a x y → (D (n+1)).near a x y)
    (hr : ∀ i, (P.spare i).bound ≤ r)
    (C : ScaleCover (D (n+1)) (d (n+1)) (4*r)) :
    ∃ C' : ScaleCover (D (n+1)) (d (n+1)) (2*r),
      ∀ i, C'.sites i = growSite P i (C.sites i) := by
  refine ⟨{
    sites := fun i => growSite P i (C.sites i)
    measurable_sites := fun i => measurableSet_growSite P i (C.measurable_sites i)
    covers := fun x => by
      obtain ⟨i,hi⟩ := C.covers x
      exact ⟨i,subset_growSite P i _ hi⟩
    bound := r+C.bound+r
    bounded_sites := fun i => by
      apply (D (n+1)).mixed_bound_of_thicken (growSite_subset_thicken P i _ hmono (hr i))
      apply (D (n+1)).boundComp_mono Subset.rfl _ le_rfl (C.bounded_sites i)
      omega
  },fun i => rfl⟩

noncomputable def Batch.allCount {n : ℕ} (P : Batch D d n) (A : Set X) : ℕ :=
  countTrue (fun j => (P.covers j).splits A)

noncomputable def Batch.spareCount {n : ℕ} (P : Batch D d n) (A : Set X) : ℕ :=
  countTrue (fun j => (P.spare j).splits A)

theorem Batch.allCount_eq {n : ℕ} (P : Batch D d n) (A : Set X) : by
    classical exact P.allCount A = (if P.main.splits A then 1 else 0) + P.spareCount A := by
  classical
  exact countTrue_fin_succ _

theorem initial_batch (hd : BorelAsdimLE (D 0) (d 0) univ) :
    ∃ P : Batch D d 0, ∀ x, P.allCount ((D 0).ball x P.radius) ≤ d 0+1 := by
  let r := 0
  obtain ⟨C,hC⟩ := (D 0).exists_orthogonal_covers hd r (2*r)
  let P : Batch D d 0 := ⟨r,le_rfl,fun j => C j.val⟩
  refine ⟨P,fun x => ?_⟩
  rw [← Fintype.card_fin (d 0+1),← countTrue_true]
  apply countTrue_le_of_pick (W := fun (j : Fin (d (0+1)+2)) (i : Fin (d 0+1)) =>
    Divides ((C j.val).sites i) ((D 0).ball x r))
  · rintro j ⟨i,hi⟩
    exact ⟨i,trivial,hi⟩
  · intro j k i hj hk
    apply Fin.ext
    rcases lt_trichotomy j.val k.val with hl|he|hg
    · exact (hC hl i x hj hk).elim
    · exact he
    · exact (hC hg i x hk hj).elim

theorem next_batch {n : ℕ} (P : Batch D d n)
    (hd : BorelAsdimLE (D (n+1)) (d (n+1)) univ)
    (hmono : ∀ ⦃r x y⦄, (D n).near r x y → (D (n+1)).near r x y) :
    ∃ Q : Batch D d (n+1), P.radius ≤ Q.radius ∧
      (∀ x, Q.allCount ((D (n+1)).ball x Q.radius) ≤ d (n+1)+1) ∧
      (∀ (x : X) (A : Set X), A ⊆ (D n).ball x P.radius →
        Q.allCount A ≤ P.spareCount A) := by
  classical
  let r := max (n+1) (max P.radius (Finset.univ.sup fun i => (P.spare i).bound))
  have hp : P.radius ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hr : ∀ i, (P.spare i).bound ≤ r := by
    intro i
    exact (Finset.le_sup (f := fun j => (P.spare j).bound) (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨C,hC⟩ := (D (n+1)).exists_orthogonal_covers hd (2*r) (4*r)
  choose B hB using fun j : Fin (d (n+2)+2) => grow_cover P hmono hr (C j.val)
  let Q : Batch D d (n+1) := ⟨r,le_max_left _ _,B⟩
  have hpick (x : X) {A : Set X} (ha : A ⊆ (D (n+1)).ball x r)
      (j : Fin (d (n+2)+2)) (hj : (Q.covers j).splits A) :
      ∃ i, Divides (growSite P i ((C j.val).sites i)) A ∧
        Divides ((C j.val).sites i) ((D (n+1)).ball x (2*r)) := by
    obtain ⟨i,hi⟩ := hj
    change Divides ((B j).sites i) A at hi
    rw [hB] at hi
    exact ⟨i,hi,divides_of_growSite_subset P i hmono (hr i) ha hi⟩
  have hsep (x : X) (j k : Fin (d (n+2)+2)) (i : Fin (d (n+1)+1))
      (hj : Divides ((C j.val).sites i) ((D (n+1)).ball x (2*r)))
      (hk : Divides ((C k.val).sites i) ((D (n+1)).ball x (2*r))) : j=k := by
    apply Fin.ext
    rcases lt_trichotomy j.val k.val with hl|he|hg
    · exact (hC hl i x hj hk).elim
    · exact he
    · exact (hC hg i x hk hj).elim
  refine ⟨Q,hp,?_,?_⟩
  · intro x
    rw [← Fintype.card_fin (d (n+1)+1),← countTrue_true]
    apply countTrue_le_of_pick (W := fun (j : Fin (d (n+2)+2)) i =>
      Divides ((C j.val).sites i) ((D (n+1)).ball x (2*r)))
    · intro j hj
      obtain ⟨i,_,h⟩ := hpick x Subset.rfl j hj
      exact ⟨i,trivial,h⟩
    · exact hsep x
  · intro x A ha
    have ha' : A ⊆ (D (n+1)).ball x r := fun _ hz =>
      (D (n+1)).mono hp (hmono (ha hz))
    apply countTrue_le_of_pick (W := fun (j : Fin (d (n+2)+2)) i =>
      Divides ((C j.val).sites i) ((D (n+1)).ball x (2*r)))
    · intro j hj
      obtain ⟨i,hi,hib⟩ := hpick x ha' j hj
      exact ⟨i,divides_previous_of_growSite P i ha hi,hib⟩
    · exact hsep x

end MetricCarry
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.CarryCovers

-- BEGIN COMPLETE MODULE HirschProof.CostWalk
section
                       
                                        
                                                   
                                           

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set
open scoped Pointwise

/-- A path with its exact total integer cost. -/
inductive CostWalk {X : Type*} (step : ℕ → X → X → Prop) : X → X → ℕ → Prop
  | nil (x : X) : CostWalk step x x 0
  | cons {x y z : X} {a b : ℕ} :
      step a x y → CostWalk step y z b → CostWalk step x z (a+b)

namespace CostWalk
variable {X : Type*} {S T : ℕ → X → X → Prop}

theorem append {x y z : X} {a b : ℕ} (h : CostWalk S x y a) (k : CostWalk S y z b) :
    CostWalk S x z (a+b) := by
  induction h with
  | nil => simpa using k
  | cons e _ ih => rw [Nat.add_assoc]; exact .cons e (ih k)

theorem single {x y : X} {a : ℕ} (h : S a x y) : CostWalk S x y a := by
  simpa using (CostWalk.cons h (.nil y))

theorem reverse (hs : ∀ a x y, S a x y → S a y x)
    {x y : X} {a : ℕ} (h : CostWalk S x y a) : CostWalk S y x a := by
  induction h with
  | nil => exact .nil _
  | @cons x y z a b e h ih =>
    rw [Nat.add_comm]
    exact ih.append (single (hs a x y e))

theorem mono (hm : ∀ a x y, S a x y → T a x y)
    {x y : X} {a : ℕ} (h : CostWalk S x y a) : CostWalk T x y a := by
  induction h with
  | nil => exact .nil _
  | cons e _ ih => exact .cons (hm _ _ _ e) ih

theorem zero_eq (pos : ∀ {a x y}, S a x y → 0 < a)
    {x y : X} {a : ℕ} (h : CostWalk S x y a) (ha : a = 0) : x = y := by
  cases h with
  | nil => rfl
  | cons e _ => have := pos e; omega

section Measurable
variable [MeasurableSpace X] [MeasurableEq X]
variable (M : ℕ → X → X)

private def eval : List (ℕ × ℕ) → X → X
  | [], x => x
  | (_,i)::w, x => eval w (M i x)

private def valid (S : ℕ → X → X → Prop) : List (ℕ × ℕ) → X → Prop
  | [], _ => True
  | (a,i)::w, x => S a x (M i x) ∧ valid S w (M i x)

private def total : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (a,_)::w => a + total w

private theorem measurable_eval (hM : ∀ i, Measurable (M i))
    (w : List (ℕ × ℕ)) : Measurable (eval M w) := by
  induction w with
  | nil => exact measurable_id
  | cons ai w ih => exact ih.comp (hM ai.2)

private theorem measurableSet_valid (hM : ∀ i, Measurable (M i))
    (hS : ∀ a, MeasurableSet {p : X×X | S a p.1 p.2})
    (w : List (ℕ × ℕ)) : MeasurableSet {x | valid M S w x} := by
  induction w with
  | nil =>
    change MeasurableSet {x : X | True}
    simp
  | cons ai w ih =>
    exact ((hS ai.1).preimage (measurable_id.prodMk (hM ai.2))).inter
      (ih.preimage (hM ai.2))

private theorem costWalk_of_valid {w : List (ℕ × ℕ)} {x : X} (h : valid M S w x) :
    CostWalk S x (eval M w x) (total w) := by
  induction w generalizing x with
  | nil => exact .nil _
  | cons ai w ih => exact .cons h.1 (ih h.2)

private theorem exists_valid (hmove : ∀ {a x y}, S a x y → ∃ i, M i x = y)
    {a : ℕ} {x y : X} (h : CostWalk S x y a) :
    ∃ w, valid M S w x ∧ eval M w x = y ∧ total w = a := by
  induction h with
  | nil => exact ⟨[],trivial,rfl,rfl⟩
  | @cons x y z a b e h ih =>
    obtain ⟨i,hi⟩ := hmove e
    obtain ⟨w,hw,hw1,hw2⟩ := ih
    refine ⟨(a,i) :: w,?_,?_,?_⟩
    · change S a x (M i x) ∧ valid M S w (M i x)
      rw [hi]; exact ⟨e,hw⟩
    · change eval M w (M i x) = z
      rwa [hi]
    · simpa only [total,hw2]

theorem measurableSet_le (hM : ∀ i, Measurable (M i))
    (hS : ∀ a, MeasurableSet {p : X×X | S a p.1 p.2})
    (hmove : ∀ {a x y}, S a x y → ∃ i, M i x = y) (r : ℕ) :
    MeasurableSet {p : X×X | ∃ a ≤ r, CostWalk S p.1 p.2 a} := by
  have heq : {p : X×X | ∃ a ≤ r, CostWalk S p.1 p.2 a} =
      ⋃ w : List (ℕ × ℕ), {p : X×X | total w ≤ r ∧
        (valid M S w p.1 ∧ eval M w p.1 = p.2)} := by
    ext p
    simp only [mem_setOf_eq,mem_iUnion]
    constructor
    · rintro ⟨a,ha,hp⟩
      obtain ⟨w,hw,he,ht⟩ := exists_valid M hmove hp
      exact ⟨w,ht.symm ▸ ha,hw,he⟩
    · rintro ⟨w,ha,hw,he⟩
      exact ⟨total w,ha,he ▸ costWalk_of_valid M hw⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro w
  by_cases h : total w ≤ r
  · have hset : {p : X×X | total w ≤ r ∧
        (valid M S w p.1 ∧ eval M w p.1 = p.2)} =
        {p : X×X | valid M S w p.1 ∧ eval M w p.1 = p.2} := by ext p; simp [h]
    rw [hset]
    exact ((measurableSet_valid M hM hS w).preimage measurable_fst).inter
      (measurableSet_eq_fun ((measurable_eval M hM w).comp measurable_fst) measurable_snd)
  · simp [h]

end Measurable

end CostWalk

section Group

variable {G X : Type*} [Group G] [MulAction G X]

/-- All displacements of words of length at most the specified integer. -/
noncomputable def wordBall (A : Finset G) : ℕ → Finset G
  | 0 => {1}
  | k+1 => by classical exact wordBall A k ∪ wordBall A k * A

theorem one_mem_wordBall (A : Finset G) (r : ℕ) : (1 : G) ∈ wordBall A r := by
  classical
  induction r with
  | zero => simp [wordBall]
  | succ n ih => exact Finset.mem_union_left _ ih

theorem wordBall_mono (A : Finset G) : Monotone (wordBall A) := by
  classical
  apply monotone_nat_of_le_succ
  intro n g hg
  exact Finset.mem_union_left _ hg

theorem wordBall_append_mem (A : Finset G) {r : ℕ} {h g : G}
    (hh : h ∈ wordBall A r) (hg : g ∈ A) : h*g ∈ wordBall A (r+1) := by
  classical
  exact Finset.mem_union_right _ (Finset.mul_mem_mul hh hg)

theorem CostWalk.exists_wordBall {S : ℕ → X → X → Prop} (A : Finset G)
    (hstep : ∀ {a x y}, S a x y → 0 < a ∧ ∃ g ∈ A, g • x = y)
    {x y : X} {a : ℕ} (p : CostWalk S x y a) :
    ∃ g ∈ wordBall A a, g • x = y := by
  induction p with
  | nil => exact ⟨1,one_mem_wordBall A 0,one_smul _ _⟩
  | @cons x y z a b h _ ih =>
    obtain ⟨ha,g,hg,hxy⟩ := hstep h
    obtain ⟨h,hh,hyz⟩ := ih
    exact ⟨h*g,wordBall_mono A (by omega) (wordBall_append_mem A hh hg),
      by rw [mul_smul,hxy,hyz]⟩

variable [MeasurableSpace X] [MeasurableEq X] [Countable G]

/-- Positive, Borel generator costs induce a proper extended orbit metric. -/
noncomputable def actionPathNear (A : Finset G) (S : ℕ → X → X → Prop)
    (hact : ∀ g : G, Measurable (fun x : X => g • x))
    (hstep : ∀ {a x y}, S a x y → 0 < a ∧ ∃ g ∈ A, g • x = y)
    (hsymm : ∀ a x y, S a x y → S a y x)
    (hborel : ∀ a, MeasurableSet {p : X×X | S a p.1 p.2}) : BorelNear X := by
  classical
  let g := Classical.choose (exists_surjective_nat G)
  have hg : Function.Surjective g := Classical.choose_spec (exists_surjective_nat G)
  let M : ℕ → X → X := fun i x => g i • x
  have hM (i : ℕ) : Measurable (M i) := hact (g i)
  have hmove {a : ℕ} {x y : X} (h : S a x y) : ∃ i, M i x = y := by
    obtain ⟨_,v,_,hv⟩ := hstep h
    obtain ⟨i,rfl⟩ := hg v
    exact ⟨i,hv⟩
  exact {
    near := fun r x y => ∃ a ≤ r, CostWalk S x y a
    refl := fun r x => ⟨0,Nat.zero_le r,.nil x⟩
    symm := by
      rintro r x y ⟨a,ha,h⟩
      exact ⟨a,ha,h.reverse hsymm⟩
    mono := by
      rintro r s hrs x y ⟨a,ha,h⟩
      exact ⟨a,ha.trans hrs,h⟩
    triangle := fun ⟨a,ha,h⟩ ⟨b,hb,k⟩ => ⟨a+b,Nat.add_le_add ha hb,h.append k⟩
    zero := fun ⟨a,ha,h⟩ => h.zero_eq (fun e => (hstep e).1) (Nat.eq_zero_of_le_zero ha)
    borel := CostWalk.measurableSet_le M hM hborel hmove
    moves := M
    measurable_moves := hM
    moves_cover := by
      rintro r x y ⟨a,ha,h⟩
      obtain ⟨v,_,hv⟩ := h.exists_wordBall A hstep
      obtain ⟨i,rfl⟩ := hg v
      exact ⟨i,hv⟩
    uniformly_finite := by
      intro r
      refine ⟨(wordBall A r).card,fun x => ⟨(wordBall A r).image (fun g => g • x),
        Finset.card_image_le,?_⟩⟩
      rintro y ⟨a,ha,h⟩
      obtain ⟨v,hv,rfl⟩ := h.exists_wordBall A hstep
      exact Finset.mem_image_of_mem _ (wordBall_mono A ha hv) }

end Group
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.CostWalk

-- BEGIN COMPLETE MODULE HirschProof.WeightedStages
section
                           
                               

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set
open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

def SymmetricMoves (A : Finset G) : Prop := ∀ ⦃g : G⦄, g ∈ A → g⁻¹ ∈ A

def unitStep (A : Finset G) (a : ℕ) (x y : X) : Prop :=
  a = 1 ∧ ∃ g ∈ A, g • x = y

theorem measurableSet_unitStep [MeasurableSpace X] [MeasurableEq X] [Countable G]
    (A : Finset G) (hact : ∀ g : G, Measurable (fun x : X => g • x)) (a : ℕ) :
    MeasurableSet {p : X×X | unitStep A a p.1 p.2} := by
  have heq : {p : X×X | unitStep A a p.1 p.2} =
      ⋃ g : ↑A, {p : X×X | a = 1 ∧ g.val • p.1 = p.2} := by
    ext p
    simp only [mem_setOf_eq,mem_iUnion,unitStep]
    constructor
    · rintro ⟨ha,g,hg,hgp⟩
      exact ⟨⟨g,hg⟩,ha,hgp⟩
    · rintro ⟨g,ha,hg⟩
      exact ⟨ha,g.val,g.property,hg⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro g
  by_cases ha : a = 1
  · simpa [ha] using measurableSet_eq_fun ((hact g.val).comp measurable_fst)
      (measurable_snd : Measurable (Prod.snd : X×X → X))
  · simp [ha]

variable [MeasurableSpace X] [MeasurableEq X] [Countable G]

/-- Ordinary word orbit metric for a finite symmetric set of generators. -/
noncomputable def wordNear (A : Finset G) (hA : SymmetricMoves A)
    (hact : ∀ g : G, Measurable (fun x : X => g • x)) : BorelNear X :=
  actionPathNear A (unitStep A) hact
    (fun ⟨e,h⟩ => ⟨by omega,h⟩)
    (by
      rintro a x y ⟨ha,g,hg,rfl⟩
      exact ⟨ha,g⁻¹,hA hg,inv_smul_smul g x⟩)
    (measurableSet_unitStep A hact)

theorem wordNear_iff_costWalk (A : Finset G) (hA : SymmetricMoves A)
    (hact : ∀ g : G, Measurable (fun x : X => g • x)) (r : ℕ) (x y : X) :
    (wordNear A hA hact).near r x y ↔ ∃ a ≤ r, CostWalk (unitStep A) x y a := Iff.rfl

theorem wordNear_generator (A : Finset G) (hA : SymmetricMoves A)
    (hact : ∀ g : G, Measurable (fun x : X => g • x)) {g : G} (hg : g ∈ A) (x : X) :
    (wordNear A hA hact).near 1 x (g • x) :=
  ⟨1,le_rfl,CostWalk.single ⟨rfl,g,hg,rfl⟩⟩

/-- All edges from stages below n, retaining their original costs.
Any admissible core membership can witness a cost. Taking the least cost
recovers the weighted path metric of the manuscript. -/
def stageStep (S : ℕ → Finset G) (K : ℕ → ℕ → Set X) (n a : ℕ) (x y : X) : Prop :=
  ∃ i < n, ∃ g ∈ S i, ∃ j : ℕ, a = j+1 ∧ g • x = y ∧ x ∈ K i j ∧ y ∈ K i j

theorem stageStep_mono {S : ℕ → Finset G} {K : ℕ → ℕ → Set X} {m n : ℕ} (hmn : m ≤ n) :
    ∀ a x y, stageStep S K m a x y → stageStep S K n a x y := by
  rintro a x y ⟨i,hi,g,hg,j,hj,hxy,hx,hy⟩
  exact ⟨i,hi.trans_le hmn,g,hg,j,hj,hxy,hx,hy⟩

theorem measurableSet_stageStep (S : ℕ → Finset G) (K : ℕ → ℕ → Set X)
    (hK : ∀ i j, MeasurableSet (K i j))
    (hact : ∀ g : G, Measurable (fun x : X => g • x)) (n a : ℕ) :
    MeasurableSet {p : X×X | stageStep S K n a p.1 p.2} := by
  have hset : {p : X×X | stageStep S K n a p.1 p.2} =
      ⋃ i : ℕ, ⋃ g : ↑(S i), ⋃ j : ℕ,
        {p : X×X | (i < n ∧ a = j+1) ∧
          (g.val • p.1 = p.2 ∧ p.1 ∈ K i j ∧ p.2 ∈ K i j)} := by
    ext p
    simp only [mem_iUnion,mem_setOf_eq,stageStep]
    constructor
    · rintro ⟨i,hi,g,hg,j,ha,he,hx,hy⟩
      exact ⟨i,⟨g,hg⟩,j,⟨hi,ha⟩,he,hx,hy⟩
    · rintro ⟨i,g,j,⟨hi,ha⟩,he,hx,hy⟩
      exact ⟨i,hi,g.val,g.property,j,ha,he,hx,hy⟩
  rw [hset]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun g =>
    MeasurableSet.iUnion fun j => ?_
  by_cases h : i < n ∧ a = j+1
  · simpa only [h,true_and] using
      (measurableSet_eq_fun ((hact g.val).comp measurable_fst) measurable_snd).inter
        (((hK i j).preimage measurable_fst).inter ((hK i j).preimage measurable_snd))
  · simp [h]

noncomputable def stageNear (S : ℕ → Finset G) (K : ℕ → ℕ → Set X)
    (hS : Monotone S) (hsymm : ∀ n, SymmetricMoves (S n))
    (hK : ∀ n j, MeasurableSet (K n j))
    (hact : ∀ g : G, Measurable (fun x : X => g • x)) (n : ℕ) : BorelNear X :=
  actionPathNear (S n) (stageStep S K n) hact
    (by
      rintro a x y ⟨i,hi,g,hg,j,rfl,hxy,_,_⟩
      exact ⟨Nat.succ_pos _,g,hS hi.le hg,hxy⟩)
    (by
      rintro a x y ⟨i,hi,g,hg,j,hj,rfl,hx,hy⟩
      exact ⟨i,hi,g⁻¹,hsymm i hg,j,hj,inv_smul_smul g x,hy,hx⟩)
    (measurableSet_stageStep S K hK hact n)

section Stage
variable (S : ℕ → Finset G) (K : ℕ → ℕ → Set X)
variable (hS : Monotone S) (hsymm : ∀ n, SymmetricMoves (S n))
variable (hK : ∀ n j, MeasurableSet (K n j))
variable (hact : ∀ g : G, Measurable (fun x : X => g • x))

local notation "rho" => stageNear S K hS hsymm hK hact
local notation "phys" => fun n => wordNear (S n) (hsymm n) hact

theorem stageNear_iff_costWalk (n r : ℕ) (x y : X) :
    (rho n).near r x y ↔ ∃ a ≤ r, CostWalk (stageStep S K n) x y a := Iff.rfl

theorem stageNear_compatible {m n : ℕ} (hmn : m ≤ n) {r : ℕ} {x y : X}
    (h : (rho m).near r x y) : (rho n).near r x y := by
  obtain ⟨a,ha,p⟩ := h
  exact ⟨a,ha,p.mono (stageStep_mono hmn)⟩

include hS in
theorem stageStep_phys {i n a : ℕ} (hin : i ≤ n) {x y : X}
    (h : stageStep S K (i+1) a x y) : (phys n).near a x y := by
  obtain ⟨k,hk,g,hg,j,rfl,rfl,_,_⟩ := h
  exact (phys n).mono (Nat.succ_le_succ (Nat.zero_le j))
    (wordNear_generator (S n) (hsymm n) hact (hS (by omega) hg) x)

include hS in
theorem costWalk_phys {i n a : ℕ} (hin : i ≤ n) {x y : X}
    (h : CostWalk (stageStep S K (i+1)) x y a) : (phys n).near a x y := by
  induction h with
  | nil => exact (phys n).refl _ _
  | cons e _ ih =>
    exact (phys n).triangle (stageStep_phys S K hS hsymm hact hin e) ih

theorem stageNear_phys {n r : ℕ} {x y : X} (h : (rho (n+1)).near r x y) :
    (phys n).near r x y := by
  obtain ⟨a,ha,p⟩ := h
  exact (phys n).mono ha (costWalk_phys S K hS hsymm hact le_rfl p)

include hS in
/-- A short path outside the new core neighborhood cannot use a new edge. -/
theorem costWalk_old_of_outside {n a r : ℕ} {x y : X}
    (hKm : Monotone (K n)) (p : CostWalk (stageStep S K (n+1)) x y a)
    (ha : a ≤ r) (hx : x ∉ (phys n).thicken (K n r) r) :
    CostWalk (stageStep S K n) x y a := by
  induction p generalizing r with
  | nil => exact .nil _
  | @cons x y z a b he p ih =>
    have heold : stageStep S K n a x y := by
      obtain ⟨i,hi,g,hg,j,hj,hxy,hxj,hyj⟩ := he
      have hne : i ≠ n := by
        intro h
        subst i
        exact hx ⟨x,hKm (by omega) hxj,(phys n).refl _ _⟩
      exact ⟨i,by omega,g,hg,j,hj,hxy,hxj,hyj⟩
    have hy : y ∉ (phys n).thicken (K n (r-a)) (r-a) := by
      rintro ⟨u,hu,hyu⟩
      have hxu := (phys n).triangle (stageStep_phys S K hS hsymm hact le_rfl he) hyu
      exact hx ⟨u,hKm (Nat.sub_le _ _) hu,(phys n).mono (by omega) hxu⟩
    exact .cons heold (ih (by omega) hy)

theorem stageNear_old_of_outside {n r : ℕ} {x y : X}
    (hKm : Monotone (K n)) (h : (rho (n+1)).near r x y)
    (hx : x ∉ (phys n).thicken (K n r) r) : (rho n).near r x y := by
  obtain ⟨a,ha,p⟩ := h
  exact ⟨a,ha,costWalk_old_of_outside S K hS hsymm hact hKm p ha hx⟩

theorem stageNear_zero (r : ℕ) {x y : X} (h : (rho 0).near r x y) : x = y := by
  obtain ⟨a,_,p⟩ := h
  cases p with
  | nil => rfl
  | cons he _ =>
    obtain ⟨i,hi,_⟩ := he
    exact (Nat.not_lt_zero i hi).elim

end Stage

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.WeightedStages

-- BEGIN COMPLETE MODULE HirschProof.WeightedExhaustions
section
                                 
                                   

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

section Group
variable {G X : Type*} [Group G] [MulAction G X] [Countable G]
variable [MeasurableSpace X] [MeasurableEq X]
variable (S : ℕ → Finset G) (K : ℕ → ℕ → Set X)
variable (hS : Monotone S) (hsymm : ∀ n, SymmetricMoves (S n))
variable (hK : ∀ n j, MeasurableSet (K n j))
variable (hact : ∀ g : G, Measurable (fun x : X => g • x))

local notation "rho" => stageNear S K hS hsymm hK hact
local notation "phys" => fun n => wordNear (S n) (hsymm n) hact

theorem stageNear_asdim_zero : BorelAsdimLE (rho 0) 0 univ := by
  intro r
  refine ⟨fun _ => univ,0,fun _ => Subset.rfl,fun _ => MeasurableSet.univ,
    fun _ _ => ⟨0,mem_univ _⟩,?_⟩
  intro i x y hxy
  obtain ⟨s,h⟩ := (rho 0).exists_near_of_comp hxy
  have he := stageNear_zero S K hS hsymm hK hact s h
  subst y
  exact (rho 0).refl 0 x

theorem stageNear_asdim_succ {b d n : ℕ} (hKm : Monotone (K n))
    (hprev : BorelAsdimLE (rho n) b univ)
    (hcore : ∀ j, BorelAsdimLE (phys n) d (K n j)) :
    BorelAsdimLE (rho (n+1)) (d+b+1) univ := by
  classical
  intro r
  let V := (phys n).thicken (K n r) r
  have hV : MeasurableSet V := (phys n).measurableSet_thicken (hK n r) r
  obtain ⟨L,RL,hL,hLm,hLcov,hLB⟩ := (phys n).asdim_thicken (hcore r) r
  obtain ⟨R,RR,_,hRm,hRcov,hRB⟩ := hprev r
  have hR' (i : Fin (b+1)) :
      (rho (n+1)).boundComp (R i ∩ Vᶜ) r RR := by
    intro x y h
    have hold := (rho (n+1)).comp_mono_near (rho n) (by
      intro x' y' hx' hy' hxy'
      exact stageNear_old_of_outside S K hS hsymm hK hact hKm hxy' hx'.2) h
    exact stageNear_compatible S K hS hsymm hK hact (Nat.le_succ n)
      (hRB i ((rho n).comp_mono inter_subset_left le_rfl hold))
  obtain ⟨N,hN⟩ := (phys n).uniformly_finite RL
  have hL' (i : Fin (d+1)) : (rho (n+1)).boundComp (L i) r (r*N) := by
    apply (rho (n+1)).boundComp_of_small
    intro x
    obtain ⟨t,ht,htx⟩ := hN x
    refine ⟨t,ht,fun y hxy => htx y (hLB i ?_)⟩
    exact (rho (n+1)).comp_mono_near (phys n)
      (by intro x' y' _ _ h; exact stageNear_phys S K hS hsymm hK hact h) hxy
  let U : Fin ((d+1)+(b+1)) → Set X :=
    Fin.addCases L (fun i => R i ∩ Vᶜ)
  have hcard : d + b + 1 + 1 = (d+1)+(b+1) := by omega
  refine ⟨fun i => U (Fin.cast hcard i),max (r*N) RR,fun _ => subset_univ _,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (motive := fun t => MeasurableSet (U t)) ?_ ?_ (Fin.cast hcard i)
    · intro j; simpa [U] using hLm j
    · intro j; simpa [U] using (hRm j).inter hV.compl
  · intro x _
    by_cases hx : x ∈ V
    · obtain ⟨i,hi⟩ := hLcov x hx
      refine ⟨Fin.cast hcard.symm (Fin.castAdd (b+1) i),?_⟩
      simpa [U] using hi
    · obtain ⟨i,hi⟩ := hRcov x (mem_univ x)
      refine ⟨Fin.cast hcard.symm (Fin.natAdd (d+1) i),?_⟩
      simpa [U] using (show x ∈ R i ∩ Vᶜ from ⟨hi,hx⟩)
  · intro i
    refine Fin.addCases (motive := fun t => (rho (n+1)).boundComp (U t) r (max (r*N) RR))
      ?_ ?_ (Fin.cast hcard i)
    · intro j
      simpa [U] using (rho (n+1)).boundComp_mono Subset.rfl le_rfl (le_max_left _ _) (hL' j)
    · intro j
      simpa [U] using (rho (n+1)).boundComp_mono Subset.rfl le_rfl (le_max_right _ _) (hR' j)

theorem stageNear_fixed_orbit_rel (hSall : ∀ g : G, ∃ n, g ∈ S n)
    (hKm : ∀ n, Monotone (K n)) (hcover : ∀ n x, ∃ j, x ∈ K n j) (x y : X) :
    (∃ n r, (rho n).near r x y) ↔ ∃ g : G, g • x = y := by
  constructor
  · rintro ⟨n,r,a,ha,p⟩
    obtain ⟨g,_,hg⟩ := p.exists_wordBall (S n) (by
      rintro a x y ⟨i,hi,g,hg,j,rfl,hxy,_,_⟩
      exact ⟨Nat.succ_pos _,g,hS hi.le hg,hxy⟩)
    exact ⟨g,hg⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨n,hn⟩ := hSall g
    obtain ⟨jx,hx⟩ := hcover n x
    obtain ⟨jy,hy⟩ := hcover n (g • x)
    let j := max jx jy
    refine ⟨n+1,j+1,j+1,le_rfl,CostWalk.single ?_⟩
    exact ⟨n,Nat.lt_succ_self _,g,hn,j,rfl,rfl,
      hKm n (le_max_left _ _) hx,hKm n (le_max_right _ _) hy⟩

end Group

theorem exists_symmetric_exhaustion (G : Type*) [Group G] [Countable G] :
    ∃ S : ℕ → Finset G, Monotone S ∧ (∀ n, SymmetricMoves (S n)) ∧
      ∀ g : G, ∃ n, g ∈ S n := by
  classical
  obtain ⟨g,hg⟩ := exists_surjective_nat G
  let A (n : ℕ) := (Finset.range n).image g
  let S (n : ℕ) := A n ∪ (A n).image Inv.inv
  have hA : Monotone A := by
    intro a b hab
    exact Finset.image_subset_image (Finset.range_mono hab)
  refine ⟨S,?_,?_,?_⟩
  · intro a b hab
    exact Finset.union_subset_union (hA hab) (Finset.image_subset_image (hA hab))
  · intro n v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv)
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_union_left _ (by simpa using ht)
  · intro v
    obtain ⟨n,rfl⟩ := hg v
    exact ⟨n+1,Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr
      (Nat.lt_succ_self n)))⟩

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.WeightedExhaustions

-- BEGIN COMPLETE MODULE HirschProof.CompatibleUnion
section
                                          
                              
                                      

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

variable {X : Type*} [MeasurableSpace X]

namespace ScaleCover
variable {D : BorelNear X} {d r : ℕ} (C : ScaleCover D d r)

/-- Membership in each cover set and its component determines a finite class. -/
def relation (x y : X) : Prop :=
  ∀ i, (x ∉ C.sites i ∧ y ∉ C.sites i) ∨ D.comp r (C.sites i) x y

theorem equivalence_relation : Equivalence C.relation := by
  refine ⟨?_,?_,?_⟩
  · intro x i
    by_cases h : x ∈ C.sites i
    · exact Or.inr (D.comp_refl h)
    · exact Or.inl ⟨h,h⟩
  · intro x y h i
    rcases h i with h'|h'
    · exact Or.inl ⟨h'.2,h'.1⟩
    · exact Or.inr (D.comp_symm h')
  · intro x y z h h' i
    rcases h i with hxy|hxy <;> rcases h' i with hyz|hyz
    · exact Or.inl ⟨hxy.1,hyz.2⟩
    · exact (hxy.2 (D.comp_start hyz)).elim
    · exact (hyz.1 (D.comp_end hxy)).elim
    · exact Or.inr (D.comp_trans hxy hyz)

theorem measurableSet_relation [MeasurableEq X] :
    MeasurableSet {p : X×X | C.relation p.1 p.2} := by
  change MeasurableSet {p : X×X | ∀ i, (p.1 ∉ C.sites i ∧ p.2 ∉ C.sites i) ∨
    D.comp r (C.sites i) p.1 p.2}
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun i =>
    (((C.measurable_sites i).compl.preimage measurable_fst).inter
      ((C.measurable_sites i).compl.preimage measurable_snd)).union
      (D.measurableSet_comp (C.measurable_sites i) r)

theorem near_of_relation {x y : X} (h : C.relation x y) :
    D.near C.bound x y := by
  obtain ⟨i,hi⟩ := C.covers x
  exact C.bounded_sites i ((h i).resolve_left fun h' => h'.1 hi)

theorem finite_class (x : X) : {y | C.relation x y}.Finite :=
  (D.ball_finite C.bound x).subset fun _ h => C.near_of_relation h

theorem relation_of_no_split {A : Set X} (hA : ¬ C.splits A) {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : D.near r x y) : C.relation x y := by
  intro i
  by_cases hxi : x ∈ C.sites i <;> by_cases hyi : y ∈ C.sites i
  · exact Or.inr (D.comp_single hxi hyi hxy)
  · exact (hA ⟨i,⟨x,hx,hxi⟩,⟨y,hy,hyi⟩⟩).elim
  · exact (hA ⟨i,⟨y,hy,hyi⟩,⟨x,hx,hxi⟩⟩).elim
  · exact Or.inl ⟨hxi,hyi⟩

end ScaleCover

private noncomputable def countPrefix (P : ℕ → Prop) (n : ℕ) : ℕ := by
  classical exact ((Finset.range n).filter P).card

private theorem countPrefix_zeroBelow {P : ℕ → Prop} {k : ℕ}
    (h : ∀ m < k, ¬ P m) : countPrefix P k = 0 := by
  classical
  rw [countPrefix,Finset.card_filter_eq_zero_iff]
  intro m hm
  exact h m (Finset.mem_range.mp hm)

private theorem countPrefix_succ (P : ℕ → Prop) (n : ℕ) : by
    classical exact countPrefix P (n+1) = (if P n then 1 else 0) + countPrefix P n := by
  classical
  rw [countPrefix,countPrefix,Finset.range_add_one,Finset.filter_insert]
  split_ifs with h
  · have hn : n ∉ (Finset.range n).filter P := by simp
    rw [Finset.card_insert_of_notMem hn,Nat.add_comm]
  · exact (Nat.zero_add _).symm

private theorem countPrefix_mono (P : ℕ → Prop) : Monotone (countPrefix P) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  rw [countPrefix_succ]
  exact Nat.le_add_left _ _

private theorem exists_attained_upper (u : ℕ → ℕ) (b : ℕ)
    (h : ∀ n, u n ≤ b) : ∃ n, ∀ m, u m ≤ u n := by
  induction b with
  | zero =>
    exact ⟨0,fun m => (h m).trans (Nat.zero_le _)⟩
  | succ b ih =>
    by_cases he : ∃ n, u n = b+1
    · obtain ⟨n,hn⟩ := he
      exact ⟨n,fun m => hn.symm ▸ h m⟩
    · apply ih
      intro n
      have hn := h n
      have hne : u n ≠ b+1 := fun heq => he ⟨n,heq⟩
      omega

private theorem eventually_no_split {P : ℕ → Prop} {b : ℕ}
    (h : ∀ n, countPrefix P n ≤ b) : ∃ n, ∀ m ≥ n, ¬ P m := by
  classical
  obtain ⟨n,hn⟩ := exists_attained_upper (countPrefix P) b h
  refine ⟨n,?_⟩
  intro m hm hPm
  have hu := hn (m+1)
  have hl := countPrefix_mono P hm
  rw [countPrefix_succ,if_pos hPm] at hu
  omega

private theorem isHyperfinite_of_eventual {E : X → X → Prop} (F : ℕ → X → X → Prop)
    (hF : ∀ n, BorelEquivalence (F n) ∧ ∀ x, {y | F n x y}.Finite)
    (hE : ∀ x y, E x y ↔ ∃ n, ∀ m ≥ n, F m x y) : IsHyperfinite E := by
  let G (n : ℕ) (x y : X) := ∀ m ≥ n, F m x y
  have hGm : Monotone G := by
    intro a b hab x y h m hm
    exact h m (hab.trans hm)
  have hG (n : ℕ) : BorelEquivalence (G n) ∧ ∀ x, {y | G n x y}.Finite := by
    refine ⟨⟨⟨fun x m _ => (hF m).1.1.refl x,
      fun h m hm => (hF m).1.1.symm (h m hm),
      fun h h' m hm => (hF m).1.1.trans (h m hm) (h' m hm)⟩,?_⟩,?_⟩
    · have he : {p : X×X | G n p.1 p.2} =
          ⋂ m : {m : ℕ // n ≤ m}, {p : X×X | F m.val p.1 p.2} := by
        ext p
        simp [G]
      rw [he]
      exact MeasurableSet.iInter fun m => (hF m.val).1.2
    · intro x
      exact ((hF n).2 x).subset fun _ h => h n le_rfl
  refine ⟨⟨⟨?_,?_,?_⟩,?_⟩,G,hGm,hG,fun x y => hE x y⟩
  · intro x
    exact (hE x x).mpr ⟨0,(hG 0).1.1.refl x⟩
  · intro x y h
    obtain ⟨n,hn⟩ := (hE x y).mp h
    exact (hE y x).mpr ⟨n,(hG n).1.1.symm (show G n x y from hn)⟩
  · intro x y z hxy hyz
    obtain ⟨m,hm⟩ := (hE x y).mp hxy
    obtain ⟨n,hn⟩ := (hE y z).mp hyz
    exact (hE x z).mpr ⟨max m n,(hG _).1.1.trans (hGm (le_max_left _ _) x y hm)
      (hGm (le_max_right _ _) y z hn)⟩
  · have he : {p : X×X | E p.1 p.2} = ⋃ n, {p : X×X | G n p.1 p.2} := by
      ext p
      exact (hE p.1 p.2).trans (by simp [G])
    rw [he]
    exact MeasurableSet.iUnion fun n => (hG n).1.2

/-- Conley–Jackson–Marks–Seward–Tucker-Drob Theorem 7.3 for decreasing
integer-valued extended metrics, which is the form needed by the paper. -/
theorem hyperfinite_of_decreasing_near [MeasurableEq X]
    (D : ℕ → BorelNear X) (d : ℕ → ℕ)
    (hD : ∀ n, BorelAsdimLE (D n) (d n) univ)
    (hmono : ∀ n ⦃r x y⦄, (D n).near r x y → (D (n+1)).near r x y) :
    IsHyperfinite (fun x y => ∃ n r, (D n).near r x y) := by
  classical
  have hDN {k n r : ℕ} {x y : X} (hkn : k ≤ n) (h : (D k).near r x y) :
      (D n).near r x y := by
    induction hkn with
    | refl => exact h
    | step _ ih => exact hmono _ ih
  obtain ⟨P0,hP0⟩ := MetricCarry.initial_batch (D := D) (d := d) (hD 0)
  let H (n : ℕ) (P : MetricCarry.Batch D d n) :=
    MetricCarry.next_batch P (hD (n+1)) (hmono n)
  let B : (n : ℕ) → MetricCarry.Batch D d n :=
    fun n => Nat.rec P0 (fun j Q => Classical.choose (H j Q)) n
  have hBs (n : ℕ) := Classical.choose_spec (H n (B n))
  have hR : Monotone (fun n => (B n).radius) := monotone_nat_of_le_succ fun n => (hBs n).1
  have hfresh (n : ℕ) (x : X) : (B n).allCount ((D n).ball x (B n).radius) ≤ d n+1 := by
    cases n with
    | zero => exact hP0 x
    | succ n => exact (hBs n).2.1 x
  have hcarry (k n : ℕ) (hn : k ≤ n) (x : X) :
      (B (n+1)).allCount ((D k).ball x (B k).radius) ≤
        (B n).spareCount ((D k).ball x (B k).radius) := by
    apply (hBs n).2.2 x _
    intro z hz
    exact (D n).mono (hR hn) (hDN hn hz)
  have havoid (k : ℕ) (x : X) :
      ∃ N, ∀ n ≥ N, k ≤ n → ¬ (B n).main.splits ((D k).ball x (B k).radius) := by
    let A := (D k).ball x (B k).radius
    let p (n : ℕ) := k ≤ n ∧ (B n).main.splits A
    have hbudget (n : ℕ) (hn : k ≤ n) :
        countPrefix p (n+1) + (B n).spareCount A ≤ d k+1 := by
      induction hn with
      | refl =>
        have hz : countPrefix p k = 0 :=
          countPrefix_zeroBelow (fun _ hm hp => (Nat.not_le_of_lt hm) hp.1)
        have h := hfresh k x
        change (B k).allCount A ≤ d k+1 at h
        rw [(B k).allCount_eq] at h
        rw [countPrefix_succ,hz,add_zero]
        simpa only [p,le_refl,true_and] using h
      | @step n hn ih =>
        have h := hcarry k n hn x
        change (B (n+1)).allCount A ≤ (B n).spareCount A at h
        rw [(B (n+1)).allCount_eq] at h
        have hkn : k ≤ n+1 := Nat.le_succ_of_le hn
        rw [countPrefix_succ p (n+1)]
        change _ + _ + (B (n+1)).spareCount A ≤ _
        by_cases hM : (B (n+1)).main.splits A
        · have hp : p (n+1) := ⟨hkn,hM⟩
          simp only [if_pos hp,if_pos hM] at h ⊢
          omega
        · have hp : ¬ p (n+1) := fun he => hM he.2
          simp only [if_neg hp,if_neg hM] at h ⊢
          omega
    obtain ⟨N,hN⟩ := eventually_no_split (P := p) (b := d k+1) (by
      intro n
      by_cases hn : n ≤ k
      · rw [countPrefix_zeroBelow (fun _ hm hp => (Nat.not_le_of_lt (hm.trans_le hn)) hp.1)]
        exact Nat.zero_le _
      · have h := hbudget (n-1) (by omega)
        rw [show n-1+1=n by omega] at h
        omega)
    exact ⟨N,fun n hn hk h => hN n hn ⟨hk,h⟩⟩
  refine isHyperfinite_of_eventual (fun n => (B n).main.relation) (fun n =>
    ⟨⟨(B n).main.equivalence_relation,(B n).main.measurableSet_relation⟩,
      (B n).main.finite_class⟩) ?_
  intro x y
  constructor
  · rintro ⟨j,r,h⟩
    let k := max j r
    have hxyk : (D k).near (B k).radius x y :=
      (D k).mono ((le_max_right _ _).trans (B k).stage_le) (hDN (le_max_left _ _) h)
    obtain ⟨N,hN⟩ := havoid k x
    refine ⟨max N k,fun n hn => ?_⟩
    have hk : k ≤ n := (le_max_right _ _).trans hn
    apply (B n).main.relation_of_no_split (hN n ((le_max_left _ _).trans hn) hk)
      ((D k).refl _ x) hxyk
    have hrn : (B k).radius ≤ (B n).radius := hR hk
    exact (D n).mono (by omega) (hDN hk hxyk)
  · rintro ⟨n,hn⟩
    exact ⟨n,(B n).main.bound,(B n).main.near_of_relation (hn n le_rfl)⟩

/-- Weighted generator costs turn the finitely generated stages' Borel
core exhaustions into a hyperfinite orbit relation. -/
theorem hyperfinite_of_word_cores {G : Type*} [Group G] [Countable G]
    [MulAction G X] [StandardBorelSpace X] (hact : BorelAction G X)
    (hcore : ∀ (A : Finset G) (hA : SymmetricMoves A),
      HasCoreExhaustion (wordNear A hA hact)) :
    IsHyperfinite (orbitRel G : X → X → Prop) := by
  obtain ⟨S,hS,hss,hsall⟩ := exists_symmetric_exhaustion G
  choose b K hKm hK hKall hKb using fun n => hcore (S n) (hss n)
  let D := stageNear S K hS hss hK hact
  let d : ℕ → ℕ := Nat.rec 0 (fun n t => b n+t+1)
  have hD (n : ℕ) : BorelAsdimLE (D n) (d n) univ := by
    induction n with
    | zero => exact stageNear_asdim_zero S K hS hss hK hact
    | succ n ih => exact stageNear_asdim_succ S K hS hss hK hact (hKm n) ih (hKb n)
  have hh := hyperfinite_of_decreasing_near D d hD
    (by intro n r x y h; exact stageNear_compatible S K hS hss hK hact (Nat.le_succ n) h)
  have heq : (fun x y => ∃ n r, (D n).near r x y) = orbitRel G := by
    funext x y
    exact propext (stageNear_fixed_orbit_rel S K hS hss hK hact hsall hKm hKall x y)
  exact heq ▸ hh

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.CompatibleUnion

-- BEGIN COMPLETE MODULE HirschProof.GeneratedStage
section
                                  

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

variable {G X : Type*} [Group G]

noncomputable def liftGenerators (A : Finset G) :
    Finset (Subgroup.closure (A : Set G)) :=
  A.attach.map {
    toFun := fun a => ⟨a.val,Subgroup.subset_closure a.property⟩
    inj' := by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun q : Subgroup.closure (A : Set G) => q.val) h }

theorem mem_liftGenerators (A : Finset G) (g : Subgroup.closure (A : Set G)) :
    g ∈ liftGenerators A ↔ g.val ∈ A := by
  simp only [liftGenerators,Finset.mem_map]
  exact ⟨fun ⟨a,_,ha⟩ => (congrArg Subtype.val ha) ▸ a.property,
    fun hg => ⟨⟨g.val,hg⟩,Finset.mem_attach _ _,Subtype.ext rfl⟩⟩

theorem liftGenerators_symmetric (A : Finset G) (hA : SymmetricMoves A) :
    SymmetricMoves (liftGenerators A) := by
  intro g hg
  exact (mem_liftGenerators A g⁻¹).2 (hA ((mem_liftGenerators A g).1 hg))

theorem closure_liftGenerators (A : Finset G) :
    Subgroup.closure (liftGenerators A : Set (Subgroup.closure (A : Set G))) = ⊤ := by
  let H := Subgroup.closure (A : Set G)
  have himg : H.subtype '' (liftGenerators A : Set H) = (A : Set G) := by
    ext g
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact (mem_liftGenerators A u).mp hu
    · intro hg
      let u : H := ⟨g,Subgroup.subset_closure hg⟩
      exact ⟨u,(mem_liftGenerators A u).mpr hg,rfl⟩
  have hmap : (Subgroup.closure (liftGenerators A : Set H)).map H.subtype = H := by
    rw [H.subtype.map_closure,himg]
  apply top_unique
  intro g _
  have hg : g.val ∈ (Subgroup.closure (liftGenerators A : Set H)).map H.subtype := hmap.symm ▸ g.property
  exact (Subgroup.mem_map_iff_mem H.subtype_injective).1 hg

variable [MulAction G X] [Countable G] [MeasurableSpace X] [StandardBorelSpace X]

theorem wordNear_liftGenerators (A : Finset G) (hA : SymmetricMoves A)
    (hact : BorelAction G X) (r : ℕ) (x y : X) :
    (wordNear A hA hact).near r x y ↔
    (wordNear (liftGenerators A) (liftGenerators_symmetric A hA) (fun g => hact g.val)).near r x y := by
  constructor
  · rintro ⟨a,ha,h⟩
    refine ⟨a,ha,h.mono ?_⟩
    rintro k u v ⟨hk,g,hg,hg'⟩
    let g' : Subgroup.closure (A : Set G) := ⟨g,Subgroup.subset_closure hg⟩
    exact ⟨hk,g',(mem_liftGenerators A g').mpr hg,hg'⟩
  · rintro ⟨a,ha,h⟩
    refine ⟨a,ha,h.mono ?_⟩
    rintro k u v ⟨hk,g,hg,hg'⟩
    exact ⟨hk,g.val,(mem_liftGenerators A g).mp hg,hg'⟩

omit [MulAction G X] [Countable G] [StandardBorelSpace X] in
theorem coreExhaustion_of_same_near (D D' : BorelNear X)
    (h : ∀ r x y, D.near r x y ↔ D'.near r x y) (hD' : HasCoreExhaustion D') :
    HasCoreExhaustion D := by
  obtain ⟨b,K,hKm,hK,hKall,hKb⟩ := hD'
  refine ⟨b,K,hKm,hK,hKall,fun j r => ?_⟩
  obtain ⟨U,R,hU,hUm,hUall,hUb⟩ := hKb j r
  refine ⟨U,R,hU,hUm,hUall,?_⟩
  intro i x y hxy
  exact (h R x y).mpr (hUb i (D.comp_mono_near D' (by
    intro a b _ _ hab
    exact (h r a b).mp hab) hxy))

/-- The local-to-global argument can test only word metrics of the
finitely generated subgroups with the restricted action. -/
theorem hyperfinite_of_finitely_generated_cores (hact : BorelAction G X)
    (hcore : ∀ (H : Subgroup G) (A : Finset H) (hA : SymmetricMoves A),
      Subgroup.closure (A : Set H) = ⊤ →
      HasCoreExhaustion (wordNear A hA (fun g => hact g.val))) :
    IsHyperfinite (orbitRel G : X → X → Prop) := by
  apply hyperfinite_of_word_cores hact
  intro A hA
  exact coreExhaustion_of_same_near _ _ (wordNear_liftGenerators A hA hact)
    (hcore _ _ _ (closure_liftGenerators A))

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.GeneratedStage

-- BEGIN COMPLETE MODULE HirschProof.CoreTransfers
section
                               
                               

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Pulling back bounded and measurable covers across a controlled finite-fiber map. -/
theorem asdim_pullback_finite_fibers (D : BorelNear X) (B : BorelNear Y)
    {A : Set X} {U : Set Y} (f : X → Y) (hf : Measurable f)
    (hA : MeasurableSet A) (hfA : MapsTo f A U)
    (hcontrolled : ∀ r : ℕ, ∃ s : ℕ, ∀ ⦃x y⦄,
      x ∈ A → y ∈ A → D.near r x y → B.near s (f x) (f y))
    (hfinite : ∃ N : ℕ, ∀ y : Y, ∃ t : Finset X, t.card ≤ N ∧
      ∀ x ∈ A, f x = y → x ∈ t)
    {d : ℕ} (hU : BorelAsdimLE B d U) : BorelAsdimLE D d A := by
  classical
  obtain ⟨N,hN⟩ := hfinite
  choose fibers hfcard hfmem using hN
  intro r
  obtain ⟨s,hs⟩ := hcontrolled r
  obtain ⟨V,R,hV,hVm,hcov,hcomp⟩ := hU s
  obtain ⟨M,hM⟩ := B.uniformly_finite R
  let W i := A ∩ f ⁻¹' V i
  refine ⟨W,r*(M*N),fun _ => inter_subset_left,
    fun i => hA.inter ((hVm i).preimage hf),?_,?_⟩
  · intro x hx
    obtain ⟨i,hix⟩ := hcov (f x) (hfA hx)
    exact ⟨i,hx,hix⟩
  · intro i
    apply D.boundComp_of_small
    intro x
    obtain ⟨t,ht,hball⟩ := hM (f x)
    refine ⟨t.biUnion fibers,?_,?_⟩
    · calc
        (t.biUnion fibers).card ≤ ∑ y ∈ t, (fibers y).card := Finset.card_biUnion_le
        _ ≤ t.card * N := Finset.sum_le_card_nsmul _ _ _ (fun y _ => hfcard y)
        _ ≤ M * N := Nat.mul_le_mul_right N ht
    · intro y hxy
      have hmap : B.comp s (V i) (f x) (f y) := by
        apply D.comp_map f (fun _ h => h.2) _ hxy
        intro a b ha hb hab
        exact hs ha.1 hb.1 hab
      exact Finset.mem_biUnion.mpr
        ⟨f y,hball _ (hcomp i hmap),hfmem _ y (D.comp_end hxy).1 rfl⟩

/-- A core exhaustion on a complete section thickens to an exhaustion
of the whole space with the same dimension upper bound. -/
theorem core_exhaustion_of_complete_section (D : BorelNear X)
    (Z : Set X) (hZ : ∀ x : X, ∃ y ∈ Z, ∃ r, D.near r x y)
    (d : ℕ) (V : ℕ → Set X) (hmono : Monotone V)
    (hVm : ∀ i, MeasurableSet (V i)) (hcover : Z ⊆ ⋃ i, V i)
    (hV : ∀ i, BorelAsdimLE D d (V i)) : HasCoreExhaustion D := by
  refine ⟨d,fun i => D.thicken (V i) i,?_,
    fun i => D.measurableSet_thicken (hVm i) i,?_,fun i => D.asdim_thicken (hV i)⟩
  · intro i j hij
    exact (D.thicken_mono_set (hmono hij) i).trans (D.thicken_mono_radius (V j) hij)
  · intro x
    obtain ⟨y,hy,r,hr⟩ := hZ x
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover hy)
    exact ⟨max r i,y,hmono (le_max_right r i) hi,D.mono (le_max_left r i) hr⟩

/-- Combine finitely many same-color covers on distinct invariant pieces. -/
theorem asdim_finset_invariant_union {J : Type*} (D : BorelNear X)
    (t : Finset J) (P V : J → Set X) (hVP : ∀ j ∈ t, V j ⊆ P j)
    (hsep : ∀ j ∈ t, ∀ k ∈ t, ∀ x ∈ P j, ∀ y ∈ P k,
      (∃ r, D.near r x y) → j = k)
    (d : ℕ) (hV : ∀ j ∈ t, BorelAsdimLE D d (V j)) :
    BorelAsdimLE D d (⋃ j ∈ t, V j) := by
  classical
  intro r
  let Jt := {j // j ∈ t}
  have hx (j : Jt) := hV j.val j.property r
  choose U R hU hUm hcov hbound using hx
  let W (i : Fin (d+1)) := ⋃ j : Jt, U j i
  have hW (i : Fin (d+1)) : W i ⊆ ⋃ j ∈ t, V j := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨j.val,mem_iUnion.mpr ⟨j.property,hU j i hj⟩⟩
  let Rmax := Finset.univ.sup R
  refine ⟨W,Rmax,hW,fun i => MeasurableSet.iUnion (fun j => hUm j i),?_,?_⟩
  · intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨j,hj,hx⟩ := hx
    obtain ⟨i,hi⟩ := hcov ⟨j,hj⟩ x hx
    exact ⟨i,mem_iUnion.mpr ⟨⟨j,hj⟩,hi⟩⟩
  · intro i x y hxy
    obtain ⟨j,hxj⟩ := mem_iUnion.mp hxy.1
    have hcomp : D.comp r (U j i) x y := by
      refine ⟨hxj,?_⟩
      have path := hxy.2
      clear hxy
      induction path with
      | refl => exact .refl
      | @tail a b ha hab ih =>
        have haj := D.comp_end ⟨hxj,ih⟩
        obtain ⟨k,hbk⟩ := mem_iUnion.mp hab.2.1
        have hjk : j = k := Subtype.ext (hsep j.val j.property k.val k.property
          a (hVP j.val j.property (hU j i haj)) b (hVP k.val k.property (hU k i hbk)) ⟨r,hab.2.2⟩)
        subst k
        exact ih.tail ⟨haj,hbk,hab.2.2⟩
    exact D.mono (Finset.le_sup (f := R) (Finset.mem_univ j)) (hbound j i hcomp)

/-- Invariant pieces can be exhausted together when their bounds on dimension agree. -/
theorem core_exhaustion_of_invariant_pieces (D : BorelNear X)
    (d : ℕ) (P : ℕ → Set X) (V : ℕ → ℕ → Set X)
    (hVP : ∀ j n, V j n ⊆ P j)
    (hsep : ∀ j k, ∀ x ∈ P j, ∀ y ∈ P k, (∃ r, D.near r x y) → j = k)
    (hVmono : ∀ j, Monotone (V j)) (hVm : ∀ j n, MeasurableSet (V j n))
    (hcov : ∀ x : X, ∃ j n, x ∈ V j n) (hV : ∀ j n, BorelAsdimLE D d (V j n)) :
    HasCoreExhaustion D := by
  let W (n : ℕ) := ⋃ j ∈ Finset.range (n+1), V j n
  refine ⟨d,W,?_,fun n => MeasurableSet.iUnion (fun j =>
    MeasurableSet.iUnion (fun _ : j ∈ Finset.range (n+1) => hVm j n)),?_,?_⟩
  · intro n m hnm x hx
    simp only [W,mem_iUnion] at hx ⊢
    obtain ⟨j,hj,hx⟩ := hx
    exact ⟨j,Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le (Nat.succ_le_succ hnm)),
      hVmono j hnm hx⟩
  · intro x
    obtain ⟨j,n,hx⟩ := hcov x
    refine ⟨max j n,?_⟩
    simp only [W,mem_iUnion]
    exact ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_left j n)),
      hVmono j (le_max_right j n) hx⟩
  · intro n
    exact asdim_finset_invariant_union D (Finset.range (n+1)) P (fun j => V j n)
      (fun j _ => hVP j n) (fun j _ k _ => hsep j k) d (fun j _ => hV j n)

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.CoreTransfers

-- BEGIN COMPLETE MODULE HirschProof.BoundedPartitions
section
                                
                            
                                    

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

variable {X : Type*} [MeasurableSpace X]

def tileSet (D : BorelNear X) (E : Setoid X) (A : Set X) (r : ℕ) (x : X) : Set (Quotient E) :=
  Quotient.mk E '' (A ∩ D.ball x r)

theorem tileSet_finite (D : BorelNear X) (E : Setoid X) (A : Set X) (r : ℕ) (x : X) :
    (tileSet D E A r x).Finite :=
  ((D.ball_finite r x).subset inter_subset_right).image _

def BoundedPartitionAt (D : BorelNear X) (A : Set X) (r n : ℕ) : Prop :=
  ∃ E : Setoid X, ∃ R : ℕ,
    MeasurableSet {p : X × X | E.r p.1 p.2} ∧
    (∀ x ∈ A, ∀ y ∈ A, E.r x y → D.near R x y) ∧
    ∀ x ∈ A, (tileSet D E A r x).ncard ≤ n

private theorem measurableSet_le_tileCount (D : BorelNear X) (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2}) {A : Set X} (hA : MeasurableSet A)
    (r k : ℕ) : MeasurableSet {x | k ≤ (tileSet D E A r x).ncard} := by
  classical
  have witness (x : X) : k ≤ (tileSet D E A r x).ncard ↔
      ∃ z : Fin k → ℕ,
        (∀ i, D.moves (z i) x ∈ A ∧ D.near r x (D.moves (z i) x)) ∧
        (∀ i j, i ≠ j → ¬ E.r (D.moves (z i) x) (D.moves (z j) x)) := by
    constructor
    · intro h
      let T := tileSet D E A r x
      letI : Fintype T := (tileSet_finite D E A r x).fintype
      have hc : Fintype.card (Fin k) ≤ Fintype.card T := by
        change k ≤ Nat.card T at h
        simpa only [Fintype.card_fin,Nat.card_eq_fintype_card] using h
      obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
      have hy (i : Fin k) : ∃ y, (y ∈ A ∧ D.near r x y) ∧ Quotient.mk E y = (f i).val :=
        (f i).property
      choose y hY hQ using hy
      choose z hz using fun i => D.moves_cover (hY i).2
      refine ⟨z,fun i => (hz i).symm ▸ hY i,?_⟩
      intro i j hij hrel
      apply hij
      apply f.injective
      apply Subtype.ext
      rw [← hQ i, ← hQ j]
      exact Quotient.sound (by simpa only [hz] using hrel)
    · rintro ⟨z,hz,hsep⟩
      let f (i : Fin k) : Quotient E := Quotient.mk E (D.moves (z i) x)
      have hmem (i : Fin k) : f i ∈ tileSet D E A r x := ⟨_,hz i,rfl⟩
      have hf : Function.Injective f := fun i j he => by
        by_contra hn
        exact hsep i j hn (Quotient.exact he)
      calc
        k = (Set.range f).ncard := by rw [Set.ncard_range_of_injective hf,Nat.card_fin]
        _ ≤ (tileSet D E A r x).ncard :=
          Set.ncard_le_ncard (range_subset_iff.mpr hmem) (tileSet_finite D E A r x)
  have heq : {x | k ≤ (tileSet D E A r x).ncard} = ⋃ z : Fin k → ℕ,
      ((⋂ i, {x | D.moves (z i) x ∈ A ∧ D.near r x (D.moves (z i) x)}) ∩
       ⋂ i : Fin k, ⋂ j : Fin k, ⋂ _ : i ≠ j, {x | ¬ E.r (D.moves (z i) x) (D.moves (z j) x)}) := by
    ext x
    simpa only [mem_iUnion,mem_inter_iff, mem_iInter,mem_setOf_eq] using witness x
  rw [heq]
  refine MeasurableSet.iUnion fun z => (MeasurableSet.iInter fun i =>
    (hA.preimage (D.measurable_moves (z i))).inter
      ((D.borel r).preimage (measurable_id.prodMk (D.measurable_moves (z i))))).inter ?_
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ : i ≠ j =>
    (hE.preimage ((D.measurable_moves (z i)).prodMk (D.measurable_moves (z j)))).compl

private theorem measurableSet_eq_tileCount (D : BorelNear X) (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2}) {A : Set X} (hA : MeasurableSet A)
    (r k : ℕ) : MeasurableSet {x | (tileSet D E A r x).ncard = k} := by
  have he : {x | (tileSet D E A r x).ncard = k} =
      {x | k ≤ (tileSet D E A r x).ncard} \ {x | k+1 ≤ (tileSet D E A r x).ncard} := by
    ext x; simp only [mem_setOf_eq,mem_diff]; omega
  rw [he]
  exact (measurableSet_le_tileCount D E hE hA r k).diff
    (measurableSet_le_tileCount D E hE hA r (k+1))

private theorem exists_stable_count (n : ℕ) (b : ℕ → ℕ)
    (hmono : Monotone b) (hfirst : 1 ≤ b 0) (hlast : b (n+1) ≤ n+1) :
    ∃ i : Fin (n+1), b i.val = i.val+1 ∧ b (i.val+1) = i.val+1 := by
  classical
  have hex : ∃ j, b (j+1) ≤ j+1 := ⟨n,hlast⟩
  let i := Nat.find hex
  have hi : i ≤ n := Nat.find_min' hex hlast
  have hi' : b (i+1) ≤ i+1 := Nat.find_spec hex
  have hi₀ : i+1 ≤ b i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · simpa [h] using hfirst
    · have hmin := Nat.find_min hex (show i-1 < i by omega)
      have he : i-1+1 = i := by omega
      rw [he] at hmin
      omega
  have hm : b i ≤ b (i+1) := hmono (Nat.le_succ i)
  exact ⟨⟨i,by omega⟩,(show b i = i+1 by omega),(show b (i+1) = i+1 by omega)⟩

/-- The bounded partition criterion implies the Borel component-cover criterion. -/
theorem asdim_of_bounded_partitions (D : BorelNear X) {A : Set X} (hA : MeasurableSet A)
    (d : ℕ) (h : ∀ r : ℕ, BoundedPartitionAt D A r (d+1)) : BorelAsdimLE D d A := by
  classical
  intro r
  obtain ⟨E,R,hE,hDiam,hAt⟩ := h ((d+2)*r)
  let B (x : X) (i : ℕ) := tileSet D E A ((i+1)*r) x
  let U (i : Fin (d+1)) := {x ∈ A | (B x i.val).ncard = i.val+1 ∧
    (B x (i.val+1)).ncard = i.val+1}
  have hB (x : X) {i j : ℕ} (hij : i ≤ j) : B x i ⊆ B x j := by
    rintro t ⟨y,⟨hy,hxy⟩,rfl⟩
    exact ⟨y,⟨hy,D.mono (Nat.mul_le_mul_right r (Nat.succ_le_succ hij)) hxy⟩,rfl⟩
  have hf (x : X) (i : ℕ) : (B x i).Finite := tileSet_finite ..
  have hop (i : Fin (d+1)) {x y : X} (hx : x ∈ U i) (hy : y ∈ U i) (hxy : D.near r x y) :
      B x i.val = B y i.val := by
    have hrad : r+(i.val+1)*r = (i.val+1+1)*r := by
      rw [Nat.add_mul (i.val+1) 1 r,Nat.one_mul,Nat.add_comm r]
    have hx' : B x i.val = B x (i.val+1) :=
      Set.eq_of_subset_of_ncard_le (hB x (Nat.le_succ _)) (le_of_eq (hx.2.2.trans hx.2.1.symm)) (hf _ _)
    have hy' : B y i.val = B y (i.val+1) :=
      Set.eq_of_subset_of_ncard_le (hB y (Nat.le_succ _)) (le_of_eq (hy.2.2.trans hy.2.1.symm)) (hf _ _)
    refine Set.Subset.antisymm ?_ ?_
    · rw [hy']
      rintro z ⟨w,⟨hw,hxw⟩,rfl⟩
      exact ⟨w,⟨hw,by
        exact hrad ▸ D.triangle (D.symm r hxy) hxw⟩,rfl⟩
    · rw [hx']
      rintro z ⟨w,⟨hw,hyw⟩,rfl⟩
      exact ⟨w,⟨hw,by
        exact hrad ▸ D.triangle hxy hyw⟩,rfl⟩
  refine ⟨U,R+(d+1)*r,fun _ _ hx => hx.1,fun i => ?_,?_,?_⟩
  · exact hA.inter ((measurableSet_eq_tileCount D E hE hA ((i.val+1)*r) (i.val+1)).inter
      (measurableSet_eq_tileCount D E hE hA ((i.val+1+1)*r) (i.val+1)))
  · intro x hx
    have hxq : Quotient.mk E x ∈ B x 0 := ⟨x,⟨hx,D.refl _ x⟩,rfl⟩
    obtain ⟨i,hi,hj⟩ := exists_stable_count d (fun i => (B x i).ncard)
      (fun _ _ hij => Set.ncard_le_ncard (hB x hij) (hf _ _))
      (Nat.succ_le_of_lt ((Set.ncard_pos (hf _ _)).mpr ⟨_,hxq⟩)) (hAt x hx)
    exact ⟨i,hx,hi,hj⟩
  · intro i x y hxy
    have hconst : B x i.val = B y i.val := by
      have hp := hxy.2
      clear hxy
      induction hp with
      | refl => rfl
      | @tail _ _ _ ht ih => exact ih.trans (hop i ht.1 ht.2.1 ht.2.2)
    have hx : Quotient.mk E x ∈ B x i.val := ⟨x,⟨hxy.1.1,D.refl _ x⟩,rfl⟩
    rw [hconst] at hx
    obtain ⟨w,⟨hw,hyw⟩,hrel⟩ := hx
    refine D.mono (Nat.add_le_add_left (Nat.mul_le_mul_right r ?_) R)
      (D.triangle (hDiam x hxy.1.1 w hw (E.iseqv.symm (Quotient.exact hrel))) (D.symm _ hyw))
    exact Nat.succ_le_succ (Nat.le_of_lt_succ i.isLt)

/-- Borel component covers yield Borel bounded partitions with bounded ball multiplicity. -/
theorem bounded_partitions_of_asdim [MeasurableEq X] (D : BorelNear X)
    {A : Set X} {d : ℕ} (h : BorelAsdimLE D d A) (r : ℕ) : BoundedPartitionAt D A r (d+1) := by
  classical
  obtain ⟨V,R,hV,hVm,hcov,hcomp⟩ := h (r+r)
  let W (i : Fin (d+1)) := V i \ ⋃ j : Fin (d+1), ⋃ _ : j < i, V j
  have hWV (i : Fin (d+1)) : W i ⊆ V i := fun _ hx => hx.1
  have hWA (i : Fin (d+1)) : W i ⊆ A := (hWV i).trans (hV i)
  have hWm (i : Fin (d+1)) : MeasurableSet (W i) :=
    (hVm i).diff (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ : j < i => hVm j)
  have heq : ∀ {x : X} {i j : Fin (d+1)}, x ∈ W i → x ∈ W j → i = j := by
    intro x i j hi hj
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim (hj.2 (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hij,hi.1⟩⟩))
    · exact hij
    · exact False.elim (hi.2 (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hij,hj.1⟩⟩))
  have hc (x : X) (hx : x ∈ A) : ∃ i, x ∈ W i := by
    have hex : ∃ n : ℕ, ∃ h : n < d+1, x ∈ V ⟨n,h⟩ := by
      obtain ⟨i,hi⟩ := hcov x hx
      exact ⟨i.val,i.isLt,hi⟩
    obtain ⟨hi,hVx⟩ := Nat.find_spec hex
    refine ⟨⟨Nat.find hex,hi⟩,hVx,?_⟩
    rintro hb
    obtain ⟨j,hj⟩ := mem_iUnion.mp hb
    obtain ⟨hji,hxj⟩ := mem_iUnion.mp hj
    exact Nat.find_min hex hji ⟨j.isLt,hxj⟩
  let relation (x y : X) := x = y ∨ ∃ i, D.comp (r+r) (W i) x y
  let E : Setoid X := ⟨relation,⟨fun _ => Or.inl rfl,by
    rintro x y (hxy | ⟨i,hxy⟩)
    · exact Or.inl hxy.symm
    · exact Or.inr ⟨i,D.comp_symm hxy⟩, by
    rintro x y z (rfl | ⟨i,hxy⟩) h2
    · exact h2
    · rcases h2 with rfl | ⟨j,hyz⟩
      · exact Or.inr ⟨i,hxy⟩
      · have hij := heq (D.comp_end hxy) (D.comp_start hyz)
        exact Or.inr ⟨i,D.comp_trans hxy (hij.symm ▸ hyz)⟩⟩⟩
  let label : X → Fin (d+1) := fun x => if hx : x ∈ A then (hc x hx).choose else 0
  have hlabel {x : X} (hx : x ∈ A) : x ∈ W (label x) := by
    simp only [label,dif_pos hx]
    exact (hc x hx).choose_spec
  have hlabelE {x y : X} (hxy : E.r x y) : label x = label y := by
    rcases hxy with rfl | ⟨i,hi⟩
    · rfl
    · exact (heq (hlabel (hWA i (D.comp_start hi))) (D.comp_start hi)).trans
        (heq (D.comp_end hi) (hlabel (hWA i (D.comp_end hi))))
  let q : Quotient E → Fin (d+1) := Quotient.lift label (fun _ _ h => hlabelE h)
  refine ⟨E,R,?_,?_,?_⟩
  · have hre : {p : X × X | E.r p.1 p.2} = {p | p.1 = p.2} ∪
        ⋃ i : Fin (d+1), {p | D.comp (r+r) (W i) p.1 p.2} := by
      ext p
      change relation p.1 p.2 ↔ p ∈ _
      simp [relation]
    rw [hre]
    exact (measurableSet_eq_fun measurable_fst measurable_snd).union
      (MeasurableSet.iUnion fun i => D.measurableSet_comp (hWm i) (r+r))
  · rintro x _ y _ (rfl | ⟨i,hxy⟩)
    · exact D.refl _ _
    · exact hcomp i (D.comp_mono (hWV i) le_rfl hxy)
  · intro x _
    have hi : InjOn q (tileSet D E A r x) := by
      rintro _ ⟨a,⟨ha,hxa⟩,rfl⟩ _ ⟨b,⟨hb,hxb⟩,rfl⟩ hab
      change label a = label b at hab
      apply Quotient.sound
      exact Or.inr ⟨label a,D.comp_single (hlabel ha) (hab.symm ▸ hlabel hb)
        (D.triangle (D.symm r hxa) hxb)⟩
    calc
      _ ≤ (Set.univ : Set (Fin (d+1))).ncard :=
        Set.ncard_le_ncard_of_injOn q (fun _ _ => mem_univ _) hi
      _ = d+1 := by simp

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.BoundedPartitions

-- BEGIN COMPLETE MODULE HirschProof.FiniteIndexCores
section
                                    
                                
                                                      

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

variable {X : Type*} [MeasurableSpace X] {J : Type*} [Fintype J]

/-- Two tuples label the same multiset of tiles when a permutation pairs related entries. -/
def tileTupleSetoid (E : Setoid X) (f : J → X → X) : Setoid X where
  r x y := ∃ p : Equiv.Perm J, ∀ i : J, E.r (f i x) (f (p i) y)
  iseqv := ⟨fun x => ⟨Equiv.refl J,fun i => E.iseqv.refl _⟩,by
    rintro x y ⟨p,hp⟩
    refine ⟨p.symm,fun i => E.iseqv.symm ?_⟩
    simpa only [Equiv.apply_symm_apply] using hp (p.symm i),by
    rintro x y z ⟨p,hp⟩ ⟨q,hq⟩
    exact ⟨p.trans q,fun i => E.iseqv.trans (hp i) (hq (p i))⟩⟩

theorem tileTuple_borel (E : Setoid X) (f : J → X → X) (hf : ∀ i, Measurable (f i))
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2}) :
    MeasurableSet {p : X × X | (tileTupleSetoid E f).r p.1 p.2} := by
  classical
  have he : {p : X × X | (tileTupleSetoid E f).r p.1 p.2} =
      ⋃ w : Equiv.Perm J, ⋂ i : J, {p | E.r (f i p.1) (f (w i) p.2)} := by
    ext p
    change (∃ w : Equiv.Perm J, ∀ i, E.r (f i p.1) (f (w i) p.2)) ↔ p ∈ _
    simp only [mem_setOf_eq,mem_iUnion,mem_iInter]
  rw [he]
  exact MeasurableSet.iUnion fun w => MeasurableSet.iInter fun i =>
    hE.preimage (((hf i).comp measurable_fst).prodMk ((hf (w i)).comp measurable_snd))

private theorem tuple_tile_count (D B : BorelNear X) (E : Setoid X) (f : J → X → X)
    {A T : Set X} (hAT : ∀ i, MapsTo (f i) A T) {r s n : ℕ}
    (hAt : ∀ x ∈ T, (tileSet B E T s x).ncard ≤ n)
    (hmatch : ∀ ⦃x y⦄, x ∈ A → y ∈ A → D.near r x y →
      ∃ p : Equiv.Perm J, ∀ i, B.near s (f i x) (f (p i) y)) (x : X) (hx : x ∈ A) :
    (tileSet D (tileTupleSetoid E f) A r x).ncard ≤ n ^ Fintype.card J := by
  classical
  let Q := tileTupleSetoid E f
  let P := tileSet D Q A r x
  let T' (i : J) := tileSet B E T s (f i x)
  have hP (a : P) : ∃ y, (y ∈ A ∧ D.near r x y) ∧ Quotient.mk Q y = a.val := a.property
  choose y hy hq using hP
  choose perm hperm using fun a : P => hmatch hx (hy a).1 (hy a).2
  let mark (a : P) (i : J) : T' i :=
    ⟨Quotient.mk E (f (perm a i) (y a)),⟨_,⟨hAT _ (hy a).1,hperm a i⟩,rfl⟩⟩
  have hmark : Function.Injective mark := by
    intro a b hab
    apply Subtype.ext
    rw [← hq a,← hq b]
    apply Quotient.sound
    refine ⟨(perm a).symm.trans (perm b),?_⟩
    intro i
    have hi := congrArg Subtype.val (congrFun hab ((perm a).symm i))
    have hi' := Quotient.exact hi
    simpa only [Equiv.apply_symm_apply,Equiv.trans_apply] using hi'
  letI : Fintype P := (tileSet_finite D Q A r x).fintype
  letI (i : J) : Fintype (T' i) := (tileSet_finite B E T s (f i x)).fintype
  change Nat.card P ≤ n ^ Fintype.card J
  rw [Nat.card_eq_fintype_card]
  refine (Fintype.card_le_of_injective mark hmark).trans ?_
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _i : J, n := Finset.prod_le_prod' (fun i _ => by
      have h := hAt (f i x) (hAT i hx)
      change Nat.card (T' i) ≤ n at h
      simpa only [Nat.card_eq_fintype_card] using h)
    _ = n ^ Fintype.card J := by simp

/-- The finite-index comparison of core dimensions, expressed through finite
families of right-coset moves and their edge comparison. -/
theorem asdim_of_finite_coset_moves [MeasurableEq X] (D B : BorelNear X)
    (f : J → X → X) (hf : ∀ i, Measurable (f i))
    (hidentity : ∃ i, f i = id) (b : ℕ) (hshort : ∀ i x, D.near b x (f i x))
    {A T : Set X} (hA : MeasurableSet A) (hAT : ∀ i, MapsTo (f i) A T)
    (hmatch : ∀ r : ℕ, ∃ s : ℕ, ∀ ⦃x y⦄, x ∈ A → y ∈ A → D.near r x y →
      ∃ p : Equiv.Perm J, ∀ i, B.near s (f i x) (f (p i) y))
    (hcompare : ∀ s : ℕ, ∃ r : ℕ, ∀ ⦃x y⦄, x ∈ T → y ∈ T → B.near s x y → D.near r x y)
    (d : ℕ) (hT : BorelAsdimLE B d T) :
    BorelAsdimLE D ((d+1) ^ Fintype.card J - 1) A := by
  classical
  obtain ⟨i₀,hi₀⟩ := hidentity
  have hpow : 0 < (d+1) ^ Fintype.card J := Nat.pow_pos (Nat.succ_pos _)
  apply asdim_of_bounded_partitions D hA
  intro r
  obtain ⟨s,hs⟩ := hmatch r
  obtain ⟨E,R,hE,hDiam,hAt⟩ := bounded_partitions_of_asdim B hT s
  obtain ⟨R',hR'⟩ := hcompare R
  refine ⟨tileTupleSetoid E f,R'+b,tileTuple_borel E f hf hE,?_,?_⟩
  · rintro x hx y hy ⟨p,hp⟩
    have hnear : D.near R' (f i₀ x) (f (p i₀) y) :=
      hR' (hAT _ hx) (hAT _ hy) (hDiam _ (hAT _ hx) _ (hAT _ hy) (hp i₀))
    rw [hi₀] at hnear
    exact D.triangle hnear (D.symm b (hshort (p i₀) y))
  · intro x hx
    have hb := tuple_tile_count D B E f hAT hAt hs x hx
    omega

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.FiniteIndexCores

-- BEGIN COMPLETE MODULE HirschProof.ProperOrbitMetrics
section
                                          
                                 

set_option autoImplicit false
noncomputable section

namespace LocalHirschHyperfinite

open Set

/-- Closed integer balls for a left-invariant proper length on a countable group. -/
structure ProperGroupBalls (G : Type*) [Group G] where
  ball : ℕ → Finset G
  one_mem : ∀ r, 1 ∈ ball r
  inv_mem : ∀ {r g}, g ∈ ball r → g⁻¹ ∈ ball r
  mul_mem : ∀ {r s g h}, g ∈ ball r → h ∈ ball s → h*g ∈ ball (r+s)
  mono : Monotone ball
  zero : ∀ {g}, g ∈ ball 0 → g = 1
  exhaustive : ∀ g, ∃ r, g ∈ ball r

namespace ProperGroupBalls

variable {G : Type*} [Group G]

theorem finite_subset (B : ProperGroupBalls G) (F : Finset G) :
    ∃ r, ∀ g ∈ F, g ∈ B.ball r := by
  classical
  choose r hr using B.exhaustive
  exact ⟨F.sup r, fun g hg => B.mono (Finset.le_sup hg) (hr g)⟩

/-- The enumerated letter with index `i` and its inverse both cost `i+1`. -/
private def weightedStep (e : ℕ → G) (a : ℕ) (x y : G) : Prop :=
  ∃ i, a = i+1 ∧ (e i*x = y ∨ (e i)⁻¹*x = y)

private theorem weightedStep_symm (e : ℕ → G) :
    ∀ a x y, weightedStep e a x y → weightedStep e a y x := by
  rintro a x y ⟨i,hi,hxy | hxy⟩
  · exact ⟨i,hi,Or.inr (by rw [← hxy, inv_mul_cancel_left])⟩
  · exact ⟨i,hi,Or.inl (by rw [← hxy, mul_inv_cancel_left])⟩

private theorem weightedWalk_right_mul (e : ℕ → G) {x y : G} {a : ℕ}
    (h : CostWalk (weightedStep e) x y a) (z : G) :
    CostWalk (weightedStep e) (x*z) (y*z) a := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih =>
    obtain ⟨i,hi,hxy | hxy⟩ := h
    · exact .cons ⟨i,hi,Or.inl (by rw [← mul_assoc, hxy])⟩ ih
    · exact .cons ⟨i,hi,Or.inr (by rw [← mul_assoc, hxy])⟩ ih

private theorem weightedWalk_finiteBound [DecidableEq G] (e : ℕ → G) {r a : ℕ} {x y : G}
    (h : CostWalk (weightedStep e) x y a) (har : a ≤ r) :
    ∃ g ∈ wordBall (((Finset.range r).image e) ∪ ((Finset.range r).image fun i => (e i)⁻¹)) a,
      g*x = y := by
  classical
  let A := ((Finset.range r).image e) ∪ ((Finset.range r).image fun i => (e i)⁻¹)
  change ∃ g ∈ wordBall A a, g*x = y
  induction h with
  | nil => exact ⟨1,one_mem_wordBall A 0,one_mul _⟩
  | @cons x y z a b hs _ ih =>
    obtain ⟨k,hk,hkz⟩ := ih (by omega)
    obtain ⟨i,hi,his | his⟩ := hs
    · have hm : e i ∈ A := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))
      exact ⟨k*e i,wordBall_mono A (by omega) (wordBall_append_mem A hk hm),
        by rw [mul_assoc,his,hkz]⟩
    · have hm : (e i)⁻¹ ∈ A := Finset.mem_union_right _
        (Finset.mem_image_of_mem (fun j => (e j)⁻¹) (Finset.mem_range.mpr (by omega)))
      exact ⟨k*(e i)⁻¹,wordBall_mono A (by omega) (wordBall_append_mem A hk hm),
        by rw [mul_assoc,his,hkz]⟩

private def WeightedBall (e : ℕ → G) (r : ℕ) : Set G :=
  {g | ∃ a ≤ r, CostWalk (weightedStep e) 1 g a}

private theorem finite_weightedBall (e : ℕ → G) (r : ℕ) : (WeightedBall e r).Finite := by
  classical
  let A := ((Finset.range r).image e) ∪ ((Finset.range r).image fun i => (e i)⁻¹)
  apply (wordBall A r).finite_toSet.subset
  rintro g ⟨a,ha,h⟩
  obtain ⟨k,hk,he⟩ := weightedWalk_finiteBound e h ha
  have hkg : k = g := by simpa only [mul_one] using he
  subst k
  exact wordBall_mono A ha hk

/-- A chosen enumeration yields integer balls containing every group element at a finite radius. -/
def ofEnumeration (e : ℕ → G) (he : Function.Surjective e) : ProperGroupBalls G := by
  let B (n : ℕ) := (finite_weightedBall e n).toFinset
  have hB (n : ℕ) (g : G) : g ∈ B n ↔ ∃ a ≤ n, CostWalk (weightedStep e) 1 g a :=
    Set.Finite.mem_toFinset _
  refine {
    ball := B
    one_mem := fun r => (hB r 1).mpr ⟨0,Nat.zero_le r,.nil _⟩
    inv_mem := ?_
    mul_mem := ?_
    mono := ?_
    zero := ?_
    exhaustive := ?_ }
  · intro r g hg
    obtain ⟨a,ha,p⟩ := (hB r g).mp hg
    refine (hB r g⁻¹).mpr ⟨a,ha,?_⟩
    simpa only [mul_inv_cancel,one_mul] using weightedWalk_right_mul e (p.reverse (weightedStep_symm e)) g⁻¹
  · intro r s g h hg hh
    obtain ⟨a,ha,p⟩ := (hB r g).mp hg
    obtain ⟨b,hb,q⟩ := (hB s h).mp hh
    refine (hB _ _).mpr ⟨a+b,Nat.add_le_add ha hb,p.append ?_⟩
    simpa only [one_mul] using weightedWalk_right_mul e q g
  · intro r s hrs g hg
    obtain ⟨a,ha,h⟩ := (hB r g).mp hg
    exact (hB s g).mpr ⟨a,ha.trans hrs,h⟩
  · intro g hg
    obtain ⟨a,ha,p⟩ := (hB 0 g).mp hg
    exact (p.zero_eq (by rintro t x y ⟨i,hi,_⟩; omega) (by omega)).symm
  · intro g
    obtain ⟨i,rfl⟩ := he g
    refine ⟨i+1,(hB _ _).mpr ⟨i+1,le_rfl,CostWalk.single ?_⟩⟩
    exact ⟨i,rfl,Or.inl (mul_one _)⟩

def ofCountable (G : Type*) [Group G] [Countable G] : ProperGroupBalls G :=
  ofEnumeration (Classical.choose (exists_surjective_nat G))
    (Classical.choose_spec (exists_surjective_nat G))

variable {X : Type*} [MulAction G X] [MeasurableSpace X] [MeasurableEq X] [Countable G]

/-- A proper length induces uniformly finite Borel orbit balls for any Borel action. -/
def toBorelNear (B : ProperGroupBalls G) (hact : BorelAction G X) : BorelNear X := by
  classical
  let e := Classical.choose (exists_surjective_nat G)
  have he := Classical.choose_spec (exists_surjective_nat G)
  refine {
    near := fun r x y => ∃ g ∈ B.ball r, g • x = y
    refl := fun r x => ⟨1,B.one_mem r,one_smul _ _⟩
    symm := ?_
    mono := by
      rintro r s hrs x y ⟨g,hg,hxy⟩
      exact ⟨g,B.mono hrs hg,hxy⟩
    triangle := ?_
    zero := ?_
    borel := ?_
    moves := fun i x => e i • x
    measurable_moves := fun i => hact (e i)
    moves_cover := ?_
    uniformly_finite := ?_ }
  · rintro r x y ⟨g,hg,rfl⟩
    exact ⟨g⁻¹,B.inv_mem hg,inv_smul_smul _ _⟩
  · rintro r s x y z ⟨g,hg,rfl⟩ ⟨h,hh,rfl⟩
    exact ⟨h*g,B.mul_mem hg hh,mul_smul _ _ _⟩
  · rintro x y ⟨g,hg,rfl⟩
    rw [B.zero hg, one_smul]
  · intro r
    have heq : {p : X×X | ∃ g ∈ B.ball r, g • p.1 = p.2} =
        ⋃ g : (B.ball r : Set G), {p : X×X | g.val • p.1 = p.2} := by
      ext p
      simp only [mem_setOf_eq,mem_iUnion]
      exact ⟨fun ⟨g,hg,h⟩ => ⟨⟨g,hg⟩,h⟩,fun ⟨g,h⟩ => ⟨g,g.property,h⟩⟩
    rw [heq]
    exact MeasurableSet.iUnion fun g => measurableSet_eq_fun
      ((hact g.val).comp measurable_fst) measurable_snd
  · rintro r x y ⟨g,_,hxy⟩
    obtain ⟨i,hig⟩ := he g
    refine ⟨i,?_⟩
    change e i • x = y
    change e i = g at hig
    rw [hig,hxy]
  · refine fun r => ⟨(B.ball r).card,fun x => ⟨(B.ball r).image (fun g => g • x),
      Finset.card_image_le,?_⟩⟩
    rintro y ⟨g,hg,rfl⟩
    exact Finset.mem_image_of_mem _ hg

theorem toBorelNear_iff (B : ProperGroupBalls G) (hact : BorelAction G X) (r : ℕ) (x y : X) :
    (B.toBorelNear hact).near r x y ↔ ∃ g ∈ B.ball r, g • x = y := Iff.rfl

theorem near_smul (B : ProperGroupBalls G) (hact : BorelAction G X)
    {r : ℕ} {g : G} (hg : g ∈ B.ball r) (x : X) :
    (B.toBorelNear hact).near r x (g • x) := ⟨g,hg,rfl⟩

theorem toBorelNear_iff_orbit (B : ProperGroupBalls G) (hact : BorelAction G X) (x y : X) :
    (∃ r, (B.toBorelNear hact).near r x y) ↔ orbitRel G x y := by
  constructor
  · rintro ⟨r,g,_,he⟩
    exact ⟨g,he⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨r,hg⟩ := B.exhaustive g
    exact ⟨r,B.near_smul hact hg x⟩

theorem wordNear_controlled (B : ProperGroupBalls G) (A : Finset G) (hA : SymmetricMoves A)
    (hact : BorelAction G X) (r : ℕ) : ∃ s, ∀ ⦃x y : X⦄,
    (wordNear A hA hact).near r x y → (B.toBorelNear hact).near s x y := by
  obtain ⟨s,hs⟩ := B.finite_subset (wordBall A r)
  refine ⟨s,?_⟩
  rintro x y ⟨a,ha,p⟩
  obtain ⟨g,hg,rfl⟩ := p.exists_wordBall A (by rintro t u v ⟨rfl,d,hd,he⟩; exact ⟨by omega,d,hd,he⟩)
  exact B.near_smul hact (hs g (wordBall_mono A ha hg)) x

theorem wordNear_smul_bounded (A : Finset G) (hA : SymmetricMoves A)
    (hgen : Subgroup.closure (A : Set G) = ⊤) (hact : BorelAction G X) (g : G) :
    ∃ r, ∀ x : X, (wordNear A hA hact).near r x (g • x) := by
  let D := wordNear A hA hact
  have hg : g ∈ Subgroup.closure (A : Set G) := hgen.symm ▸ (Subgroup.mem_top g)
  apply Subgroup.closure_induction (p := fun g _ => ∃ r, ∀ x : X, D.near r x (g • x)) _ _ _ _ hg
  · exact fun a ha => ⟨1, wordNear_generator A hA hact ha⟩
  · exact ⟨0,fun x => by simpa only [one_smul] using D.refl 0 x⟩
  · rintro g h _ _ ⟨r,hr⟩ ⟨s,hs⟩
    exact ⟨s+r,fun x => by simpa only [mul_smul] using D.triangle (hs x) (hr (h • x))⟩
  · rintro g _ ⟨r,hr⟩
    exact ⟨r,fun x => by simpa only [smul_inv_smul] using D.symm r (hr (g⁻¹ • x))⟩

theorem controlled_by_wordNear (B : ProperGroupBalls G) (A : Finset G) (hA : SymmetricMoves A)
    (hgen : Subgroup.closure (A : Set G) = ⊤) (hact : BorelAction G X) (r : ℕ) : ∃ s, ∀ ⦃x y : X⦄,
    (B.toBorelNear hact).near r x y → (wordNear A hA hact).near s x y := by
  classical
  choose k hk using wordNear_smul_bounded A hA hgen hact
  refine ⟨(B.ball r).sup k,?_⟩
  rintro x y ⟨g,hg,rfl⟩
  exact (wordNear A hA hact).mono (Finset.le_sup hg) (hk g x)

end ProperGroupBalls

variable {X : Type*} [MeasurableSpace X]

theorem asdim_of_two_near_comparisons (D B : BorelNear X) {A : Set X} {d : ℕ}
    (hDB : ∀ r : ℕ, ∃ s : ℕ, ∀ ⦃x y⦄, D.near r x y → B.near s x y)
    (hBD : ∀ s : ℕ, ∃ r : ℕ, ∀ ⦃x y⦄, B.near s x y → D.near r x y)
    (hA : BorelAsdimLE B d A) : BorelAsdimLE D d A := by
  intro r
  obtain ⟨s,hs⟩ := hDB r
  obtain ⟨U,R,hUA,hUm,hUcov,hUbound⟩ := hA s
  obtain ⟨R',hR'⟩ := hBD R
  refine ⟨U,R',hUA,hUm,hUcov,fun i x y hxy => ?_⟩
  exact hR' (hUbound i (D.comp_mono_near B (fun _ _ _ _ h => hs h) hxy))

theorem coreExhaustion_of_two_near_comparisons (D B : BorelNear X)
    (hDB : ∀ r : ℕ, ∃ s : ℕ, ∀ ⦃x y⦄, D.near r x y → B.near s x y)
    (hBD : ∀ s : ℕ, ∃ r : ℕ, ∀ ⦃x y⦄, B.near s x y → D.near r x y)
    (hB : HasCoreExhaustion B) : HasCoreExhaustion D := by
  obtain ⟨d,K,hKm,hK,hKcov,hKd⟩ := hB
  exact ⟨d,K,hKm,hK,hKcov,fun j => asdim_of_two_near_comparisons D B hDB hBD (hKd j)⟩

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.ProperOrbitMetrics

-- BEGIN COMPLETE MODULE HirschProof.FiniteIndexActions
section
                                   
                                     
                                     

set_option autoImplicit false
noncomputable section

namespace LocalHirschHyperfinite

open Set

variable {G : Type*} [Group G]

abbrev RightCosets (H : Subgroup G) := Quotient (QuotientGroup.rightRel H)

private def rightCosetMap (H : Subgroup G) (g : G) : RightCosets H → RightCosets H :=
  Quotient.map (fun x => x*g) (by
    intro x y h
    apply QuotientGroup.rightRel_apply.mpr
    have hm := QuotientGroup.rightRel_apply.mp h
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hm)

private theorem rightCosetMap_mk (H : Subgroup G) (g x : G) :
    rightCosetMap H g (Quotient.mk _ x) = Quotient.mk _ (x*g) := rfl

/-- Right multiplication permutes right cosets. -/
def rightCosetPermutation (H : Subgroup G) (g : G) : Equiv.Perm (RightCosets H) where
  toFun := rightCosetMap H g
  invFun := rightCosetMap H g⁻¹
  left_inv := by
    intro i
    induction i using Quotient.inductionOn with
    | h x => simp only [rightCosetMap_mk, mul_inv_cancel_right]
  right_inv := by
    intro i
    induction i using Quotient.inductionOn with
    | h x => simp only [rightCosetMap_mk, inv_mul_cancel_right]

def rightCosetRepresentative (H : Subgroup G) (i : RightCosets H) : G := by
  classical
  exact if i = Quotient.mk _ (1 : G) then 1 else i.out

@[simp] theorem rightCosetRepresentative_one (H : Subgroup G) :
    rightCosetRepresentative H (Quotient.mk _ (1 : G)) = 1 := by
  classical
  simp [rightCosetRepresentative]

theorem rightCosetRepresentative_spec (H : Subgroup G) (i : RightCosets H) :
    Quotient.mk (QuotientGroup.rightRel H) (rightCosetRepresentative H i) = i := by
  classical
  unfold rightCosetRepresentative
  split
  · exact ‹i = Quotient.mk _ (1 : G)›.symm
  · exact Quotient.out_eq i

/-- The correction in `H` when a translated orbit point changes its right-coset label. -/
def rightCosetCorrection (H : Subgroup G) (g : G) (i : RightCosets H) : H := by
  let j := rightCosetPermutation H g⁻¹ i
  refine ⟨rightCosetRepresentative H j * g * (rightCosetRepresentative H i)⁻¹,?_⟩
  have hq : Quotient.mk (QuotientGroup.rightRel H) (rightCosetRepresentative H j * g) = i := by
    rw [← rightCosetMap_mk, rightCosetRepresentative_spec]
    exact (rightCosetPermutation H g).right_inv i
  exact QuotientGroup.rightRel_apply.mp
    (Quotient.exact ((rightCosetRepresentative_spec H i).trans hq.symm))

variable {X : Type*} [MulAction G X]

theorem rightCosetCorrection_smul (H : Subgroup G) (g : G) (i : RightCosets H) (x : X) :
    rightCosetCorrection H g i • (rightCosetRepresentative H i • x) =
      rightCosetRepresentative H (rightCosetPermutation H g⁻¹ i) • (g • x) := by
  change (rightCosetRepresentative H (rightCosetPermutation H g⁻¹ i) * g *
      (rightCosetRepresentative H i)⁻¹) • (rightCosetRepresentative H i • x) = _
  rw [mul_smul, inv_smul_smul, mul_smul]

/-- A point belongs to the induced core when all its coset representatives land in `K`. -/
def finiteCosetCore (H : Subgroup G) (K : Set X) : Set X :=
  {x | ∀ i : RightCosets H, rightCosetRepresentative H i • x ∈ K}

theorem finiteCosetCore_mono (H : Subgroup G) : Monotone (finiteCosetCore H : Set X → Set X) :=
  fun _ _ h _ hx i => h (hx i)

variable [MeasurableSpace X] [MeasurableEq X] [Countable G]

/-- Orbit balls of a subgroup are uniformly controlled by the ambient proper balls. -/
theorem subgroupNear_controlled (H : Subgroup G) (BG : ProperGroupBalls G) (BH : ProperGroupBalls H)
    (hact : BorelAction G X) (s : ℕ) : ∃ r : ℕ, ∀ ⦃x y : X⦄,
    (BH.toBorelNear (fun h => hact h.val)).near s x y → (BG.toBorelNear hact).near r x y := by
  classical
  let F := (BH.ball s).image (fun g : H => g.val)
  obtain ⟨r,hr⟩ := BG.finite_subset F
  refine ⟨r,?_⟩
  rintro x y ⟨h,hh,hxy⟩
  exact ⟨h.val,hr _ (Finset.mem_image_of_mem _ hh),hxy⟩

variable (H : Subgroup G) [H.FiniteIndex]

theorem measurableSet_finiteCosetCore (hact : BorelAction G X) {K : Set X}
    (hK : MeasurableSet K) : MeasurableSet (finiteCosetCore H K) := by
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have heq : finiteCosetCore H K = ⋂ i : RightCosets H, (fun x => rightCosetRepresentative H i • x) ⁻¹' K := by
    ext x
    simp only [finiteCosetCore,mem_setOf_eq,mem_iInter,mem_preimage]
  rw [heq]
  exact MeasurableSet.iInter fun i => hK.preimage (hact (rightCosetRepresentative H i))

/-- The explicit finite-index dimension bound for a core and all its right-coset translates. -/
theorem asdim_finiteIndex_action (BG : ProperGroupBalls G) (BH : ProperGroupBalls H)
    (hact : BorelAction G X) {K : Set X} (hK : MeasurableSet K) (d : ℕ)
    (hcores : BorelAsdimLE (BH.toBorelNear (fun h => hact h.val)) d K) :
    BorelAsdimLE (BG.toBorelNear hact) ((d+1)^H.index-1) (finiteCosetCore H K) := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  let f (i : RightCosets H) (x : X) := rightCosetRepresentative H i • x
  let D := BG.toBorelNear hact
  let B := BH.toBorelNear (fun h => hact h.val)
  let A := finiteCosetCore H K
  have hcard : Fintype.card (RightCosets H) = H.index := by
    rw [QuotientGroup.card_quotient_rightRel,H.index_eq_card,Nat.card_eq_fintype_card]
  have hid : ∃ i, f i = id := by
    refine ⟨Quotient.mk _ 1,funext fun x => ?_⟩
    simp [f]
  let F : Finset G := Finset.univ.image (rightCosetRepresentative H)
  obtain ⟨b,hb⟩ := BG.finite_subset F
  have hshort (i : RightCosets H) (x : X) : D.near b x (f i x) :=
    BG.near_smul hact (hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) x
  have hmatch (r : ℕ) : ∃ s : ℕ, ∀ ⦃x y⦄, x ∈ A → y ∈ A → D.near r x y →
      ∃ p : Equiv.Perm (RightCosets H), ∀ i, B.near s (f i x) (f (p i) y) := by
    let F' : Finset H := (BG.ball r).biUnion fun g => Finset.univ.image (rightCosetCorrection H g)
    obtain ⟨s,hs⟩ := BH.finite_subset F'
    refine ⟨s,?_⟩
    rintro x y _ _ ⟨g,hg,rfl⟩
    refine ⟨rightCosetPermutation H g⁻¹,fun i => ⟨rightCosetCorrection H g i,?_,?_⟩⟩
    · exact hs _ (Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    · exact rightCosetCorrection_smul H g i x
  have hcompare (s : ℕ) : ∃ r : ℕ, ∀ ⦃x y⦄, x ∈ K → y ∈ K → B.near s x y → D.near r x y := by
    obtain ⟨r,hr⟩ := subgroupNear_controlled H BG BH hact s
    exact ⟨r,fun _ _ _ _ h => hr h⟩
  rw [← hcard]
  exact asdim_of_finite_coset_moves D B f (fun i => hact (rightCosetRepresentative H i)) hid b hshort
    (measurableSet_finiteCosetCore H hact hK) (fun i _ hx => hx i) hmatch hcompare d hcores

theorem coreExhaustion_finiteIndex_action (BG : ProperGroupBalls G) (BH : ProperGroupBalls H)
    (hact : BorelAction G X)
    (hcores : HasCoreExhaustion (BH.toBorelNear (fun h => hact h.val))) :
    HasCoreExhaustion (BG.toBorelNear hact) := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨d,K,hKm,hK,hKcov,hKd⟩ := hcores
  refine ⟨(d+1)^H.index-1,fun n => finiteCosetCore H (K n),
    (finiteCosetCore_mono H).comp hKm, fun n => measurableSet_finiteCosetCore H hact (hK n),?_,
    fun n => asdim_finiteIndex_action H BG BH hact (hK n) d (hKd n)⟩
  intro x
  choose n hn using fun i : RightCosets H => hKcov (rightCosetRepresentative H i • x)
  exact ⟨Finset.univ.sup n,fun i => hKm (Finset.le_sup (Finset.mem_univ i)) (hn i)⟩

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.FiniteIndexActions

-- BEGIN COMPLETE MODULE HirschProof.LocalAssembly
section
                                 
                                     
                                   

set_option autoImplicit false

namespace LocalHirschHyperfinite

universe u v

variable {G : Type u} {X : Type v} [Group G] [Countable G] [MulAction G X]
  [MeasurableSpace X] [StandardBorelSpace X]

/-- The finite-index and countable-stage assembly for the local Hirsch theorem.
It suffices to produce controlled cores for individual finitely generated solvable groups. -/
theorem hyperfinite_of_solvable_stage_cores (hG : IsLocallyVirtuallySolvableFiniteHirsch G)
    (hact : BorelAction G X)
    (hcore : ∀ (J : Type u) [Group J] [Countable J] [Group.FG J] [MulAction J X]
      (BJ : ProperGroupBalls J) (hJ : BorelAction J X), IsSolvableFiniteHirsch J →
      HasCoreExhaustion (BJ.toBorelNear hJ)) :
    IsHyperfinite (orbitRel G : X → X → Prop) := by
  apply hyperfinite_of_finitely_generated_cores hact
  intro H A hA hgen
  have hf : H.FG := by
    apply (Group.fg_iff_subgroup_fg H).1
    exact ⟨⟨A,hgen⟩⟩
  letI : Group.FG H := (Group.fg_iff_subgroup_fg H).2 hf
  obtain ⟨J,hJindex,hJhirsch⟩ := hG H hf
  letI : J.FiniteIndex := hJindex
  let BH := ProperGroupBalls.ofCountable H
  let BJ := ProperGroupBalls.ofCountable J
  have hHact : BorelAction H X := fun h => hact h.val
  have hJact : BorelAction J X := fun j => hHact j.val
  have hJcore := hcore J BJ hJact hJhirsch
  have hHcore := coreExhaustion_finiteIndex_action J BH BJ hHact hJcore
  exact coreExhaustion_of_two_near_comparisons (wordNear A hA hHact) (BH.toBorelNear hHact)
    (BH.wordNear_controlled A hA hHact) (BH.controlled_by_wordNear A hA hgen hHact) hHcore

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.LocalAssembly

-- BEGIN COMPLETE MODULE HirschProof.LocallyFiniteRadical
section
                                          
                                   
                                              
                                               

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

def IsLocallyFiniteGroup (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → Finite H

namespace IsLocallyFiniteGroup

variable {G H : Type*} [Group G] [Group H]

theorem finite_of_fg [Group.FG G] (h : IsLocallyFiniteGroup G) : Finite G := by
  letI : Finite (⊤ : Subgroup G) := h ⊤ Group.FG.out
  exact Finite.of_injective (fun g : G => (⟨g,Subgroup.mem_top g⟩ : (⊤ : Subgroup G)))
    (fun _ _ h' => congrArg Subtype.val h')

theorem fg_map (f : G →* H) (L : Subgroup G) (hL : L.FG) : (L.map f).FG := by
  rcases (Subgroup.fg_iff L).1 hL with ⟨s,rfl,hs⟩
  exact (Subgroup.fg_iff _).2 ⟨f '' s,(f.map_closure s).symm,hs.image _⟩

theorem of_injective (f : G →* H) (hf : Function.Injective f)
    (h : IsLocallyFiniteGroup H) : IsLocallyFiniteGroup G := by
  intro L hL
  letI : Finite (L.map f) := h _ (fg_map f L hL)
  exact Finite.of_injective (L.equivMapOfInjective f hf) (L.equivMapOfInjective f hf).injective

theorem subgroup (h : IsLocallyFiniteGroup G) (L : Subgroup G) :
    IsLocallyFiniteGroup L :=
  of_injective L.subtype L.subtype_injective h

theorem of_surjective (f : G →* H) (hf : Function.Surjective f)
    (h : IsLocallyFiniteGroup G) : IsLocallyFiniteGroup H := by
  classical
  intro L hL
  obtain ⟨s,hs,hsf⟩ := (Subgroup.fg_iff L).mp hL
  let j : H → G := fun x => Classical.choose (hf x)
  have hj (x : H) : f (j x) = x := Classical.choose_spec (hf x)
  let K := Subgroup.closure (j '' s)
  have hK : K.FG := (Subgroup.fg_iff K).2 ⟨_,rfl,hsf.image _⟩
  have himg : f '' (j '' s) = s := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa only [hj] using hz
    · intro hx
      exact ⟨j x,⟨x,hx,rfl⟩,hj x⟩
  have hKL : K.map f = L := by
    change (Subgroup.closure (j '' s)).map f = L
    rw [f.map_closure,himg,hs]
  letI : Finite K := h K hK
  have hKMap : Finite (K.map f) := Finite.of_surjective
    (fun x : K => (⟨f x.val,⟨x.val,x.property,rfl⟩⟩ : K.map f)) (by
      rintro ⟨y,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩)
  exact hKL ▸ hKMap

theorem image (L : Subgroup G) (h : IsLocallyFiniteGroup L) (f : G →* H) :
    IsLocallyFiniteGroup (L.map f) := by
  let φ : L →* L.map f := {
    toFun := fun x => ⟨f x.val,⟨x.val,x.property,rfl⟩⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }
  apply of_surjective φ _ h
  rintro ⟨y,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

/-- Locally finite groups are closed under extensions. -/
theorem extension (f : G →* H) (hk : IsLocallyFiniteGroup f.ker)
    (hr : IsLocallyFiniteGroup H) : IsLocallyFiniteGroup G := by
  intro L hL
  letI : Group.FG L := (Group.fg_iff_subgroup_fg L).2 hL
  let φ := f.comp L.subtype
  have hRange : φ.range = L.map f := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  letI : Finite φ.range := hRange.symm ▸ hr _ (fg_map f L hL)
  letI : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  letI : Group.FG φ.ker := φ.ker.fg_of_index_ne_zero
  let ι : φ.ker →* f.ker := {
    toFun := fun g => ⟨g.val.val,g.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun v : f.ker => v.val) h))
  exact (φ.finite_iff_finite_ker_range).2 ⟨finite_of_fg (of_injective ι hι hk),inferInstance⟩

theorem of_finite [Finite G] : IsLocallyFiniteGroup G :=
  fun _ _ => inferInstance

theorem sup_normal {L K : Subgroup G} [L.Normal] [K.Normal]
    (hL : IsLocallyFiniteGroup L) (hK : IsLocallyFiniteGroup K) :
    IsLocallyFiniteGroup (L ⊔ K : Subgroup G) := by
  let q : G →* G ⧸ L := QuotientGroup.mk' L
  let f : (L ⊔ K : Subgroup G) →* (L ⊔ K : Subgroup G).map q := {
    toFun := fun x => ⟨q x.val,⟨x.val,x.property,rfl⟩⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun _ _ => Subtype.ext (map_mul q _ _) }
  apply extension f
  · let ι : f.ker →* L := {
      toFun := fun x => ⟨x.val.val, (QuotientGroup.eq_one_iff _).1
        (congrArg Subtype.val x.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    apply of_injective ι _ hL
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun v : L => v.val) hxy))
  · have hq : L.map q = ⊥ := (L.map_eq_bot_iff).2 (by
      change L ≤ (QuotientGroup.mk' L).ker
      simp)
    rw [Subgroup.map_sup,hq,bot_sup_eq]
    exact image K hK q

end IsLocallyFiniteGroup

section Radical
variable (G : Type*) [Group G]

def normalLocallyFiniteSubgroups : Set (Subgroup G) :=
  {L | L.Normal ∧ IsLocallyFiniteGroup L}

theorem nonempty_normalLocallyFiniteSubgroups : (normalLocallyFiniteSubgroups G).Nonempty :=
  ⟨⊥,inferInstance,IsLocallyFiniteGroup.of_finite⟩

theorem directed_normalLocallyFiniteSubgroups :
    DirectedOn (· ≤ ·) (normalLocallyFiniteSubgroups G) := by
  rintro L ⟨hLn,hL⟩ K ⟨hKn,hK⟩
  letI := hLn
  letI := hKn
  exact ⟨L ⊔ K,⟨inferInstance,IsLocallyFiniteGroup.sup_normal hL hK⟩,le_sup_left,le_sup_right⟩

def locallyFiniteRadical : Subgroup G := sSup (normalLocallyFiniteSubgroups G)

theorem mem_locallyFiniteRadical {g : G} :
    g ∈ locallyFiniteRadical G ↔ ∃ L ∈ normalLocallyFiniteSubgroups G, g ∈ L :=
  Subgroup.mem_sSup_of_directedOn (nonempty_normalLocallyFiniteSubgroups G)
    (directed_normalLocallyFiniteSubgroups G)

instance locallyFiniteRadical_normal : (locallyFiniteRadical G).Normal := by
  constructor
  intro g hg v
  obtain ⟨L,hL,hgL⟩ := (mem_locallyFiniteRadical G).mp hg
  exact (mem_locallyFiniteRadical G).mpr ⟨L,hL,hL.1.conj_mem g hgL v⟩

theorem le_locallyFiniteRadical {L : Subgroup G} (hn : L.Normal)
    (h : IsLocallyFiniteGroup L) : L ≤ locallyFiniteRadical G :=
  le_sSup ⟨hn,h⟩

theorem locallyFiniteRadical_locallyFinite : IsLocallyFiniteGroup (locallyFiniteRadical G) := by
  classical
  let N := locallyFiniteRadical G
  intro H hH
  obtain ⟨s,rfl⟩ := hH
  have hB : ∃ L ∈ normalLocallyFiniteSubgroups G, ∀ x ∈ s, (x : N).val ∈ L := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨L,hL⟩ := nonempty_normalLocallyFiniteSubgroups G
      exact ⟨L,hL,by simp⟩
    | @insert a t hat ih =>
      obtain ⟨L,hL,hxL⟩ := ih
      obtain ⟨K,hK,haK⟩ := (mem_locallyFiniteRadical G).1 a.property
      obtain ⟨P,hP,hLP,hKP⟩ := directed_normalLocallyFiniteSubgroups G L hL K hK
      refine ⟨P,hP,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact hKP haK
      · exact hLP (hxL x hx)
  obtain ⟨L,hL,hs⟩ := hB
  have hsub : Subgroup.closure (s : Set N) ≤ L.comap N.subtype :=
    (Subgroup.closure_le _).2 (fun x hx => hs x hx)
  let ι : Subgroup.closure (s : Set N) →* L := {
    toFun := fun x => ⟨x.val.val,hsub x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun v : L => v.val) hxy))
  letI : Group.FG (Subgroup.closure (s : Set N)) :=
    (Group.fg_iff_subgroup_fg _).2 ⟨s,rfl⟩
  exact IsLocallyFiniteGroup.finite_of_fg (IsLocallyFiniteGroup.of_injective ι hι hL.2)

theorem normal_locallyFinite_in_radical_quotient_eq_bot
    (L : Subgroup (G ⧸ locallyFiniteRadical G)) (hn : L.Normal)
    (hL : IsLocallyFiniteGroup L) : L = ⊥ := by
  let R := locallyFiniteRadical G
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  let K := L.comap π
  let f : K →* L := {
    toFun := fun x => ⟨π x.val,x.property⟩
    map_one' := Subtype.ext (map_one π)
    map_mul' := fun _ _ => Subtype.ext (map_mul π _ _) }
  let ι : f.ker →* R := {
    toFun := fun x => ⟨x.val.val, (QuotientGroup.eq_one_iff _).1
      (congrArg (fun v : L => v.val) x.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro x y e
    exact Subtype.ext (Subtype.ext (congrArg (fun v : R => v.val) e))
  have hf : IsLocallyFiniteGroup K := IsLocallyFiniteGroup.extension f
    (IsLocallyFiniteGroup.of_injective ι hι (locallyFiniteRadical_locallyFinite G)) hL
  have hKR : K ≤ R := le_locallyFiniteRadical G (hn.comap π) hf
  apply le_antisymm _ bot_le
  intro y hy
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective R y
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff _).2 (hKR hy))

end Radical

theorem map_commutator_derivedSeries {G : Type*} [Group G] (n : ℕ) :
    (derivedSeries (commutator G) n).map (commutator G).subtype = derivedSeries G (n+1) := by
  induction n with
  | zero =>
    rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype, derivedSeries_one]
  | succ n ih =>
    rw [derivedSeries_succ,Subgroup.map_commutator,ih]
    exact (derivedSeries_succ G (n+1)).symm

/-- A solvable torsion group becomes finite when finitely generated. -/
theorem finite_of_fg_torsion_solvable (G : Type*) [Group G] [Group.FG G]
    [IsSolvable G] (hT : Monoid.IsTorsion G) : Finite G := by
  have general (n : ℕ) : ∀ (A : Type _) [Group A] [Group.FG A],
      derivedSeries A n = ⊥ → Monoid.IsTorsion A → Finite A := by
    induction n with
    | zero =>
      intro A _ _ hA _
      haveI : Subsingleton A := ⟨fun u v => by
        have hbot : (⊤ : Subgroup A) = ⊥ := hA
        have h (x : A) : x = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top x)
        rw [h u,h v]⟩
      infer_instance
    | succ n ih =>
      intro A _ _ hA hT'
      let f : A →* Abelianization A := Abelianization.of
      have hfs : Function.Surjective f := QuotientGroup.mk'_surjective (commutator A)
      letI : Group.FG (Abelianization A) := Group.fg_of_surjective hfs
      letI : Finite (Abelianization A) := CommGroup.finite_of_fg_torsion _
        (IsTorsion.of_surjective hfs hT')
      letI : Finite f.range := Finite.of_injective (fun v : f.range => v.val) Subtype.val_injective
      letI : f.ker.FiniteIndex := inferInstance
      letI : Group.FG f.ker := inferInstance
      have hfK : f.ker = commutator A := Abelianization.ker_of A
      letI : Group.FG (commutator A) := hfK ▸ (inferInstance : Group.FG f.ker)
      have hC : derivedSeries (commutator A) n = ⊥ := by
        apply Subgroup.map_subtype_inj.mp
        rw [map_commutator_derivedSeries,Subgroup.map_bot,hA]
      have hfin : Finite (commutator A) := ih _ hC (IsTorsion.subgroup hT' _)
      exact f.finite_iff_finite_ker_range.2 ⟨hfK.symm ▸ hfin,inferInstance⟩
  obtain ⟨n,hn⟩ := IsSolvable.solvable (G := G)
  exact general n G hn hT

theorem locallyFinite_of_torsion_solvable (G : Type*) [Group G] [IsSolvable G]
    (hT : Monoid.IsTorsion G) : IsLocallyFiniteGroup G := by
  intro H hH
  letI : Group.FG H := (Group.fg_iff_subgroup_fg H).2 hH
  exact finite_of_fg_torsion_solvable H (IsTorsion.subgroup hT H)

theorem normal_torsion_in_radical_quotient_eq_bot (G : Type*) [Group G] [IsSolvable G]
    (H : Subgroup (G ⧸ locallyFiniteRadical G)) (hn : H.Normal)
    (hT : Monoid.IsTorsion H) : H = ⊥ :=
  normal_locallyFinite_in_radical_quotient_eq_bot G H hn (locallyFinite_of_torsion_solvable H hT)

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.LocallyFiniteRadical

-- BEGIN COMPLETE MODULE HirschProof.NilpotentLeadingTerms
section
                                       
                                    
                                     

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

/-- Left associated commutators of weight n+1 in the specified alphabet. -/
def leadingWords (S : Set G) : ℕ → Set G
  | 0 => S
  | n+1 => Set.image2 (fun a b : G => ⁅a,b⁆) (leadingWords S n) S

theorem finite_leadingWords {S : Set G} (hS : S.Finite) (n : ℕ) :
    (leadingWords S n).Finite := by
  induction n with
  | zero => exact hS
  | succ n ih => exact ih.image2 _ hS

theorem leadingWords_subset_lowerCentral (S : Set G) (n : ℕ) :
    leadingWords S n ⊆ Subgroup.lowerCentralSeries G n := by
  induction n with
  | zero => exact subset_univ _
  | succ n ih =>
    rintro _ ⟨a,ha,b,hb,rfl⟩
    exact commutator_mem_commutator (ih ha) (mem_top b)

abbrev LowerQuot (G : Type*) [Group G] (n : ℕ) :=
  G ⧸ Subgroup.lowerCentralSeries G (n+1)

abbrev lowerQuot (G : Type*) [Group G] (n : ℕ) : G →* LowerQuot G n :=
  QuotientGroup.mk' _

theorem lowerQuot_eq_one {n : ℕ} {a : G}
    (ha : a ∈ Subgroup.lowerCentralSeries G (n+1)) : lowerQuot G n a = 1 :=
  (QuotientGroup.eq_one_iff a).2 ha

theorem lowerQuot_mem_center {n : ℕ} {g : G} (hg : g ∈ Subgroup.lowerCentralSeries G n) :
    lowerQuot G n g ∈ Subgroup.center (LowerQuot G n) := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.lowerCentralSeries G (n+1)) x
  have hc : ⁅g,a⁆ ∈ Subgroup.lowerCentralSeries G (n+1) :=
    commutator_mem_commutator hg (mem_top a)
  have hh := lowerQuot_eq_one hc
  rw [map_commutatorElement] at hh
  exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm

theorem quotient_commutator_central {n : ℕ} {a : G}
    (ha : a ∈ Subgroup.lowerCentralSeries G n) (b : G) :
    ⁅lowerQuot G (n+1) a,lowerQuot G (n+1) b⁆ ∈ Subgroup.center (LowerQuot G (n+1)) := by
  rw [← map_commutatorElement]
  exact lowerQuot_mem_center (commutator_mem_commutator ha (mem_top b))

private theorem conj_eq_of_mem_center {J : Type*} [Group J] {c : J}
    (hc : c ∈ Subgroup.center J) (a : J) : a*c*a⁻¹=c := by
  rw [Subgroup.mem_center_iff] at hc
  rw [hc a,mul_assoc,mul_inv_cancel,mul_one]

/-- Commuting against the n-th lower-central term is a homomorphism in the
right variable modulo the second following term. -/
def gradedBracketRight (n : ℕ) (a : Subgroup.lowerCentralSeries G n) :
    G →* LowerQuot G (n+1) where
  toFun b := lowerQuot G (n+1) ⁅a.val,b⁆
  map_one' := by
    simp [map_commutatorElement]
  map_mul' b c := by
    simp only [map_commutatorElement,map_mul]
    have he := commutatorElement_mul_right_eq_mul_conj (lowerQuot G (n+1) a.val)
      (lowerQuot G (n+1) b) (lowerQuot G (n+1) c)
    rw [he]
    rw [mul_assoc, mul_assoc, ← mul_assoc (lowerQuot G (n+1) b)]
    rw [conj_eq_of_mem_center (quotient_commutator_central a.property c)]

/-- The same leading commutator is a homomorphism in the left variable. -/
def gradedBracketLeft (n : ℕ) (b : G) :
    Subgroup.lowerCentralSeries G n →* LowerQuot G (n+1) where
  toFun a := lowerQuot G (n+1) ⁅a.val,b⁆
  map_one' := by
    simp [map_commutatorElement]
  map_mul' a c := by
    simp only [Subgroup.coe_mul,map_commutatorElement,map_mul]
    rw [commutatorElement_mul_left_eq_conj_mul,
      conj_eq_of_mem_center (quotient_commutator_central c.property b)]
    rw [Subgroup.mem_center_iff.mp (quotient_commutator_central c.property b)]

theorem gradedBracketLeft_kills_next {n : ℕ} (b : G) (a : Subgroup.lowerCentralSeries G n)
    (ha : a.val ∈ Subgroup.lowerCentralSeries G (n+1)) : gradedBracketLeft n b a = 1 :=
  lowerQuot_eq_one (commutator_mem_commutator ha (mem_top b))

theorem gradedBracketLeft_eq_of_lowerQuot_eq {n : ℕ} (b : G)
    (a c : Subgroup.lowerCentralSeries G n) (h : lowerQuot G n a.val = lowerQuot G n c.val) :
    gradedBracketLeft n b a = gradedBracketLeft n b c := by
  have hm : (a / c).val ∈ Subgroup.lowerCentralSeries G (n+1) :=
    (QuotientGroup.eq_iff_div_mem).1 h
  have hh := gradedBracketLeft_kills_next b (a/c) hm
  rw [map_div,div_eq_one] at hh
  exact hh

/-- The weight n+1 leading commutators generate the n-th lower-central
quotient whenever the alphabet generates the whole group. -/
theorem leadingWords_sup_next_lowerCentral (S : Set G) (hS : Subgroup.closure S = ⊤) (n : ℕ) :
    Subgroup.closure (leadingWords S n) ⊔ Subgroup.lowerCentralSeries G (n+1) = Subgroup.lowerCentralSeries G n := by
  induction n with
  | zero =>
    change Subgroup.closure S ⊔ Subgroup.lowerCentralSeries G 1 = ⊤
    rw [hS,top_sup_eq]
  | succ n ih =>
    let L := Subgroup.lowerCentralSeries G n
    let K := Subgroup.closure (leadingWords S (n+1))
    let q : G →* LowerQuot G (n+1) := lowerQuot G (n+1)
    have hKer : q.ker = Subgroup.lowerCentralSeries G (n+1+1) := QuotientGroup.ker_mk' _
    apply le_antisymm
    · exact sup_le ((closure_le _).2 (leadingWords_subset_lowerCentral S _))
        (Subgroup.lowerCentralSeries_antitone (Nat.le_succ _))
    · change Subgroup.lowerCentralSeries G (n+1) ≤ K ⊔ Subgroup.lowerCentralSeries G (n+1+1)
      rw [← hKer,← Subgroup.comap_map_eq,← Subgroup.map_le_iff_le_comap]
      change (Subgroup.closure {x : G | ∃ a ∈ L, ∃ b ∈ (⊤ : Subgroup G), ⁅a,b⁆=x}).map q ≤ K.map q
      rw [q.map_closure,Subgroup.closure_le]
      rintro _ ⟨z,⟨a,ha,b,_,rfl⟩,rfl⟩
      let f := gradedBracketLeft n b
      let V := ((K.map q).comap f).map L.subtype
      have hSg : leadingWords S n ∪ (Subgroup.lowerCentralSeries G (n+1) : Set G) ⊆ V := by
        intro x hx
        rcases hx with hx | hx
        · let x' : L := ⟨x,leadingWords_subset_lowerCentral S n hx⟩
          refine ⟨x',?_,rfl⟩
          change gradedBracketRight n x' b ∈ K.map q
          have hright : Subgroup.closure S ≤ (K.map q).comap (gradedBracketRight n x') := by
            apply (closure_le _).2
            intro y hy
            exact ⟨⁅x,y⁆,Subgroup.subset_closure ⟨x,hx,y,hy,rfl⟩,rfl⟩
          exact hright (hS.symm ▸ mem_top b)
        · let x' : L := ⟨x,Subgroup.lowerCentralSeries_antitone (Nat.le_succ _) hx⟩
          refine ⟨x',?_,rfl⟩
          change gradedBracketLeft n b x' ∈ K.map q
          rw [gradedBracketLeft_kills_next b x' hx]
          exact (K.map q).one_mem
      have hV : L ≤ V := by
        change Subgroup.lowerCentralSeries G n ≤ V
        rw [← ih]
        exact sup_le ((closure_le _).2 (fun x hx => hSg (Or.inl hx)))
          (fun _ hx => hSg (Or.inr hx))
      have hav := hV ha
      obtain ⟨a',ha',hae⟩ := hav
      change q ⁅a'.val,b⁆ ∈ K.map q at ha'
      exact hae ▸ ha'

/-- Raising each letter to the same power raises the leading commutator
to the appropriate product of powers in its central layer. -/
theorem exists_powered_leadingWord (S : Set G) (m n : ℕ) {g : G}
    (hg : g ∈ leadingWords S n) :
    ∃ h ∈ leadingWords ((fun x : G => x^m) '' S) n,
      lowerQuot G n h = (lowerQuot G n g)^(m^(n+1)) := by
  induction n generalizing g with
  | zero =>
    refine ⟨g^m,⟨g,hg,rfl⟩,?_⟩
    change lowerQuot G 0 (g^m) = (lowerQuot G 0 g)^(m^1)
    rw [pow_one m,map_pow]
  | succ n ih =>
    obtain ⟨a,ha,b,hb,rfl⟩ := hg
    obtain ⟨c,hc,he⟩ := ih ha
    let a' : Subgroup.lowerCentralSeries G n := ⟨a,leadingWords_subset_lowerCentral S n ha⟩
    let c' : Subgroup.lowerCentralSeries G n := ⟨c,leadingWords_subset_lowerCentral _ n hc⟩
    let k := m^(n+1)
    refine ⟨⁅c,b^m⁆,⟨c,hc,b^m,⟨b,hb,rfl⟩,rfl⟩,?_⟩
    have hq : lowerQuot G n c'.val = lowerQuot G n (a'^k).val := by
      change lowerQuot G n c = lowerQuot G n (a^k)
      rw [map_pow]
      exact he
    calc
      lowerQuot G (n+1) ⁅c,b^m⁆ = gradedBracketLeft n (b^m) c' := rfl
      _ = gradedBracketLeft n (b^m) (a'^k) := gradedBracketLeft_eq_of_lowerQuot_eq (b^m) _ _ hq
      _ = (gradedBracketLeft n (b^m) a')^k := map_pow _ _ _
      _ = (gradedBracketRight n a' (b^m))^k := rfl
      _ = ((gradedBracketRight n a' b)^m)^k := by rw [map_pow]
      _ = (lowerQuot G (n+1) ⁅a,b⁆)^(m^(n+1+1)) := by
        rw [← pow_mul, pow_succ m (n+1),Nat.mul_comm k m]
        rfl

theorem map_lowerCentralSeries_surjective {J : Type*} [Group J]
    (f : G →* J) (hf : Function.Surjective f) (n : ℕ) :
    (Subgroup.lowerCentralSeries G n).map f = Subgroup.lowerCentralSeries J n := by
  induction n with
  | zero => exact Subgroup.map_top_of_surjective f hf
  | succ n ih =>
    change ⁅Subgroup.lowerCentralSeries G n,(⊤ : Subgroup G)⁆.map f =
      ⁅Subgroup.lowerCentralSeries J n,(⊤ : Subgroup J)⁆
    rw [Subgroup.map_commutator,ih,Subgroup.map_top_of_surjective f hf]

theorem last_lowerCentral_le_center (n : ℕ)
    (h : Subgroup.lowerCentralSeries G (n+1) = ⊥) :
    Subgroup.lowerCentralSeries G n ≤ Subgroup.center G := by
  intro a ha
  apply Subgroup.mem_center_iff.mpr
  intro b
  have hc : ⁅a,b⁆ ∈ Subgroup.lowerCentralSeries G (n+1) :=
    commutator_mem_commutator ha (mem_top b)
  rw [h,Subgroup.mem_bot] at hc
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.NilpotentLeadingTerms

-- BEGIN COMPLETE MODULE HirschProof.Isolators
section
                                        

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set Subgroup

variable {G : Type*} [Group G]

private theorem relIndex_sup_of_central (H C : Subgroup G) (hc : C ≤ Subgroup.center G) :
    H.relIndex (H⊔C) = H.relIndex C := by
  have hN : C ≤ normalizer H := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxy := Subgroup.mem_center_iff.mp (hc hx) y
    have he : x*y*x⁻¹=y := by rw [← hxy,mul_assoc,mul_inv_cancel,mul_one]
    rw [he]
  rw [sup_comm H C]
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hN
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hN
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient C H hN).toEquiv.symm

/-- The index of a subgroup is the product of the indices within and
after quotienting by a central subgroup. -/
theorem index_eq_mul_of_central_extension (H C : Subgroup G) [C.Normal]
    (hc : C ≤ Subgroup.center G) :
    H.index = H.relIndex C * (H.map (QuotientGroup.mk' C)).index := by
  rw [← Subgroup.relIndex_mul_index (show H ≤ H⊔C from le_sup_left),relIndex_sup_of_central H C hc]
  rw [H.index_map (QuotientGroup.mk' C),QuotientGroup.ker_mk',
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective C),
    Subgroup.index_top,mul_one]

/-- Finite indices in a central subgroup and in its quotient multiply. -/
theorem finiteIndex_of_central_extension (H C : Subgroup G) [C.Normal]
    (hc : C ≤ Subgroup.center G) (hi : (H.subgroupOf C).FiniteIndex)
    (hq : (H.map (QuotientGroup.mk' C)).FiniteIndex) : H.FiniteIndex := by
  constructor
  rw [index_eq_mul_of_central_extension H C hc]
  exact Nat.mul_ne_zero hi.index_ne_zero hq.index_ne_zero

/-- Raising a leading commutator to the corresponding power puts it in
any subgroup containing the prescribed powers of the original letters. -/
theorem terminalLayer_power_mem {S : Set G} (H : Subgroup G) {m : ℕ}
    (hSp : ∀ x ∈ S, x^m ∈ H) (n : ℕ) (hn : Subgroup.lowerCentralSeries G (n+1) = ⊥)
    (x : G) (hx : x ∈ leadingWords S n) : x^(m^(n+1)) ∈ H := by
  obtain ⟨b,hb,hbe⟩ := exists_powered_leadingWord S m n hx
  have hbij : Function.Injective (lowerQuot G n) := by
    apply (lowerQuot G n).ker_eq_bot_iff.mp
    exact (QuotientGroup.ker_mk' _).trans hn
  have hab : b = x^(m^(n+1)) := hbij (hbe.trans ((lowerQuot G n).map_pow _ _).symm)
  have hbase : (fun g : G => g^m) '' S ⊆ H := by
    rintro _ ⟨a,ha,rfl⟩
    exact hSp a ha
  have hwords (i : ℕ) : leadingWords ((fun g : G => g^m) '' S) i ⊆ H := by
    induction i with
    | zero => exact hbase
    | succ i ih =>
      rintro _ ⟨u,hu,v,hv,rfl⟩
      unfold commutatorElement
      exact H.mul_mem (H.mul_mem (H.mul_mem (ih hu) (hbase hv)) (H.inv_mem (ih hu)))
        (H.inv_mem (hbase hv))
  exact hab ▸ hwords n hb

theorem terminalLayer_finiteIndex {S : Set G} (hSf : S.Finite)
    (hSg : closure S = ⊤) (H : Subgroup G) {m : ℕ} (hm : 0 < m)
    (hSp : ∀ x ∈ S, x^m ∈ H) (n : ℕ) (hn : Subgroup.lowerCentralSeries G (n+1) = ⊥) :
    (H.subgroupOf (Subgroup.lowerCentralSeries G n)).FiniteIndex := by
  let C := Subgroup.lowerCentralSeries G n
  let T := leadingWords S n
  have hTc : T ⊆ C := leadingWords_subset_lowerCentral S n
  have hTg : closure T = C := by
    have h := leadingWords_sup_next_lowerCentral S hSg n
    rw [hn,sup_bot_eq] at h
    exact h
  have hTf : T.Finite := finite_leadingWords hSf n
  letI : Group.FG C := (Group.fg_iff_subgroup_fg C).mpr
    ((Subgroup.fg_iff C).mpr ⟨T,hTg,hTf⟩)
  letI : CommGroup C := { (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp
      (last_lowerCentral_le_center n hn b.property) a.val) }
  let W := (powMonoidHom (α := C) (m^(n+1))).range
  letI : W.FiniteIndex := finiteIndex_range_powMonoidHom_of_fg C (pow_ne_zero _ hm.ne')
  let D := (H.subgroupOf C).comap (powMonoidHom (α := C) (m^(n+1)))
  have hDclosure : Subgroup.closure T ≤ D.map C.subtype := by
    apply (closure_le _).mpr
    intro x hx
    exact ⟨⟨x,hTc hx⟩,terminalLayer_power_mem H hSp n hn x hx,rfl⟩
  apply finiteIndex_of_le (H := W)
  rintro _ ⟨x,rfl⟩
  have hx : x.val ∈ D.map C.subtype := hDclosure (hTg.symm ▸ x.property)
  have hxD : x ∈ D := (Subgroup.mem_map_iff_mem C.subtype_injective).mp hx
  exact hxD

/-- In a finitely generated nilpotent group, a subgroup containing the
same positive power of each generator has finite index. -/
theorem finiteIndex_of_common_power_generators [Group.IsNilpotent G]
    {S : Set G} (hSf : S.Finite) (hSg : closure S = ⊤)
    (H : Subgroup G) {m : ℕ} (hm : 0 < m) (hSp : ∀ x ∈ S, x^m ∈ H) :
    H.FiniteIndex := by
  have gen (n : ℕ) : ∀ (J : Type _) [Group J], Subgroup.lowerCentralSeries J n = ⊥ →
      ∀ (T : Set J), T.Finite → closure T = ⊤ →
      ∀ K : Subgroup J, (∀ x ∈ T, x^m ∈ K) → K.FiniteIndex := by
    induction n with
    | zero =>
      intro J _ hn T hT hTg K hK
      have htop : (⊤ : Subgroup J) = ⊥ := hn
      have hKtop : K = ⊤ := le_antisymm le_top (htop.symm ▸ bot_le)
      exact hKtop.symm ▸ (inferInstance : (⊤ : Subgroup J).FiniteIndex)
    | succ n ih =>
      intro J _ hn T hT hTg K hK
      let C := Subgroup.lowerCentralSeries J n
      let q : J →* J ⧸ C := QuotientGroup.mk' C
      have hs : Function.Surjective q := QuotientGroup.mk'_surjective C
      have hq : Subgroup.lowerCentralSeries (J ⧸ C) n = ⊥ := by
        rw [← map_lowerCentralSeries_surjective q hs]
        exact (Subgroup.map_eq_bot_iff C).mpr (by simp [q])
      have hTq : closure (q '' T) = ⊤ := by
        rw [← q.map_closure,hTg,Subgroup.map_top_of_surjective q hs]
      have hiq : (K.map q).FiniteIndex := ih _ hq _ (hT.image _) hTq _ (by
        rintro _ ⟨x,hx,rfl⟩
        rw [← q.map_pow]
        exact ⟨x^m,hK x hx,rfl⟩)
      exact finiteIndex_of_central_extension K C (last_lowerCentral_le_center n hn)
        (terminalLayer_finiteIndex hT hTg K hm hK n hn) hiq
  obtain ⟨n,hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent G)
  exact gen n G hn S hSf hSg H hSp

private theorem exists_common_power (H : Subgroup G) (S : Finset G)
    (h : ∀ x ∈ S, ∃ m : ℕ, 0 < m ∧ x^m ∈ H) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ S, x^m ∈ H := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,Nat.one_pos,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨m,hm,hM⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    obtain ⟨n,hn,hN⟩ := h a (Finset.mem_insert_self _ _)
    refine ⟨m*n,Nat.mul_pos hm hn,?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · rw [Nat.mul_comm,pow_mul]
      exact H.pow_mem hN m
    · rw [pow_mul]
      exact H.pow_mem (hM x hx) n

theorem finiteIndex_of_power_generators [Group.IsNilpotent G] {S : Set G}
    (hSf : S.Finite) (hSg : closure S = ⊤) (H : Subgroup G)
    (hSp : ∀ x ∈ S, ∃ m : ℕ, 0 < m ∧ x^m ∈ H) : H.FiniteIndex := by
  classical
  obtain ⟨m,hm,hM⟩ := exists_common_power H hSf.toFinset
    (fun x hx => hSp x (hSf.mem_toFinset.mp hx))
  exact finiteIndex_of_common_power_generators hSf hSg H hm
    (fun x hx => hM x (hSf.mem_toFinset.mpr hx))

private theorem finiteIndex_in_generated_of_power_generators [Group.IsNilpotent G]
    {S : Set G} (hSf : S.Finite) (H : Subgroup G)
    (hSp : ∀ x ∈ S, ∃ m : ℕ, 0 < m ∧ x^m ∈ H) :
    (H.subgroupOf (Subgroup.closure S)).FiniteIndex := by
  let B := Subgroup.closure S
  let T : Set B := Subtype.val ⁻¹' S
  have hT : T.Finite := hSf.preimage Subtype.val_injective.injOn
  have hB : B.subtype '' T = S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,Subgroup.subset_closure hx⟩,hx,rfl⟩
  have hTg : Subgroup.closure T = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    rw [B.subtype.map_closure,hB,← MonoidHom.range_eq_map,Subgroup.range_subtype]
  exact finiteIndex_of_power_generators hT hTg (H.subgroupOf B) (fun x hx => hSp x.val hx)

/-- The isolator in a nilpotent group consists of elements some positive
power of which belongs to the subgroup. -/
def nilpotentIsolator [Group.IsNilpotent G] (H : Subgroup G) : Subgroup G where
  carrier := {a | ∃ n : ℕ, 0 < n ∧ a^n ∈ H}
  one_mem' := ⟨1,Nat.one_pos,by simp⟩
  mul_mem' := by
    intro a b ha hb
    let S : Set G := {a,b}
    have hi := finiteIndex_in_generated_of_power_generators (S := S)
      ((finite_singleton b).insert a) H (by
        intro x hx
        simp only [S,mem_insert_iff,mem_singleton_iff] at hx
        rcases hx with rfl|rfl
        · exact ha
        · exact hb)
    have hab : a*b ∈ Subgroup.closure S := (Subgroup.closure S).mul_mem
      (Subgroup.subset_closure (by simp [S])) (Subgroup.subset_closure (by simp [S]))
    obtain ⟨n,hn,_,hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hi.index_ne_zero hab
    exact ⟨n,hn,hmem.1⟩
  inv_mem' := by
    rintro a ⟨n,hn,h⟩
    exact ⟨n,hn,by rw [inv_pow]; exact H.inv_mem h⟩

theorem mem_nilpotentIsolator [Group.IsNilpotent G] (H : Subgroup G) (a : G) :
    a ∈ nilpotentIsolator H ↔ ∃ n : ℕ, 0 < n ∧ a^n ∈ H := Iff.rfl

theorem le_nilpotentIsolator [Group.IsNilpotent G] (H : Subgroup G) :
    H ≤ nilpotentIsolator H := by
  intro a ha
  exact ⟨1,Nat.one_pos,by simpa using ha⟩

theorem nilpotentIsolator_mono [Group.IsNilpotent G] :
    Monotone (nilpotentIsolator : Subgroup G → Subgroup G) := by
  rintro A B h a ⟨n,hn,ha⟩
  exact ⟨n,hn,h ha⟩

theorem mem_nilpotentIsolator_of_pow_mem [Group.IsNilpotent G] (H : Subgroup G)
    {a : G} {n : ℕ} (hn : 0 < n) (h : a^n ∈ nilpotentIsolator H) :
    a ∈ nilpotentIsolator H := by
  obtain ⟨m,hm,ha⟩ := h
  exact ⟨n*m,Nat.mul_pos hn hm,by rwa [pow_mul]⟩

theorem nilpotentIsolator_idempotent [Group.IsNilpotent G] (H : Subgroup G) :
    nilpotentIsolator (nilpotentIsolator H) = nilpotentIsolator H :=
  le_antisymm (fun _ ⟨n,hn,h⟩ => mem_nilpotentIsolator_of_pow_mem H hn h)
    (le_nilpotentIsolator (nilpotentIsolator H))

/-- Any finitely generated subgroup inside an isolator meets the original
subgroup in finite index. The conclusion is for the actual intersection. -/
theorem finiteIndex_of_fg_le_nilpotentIsolator [Group.IsNilpotent G]
    (H B : Subgroup G) (hBf : B.FG) (hB : B ≤ nilpotentIsolator H) :
    (H.subgroupOf B).FiniteIndex := by
  obtain ⟨S,hS,hSf⟩ := (Subgroup.fg_iff B).1 hBf
  have hB' : Subgroup.closure S ≤ nilpotentIsolator H := hS.symm ▸ hB
  have hi := finiteIndex_in_generated_of_power_generators hSf H (fun x hx =>
    hB' (Subgroup.subset_closure hx))
  exact hS ▸ hi

theorem nilpotentIsolator_map_equiv [Group.IsNilpotent G] {J : Type*}
    [Group J] [Group.IsNilpotent J] (e : G ≃* J) (H : Subgroup G) :
    (nilpotentIsolator H).map e.toMonoidHom = nilpotentIsolator (H.map e.toMonoidHom) := by
  ext a
  obtain ⟨g,rfl⟩ := e.surjective a
  change e.toMonoidHom g ∈ (nilpotentIsolator H).map e.toMonoidHom ↔
    e.toMonoidHom g ∈ nilpotentIsolator (H.map e.toMonoidHom)
  rw [Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective,
    mem_nilpotentIsolator,mem_nilpotentIsolator]
  simp only [← map_pow,Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective]

theorem measurableSet_mem_nilpotentIsolator [Group.IsNilpotent G]
    {X : Type*} [MeasurableSpace X] (F : X→Subgroup G)
    (hF : ∀ g, MeasurableSet {x | g ∈ F x}) (a : G) :
    MeasurableSet {x | a ∈ nilpotentIsolator (F x)} := by
  have he : {x | a ∈ nilpotentIsolator (F x)} = ⋃ n : ℕ, ⋃ _ : 0 < n, {x | a^n ∈ F x} := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion,mem_nilpotentIsolator,exists_prop]
  rw [he]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hF (a^n)

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.Isolators

-- BEGIN COMPLETE MODULE HirschProof.IsolatorWitnesses
section
                            
                                       

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set Subgroup

variable {G : Type*} [Group G] [Group.IsNilpotent G]

/-- Each subgroup has a finitely generated subgroup with the same isolator. -/
def HasFiniteIsolatorWitness (G : Type*) [Group G] [Group.IsNilpotent G] : Prop :=
  ∀ H : Subgroup G, ∃ H₀ : Subgroup G, H₀ ≤ H ∧ H₀.FG ∧
    nilpotentIsolator H₀ = nilpotentIsolator H

/-- A finitely generated subgroup of an image can be lifted by choosing one
preimage of each generator. -/
theorem exists_fg_subgroup_map_eq {A B : Type*} [Group A] [Group B]
    (f : A →* B) (H : Subgroup A) (J : Subgroup B) (hJ : J ≤ H.map f) (hJf : J.FG) :
    ∃ H₀ : Subgroup A, H₀ ≤ H ∧ H₀.FG ∧ H₀.map f = J := by
  classical
  obtain ⟨S,hS,hSf⟩ := (Subgroup.fg_iff J).mp hJf
  have lift (y : S) : ∃ x ∈ H, f x = y := hJ (hS ▸ Subgroup.subset_closure y.property)
  choose j hjh hjq using lift
  let T : Set A := range j
  have hTf : T.Finite := by
    letI := hSf.to_subtype
    exact finite_range j
  have hT : T ⊆ H := by rintro _ ⟨s,rfl⟩; exact hjh s
  have hMap : f '' T = S := by
    ext y
    constructor
    · rintro ⟨x,⟨s,rfl⟩,rfl⟩
      rw [hjq]
      exact s.property
    · intro hy
      exact ⟨j ⟨y,hy⟩,⟨⟨y,hy⟩,rfl⟩,hjq ⟨y,hy⟩⟩
  refine ⟨closure T,Subgroup.closure_le _ |>.mpr hT,(Subgroup.fg_iff _).mpr ⟨T,rfl,hTf⟩,?_⟩
  rw [f.map_closure,hMap,hS]

/-- The finite isolator witness property passes through central extensions. -/
theorem HasFiniteIsolatorWitness.centralExtension (C : Subgroup G) [C.Normal]
    (hc : C ≤ Subgroup.center G) (hC : HasFiniteIsolatorWitness C)
    (hQ : HasFiniteIsolatorWitness (G ⧸ C)) : HasFiniteIsolatorWitness G := by
  intro H
  let q := QuotientGroup.mk' C
  obtain ⟨Q₀,hQ₀,hQ₀f,hQiso⟩ := hQ (H.map q)
  obtain ⟨J,hJ,hJf,hJq⟩ := exists_fg_subgroup_map_eq q H Q₀ hQ₀ hQ₀f
  obtain ⟨C₀,hC₀,hC₀f,hCiso⟩ := hC (H.subgroupOf C)
  let D := J ⊔ C₀.map C.subtype
  have hD : D ≤ H := sup_le hJ (by rintro _ ⟨c,hc₀,rfl⟩; exact hC₀ hc₀)
  have hDf : D.FG := hJf.sup (IsLocallyFiniteGroup.fg_map _ _ hC₀f)
  refine ⟨D,hD,hDf,le_antisymm (nilpotentIsolator_mono hD) ?_⟩
  have hHI : H ≤ nilpotentIsolator D := by
    intro x hx
    have hxq : q x ∈ nilpotentIsolator Q₀ :=
      hQiso.symm ▸ le_nilpotentIsolator (H.map q) ⟨x,hx,rfl⟩
    obtain ⟨n,hn,hxn⟩ := hxq
    rw [← map_pow,← hJq] at hxn
    obtain ⟨j,hj,hjq⟩ := hxn
    have hcq : q (j⁻¹*x^n) = 1 := by rw [map_mul,map_inv,hjq,inv_mul_cancel]
    have hc' : j⁻¹*x^n ∈ C := (QuotientGroup.eq_one_iff _).mp hcq
    let c : C := ⟨j⁻¹*x^n,hc'⟩
    have hch : c ∈ H.subgroupOf C := H.mul_mem (H.inv_mem (hJ hj)) (H.pow_mem hx n)
    have hci : c ∈ nilpotentIsolator C₀ :=
      hCiso.symm ▸ le_nilpotentIsolator (H.subgroupOf C) hch
    obtain ⟨m,hm,hcm⟩ := hci
    have hcomm : Commute j c.val := Subgroup.mem_center_iff.mp (hc hc') j
    have he : j*c.val = x^n := by change j*(j⁻¹*x^n) = x^n; simp
    refine ⟨n*m,Nat.mul_pos hn hm,?_⟩
    rw [pow_mul,← he,hcomm.mul_pow]
    have hJD : J ≤ D := le_sup_left
    have hCD : C₀.map C.subtype ≤ D := le_sup_right
    exact D.mul_mem (D.pow_mem (hJD hj) m) (hCD ⟨c^m,hcm,rfl⟩)
  simpa only [nilpotentIsolator_idempotent] using nilpotentIsolator_mono hHI

/-- In a countable group with finite isolator witnesses there are only
countably many possible isolators. -/
theorem countable_range_nilpotentIsolator [Countable G] (h : HasFiniteIsolatorWitness G) :
    (range (nilpotentIsolator : Subgroup G → Subgroup G)).Countable := by
  classical
  let I (s : Finset G) := nilpotentIsolator (closure (s : Set G))
  apply (countable_range I).mono
  rintro _ ⟨H,rfl⟩
  obtain ⟨H₀,_,hH₀f,he⟩ := h H
  obtain ⟨T,hT,hTf⟩ := (Subgroup.fg_iff H₀).mp hH₀f
  refine ⟨hTf.toFinset,?_⟩
  change nilpotentIsolator (closure (↑hTf.toFinset : Set G)) = nilpotentIsolator H
  rw [hTf.coe_toFinset,hT,he]

theorem measurableSet_eq_nilpotentIsolator [Countable G] {X : Type*} [MeasurableSpace X]
    (F : X → Subgroup G) (hF : ∀ g, MeasurableSet {x | g ∈ F x}) (J : Subgroup G) :
    MeasurableSet {x | nilpotentIsolator (F x) = J} := by
  have he : {x | nilpotentIsolator (F x) = J} = ⋂ g : G,
      ({x | g ∈ nilpotentIsolator (F x)} ∩ {x | g ∈ J}) ∪
        ({x | g ∈ nilpotentIsolator (F x)}ᶜ ∩ {x | g ∈ J}ᶜ) := by
    classical
    ext x
    simp only [mem_setOf_eq,mem_iInter,mem_union,mem_inter_iff,mem_compl_iff]
    rw [SetLike.ext_iff]
    exact forall_congr' (fun _ => by tauto)
  rw [he]
  apply MeasurableSet.iInter
  intro g
  have hg : MeasurableSet {x : X | g ∈ J} := MeasurableSet.const _
  have hp := measurableSet_mem_nilpotentIsolator F hF g
  exact (hp.inter hg).union (hp.compl.inter hg.compl)

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.IsolatorWitnesses

-- BEGIN COMPLETE MODULE HirschProof.FiniteComponentColoring
section
                               
                                                               
                                                          
                                     
                             

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- The ordinary counterpart of the Borel finite cover definition. -/
def OrdinaryAsdimLE (D : BorelNear X) (d : ℕ) (A : Set X) : Prop :=
  ∀ r : ℕ, ∃ U : Fin (d+1) → Set X, ∃ R : ℕ,
    (∀ i, U i ⊆ A) ∧ (∀ x ∈ A, ∃ i, x ∈ U i) ∧ ∀ i, D.boundComp (U i) r R

namespace BorelNear
variable (D : BorelNear X)

section Parametric
variable {P : Type*} [MeasurableSpace P] [MeasurableEq P]

/-- Add an inert standard Borel parameter to a countably charted metric. -/
def parameterNear (P : Type*) [MeasurableSpace P] [MeasurableEq P] : BorelNear (P×X) where
  near := fun r u v => u.1 = v.1 ∧ D.near r u.2 v.2
  refl := fun r x => ⟨rfl,D.refl r x.2⟩
  symm := by
    intro r x y h
    exact ⟨h.1.symm,D.symm r h.2⟩
  mono := by
    intro r s hrs x y h
    exact ⟨h.1,D.mono hrs h.2⟩
  triangle := by
    intro r s x y z h k
    exact ⟨h.1.trans k.1,D.triangle h.2 k.2⟩
  zero := fun h => Prod.ext h.1 (D.zero h.2)
  borel := fun r =>
    (measurableSet_eq_fun measurable_fst.fst measurable_snd.fst).inter
      ((D.borel r).preimage (measurable_fst.snd.prodMk measurable_snd.snd))
  moves := fun n x => (x.1,D.moves n x.2)
  measurable_moves := fun n => measurable_fst.prodMk ((D.measurable_moves n).comp measurable_snd)
  moves_cover := by
    intro r x y h
    obtain ⟨n,hn⟩ := D.moves_cover h.2
    exact ⟨n,Prod.ext h.1 hn⟩
  uniformly_finite := by
    classical
    intro r
    obtain ⟨N,hN⟩ := D.uniformly_finite r
    refine ⟨N,fun p => ?_⟩
    obtain ⟨t,ht,hp⟩ := hN p.2
    refine ⟨t.image (fun x => (p.1,x)),Finset.card_image_le.trans ht,?_⟩
    intro q hq
    exact Finset.mem_image.mpr ⟨q.2,hp _ hq.2,Prod.ext hq.1 rfl⟩

theorem comp_parameter_iff {A : Set (P×X)} (p : P) (r : ℕ) (x y : X) :
    (D.parameterNear P).comp r A (p,x) (p,y) ↔ D.comp r {z | (p,z) ∈ A} x y := by
  constructor
  · intro h
    have hx : (p,x) ∈ A := h.1
    refine ⟨hx,?_⟩
    have H {v : P×X} (hh : Relation.ReflTransGen ((D.parameterNear P).edge r A) (p,x) v) :
        v.1 = p ∧ Relation.ReflTransGen (D.edge r {z | (p,z) ∈ A}) x v.2 := by
      induction hh with
      | refl => exact ⟨rfl,.refl⟩
      | @tail a b hab he ih =>
        have hb : b.1 = p := he.2.2.1.symm.trans ih.1
        refine ⟨hb,ih.2.tail ⟨?_,?_,he.2.2.2⟩⟩
        · have ha : (p,a.2)=a := Prod.ext ih.1.symm rfl
          change (p,a.2)∈A
          rw [ha]; exact he.1
        · have hb' : (p,b.2)=b := Prod.ext hb.symm rfl
          change (p,b.2)∈A
          rw [hb']; exact he.2.1
    exact (H h.2).2
  · intro h
    exact D.comp_map (fun z => (p,z)) (fun _ hz => hz)
      (by intro u v _ _ h; exact ⟨rfl,h⟩) h

end Parametric

section Selection
variable [StandardBorelSpace X]

private def bestIndex (A : Set X) (r : ℕ) (f : X → ℝ) (x : X) (i : ℕ) : Prop :=
  (x ∉ A ∧ i = 0) ∨
    (D.comp r A x (D.moves i x) ∧
      ∀ j : ℕ, D.comp r A x (D.moves j x) → f (D.moves i x) ≤ f (D.moves j x))

private theorem measurableSet_bestIndex {A : Set X} (hA : MeasurableSet A)
    (r : ℕ) {f : X → ℝ} (hf : Measurable f) (i : ℕ) :
    MeasurableSet {x | D.bestIndex A r f x i} := by
  have hC (j : ℕ) : MeasurableSet {x | D.comp r A x (D.moves j x)} :=
    (D.measurableSet_comp hA r).preimage (measurable_id.prodMk (D.measurable_moves j))
  have hL : MeasurableSet {x | x ∉ A ∧ i=0} := by
    by_cases h : i = 0
    · simpa only [h,and_true] using hA.compl
    · simp [h]
  apply hL.union
  apply (hC i).inter
  change MeasurableSet {x | ∀ j : ℕ,
    D.comp r A x (D.moves j x) → f (D.moves i x) ≤ f (D.moves j x)}
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  convert (hC j).compl.union
    (measurableSet_le (hf.comp (D.measurable_moves i)) (hf.comp (D.measurable_moves j))) using 1
  ext x
  simp [imp_iff_not_or,Function.comp_def]

private theorem exists_bestIndex {A : Set X} {r R : ℕ}
    (hR : D.boundComp A r R) (f : X → ℝ) (x : X) :
    ∃ i, D.bestIndex A r f x i := by
  classical
  by_cases hx : x∈A
  · let C := {y | D.comp r A x y}
    have hC : C.Finite := (D.ball_finite R x).subset (fun _ h => hR h)
    have hnon : C.Nonempty := ⟨x,D.comp_refl hx⟩
    obtain ⟨v,hv,hmin⟩ := Set.exists_min_image C f hC hnon
    obtain ⟨i,hi⟩ := D.moves_cover (hR hv)
    refine ⟨i,Or.inr ⟨?_,?_⟩⟩
    · rw [hi]; exact hv
    · intro j hj
      rw [hi]
      exact hmin _ hj
  · exact ⟨0,Or.inl ⟨hx,rfl⟩⟩

/-- Borel choice of a common representative of each bounded component. -/
theorem exists_measurable_component_representative {A : Set X} {r R : ℕ}
    (hA : MeasurableSet A) (hR : D.boundComp A r R) :
    ∃ p : X → X, Measurable p ∧
      (∀ x ∈ A, D.comp r A x (p x)) ∧
      ∀ ⦃x y⦄, D.comp r A x y → p x = p y := by
  classical
  obtain ⟨f,hf⟩ := exists_measurableEmbedding_real X
  let w (x : X) := Nat.find (D.exists_bestIndex hR f x)
  let p (x : X) := D.moves (w x) x
  have hp (x : X) (hx : x∈A) : D.comp r A x (p x) ∧
      ∀ j, D.comp r A x (D.moves j x) → f (p x) ≤ f (D.moves j x) := by
    exact (Nat.find_spec (D.exists_bestIndex hR f x)).resolve_left (fun h => h.1 hx)
  have hmin {x y : X} (h : D.comp r A x y) : f (p x) ≤ f y := by
    obtain ⟨j,hj⟩ := D.moves_cover (hR h)
    rw [← hj] at h ⊢
    exact (hp x h.1).2 j h
  refine ⟨p,?_,fun x hx => (hp x hx).1,?_⟩
  · exact Measurable.find D.measurable_moves
      (fun i => D.measurableSet_bestIndex hA r hf.measurable i)
      (D.exists_bestIndex hR f)
  · intro x y h
    have hxp := (hp x (D.comp_start h)).1
    have hyp := (hp y (D.comp_end h)).1
    apply hf.injective
    exact le_antisymm (hmin (D.comp_trans h hyp))
      (hmin (D.comp_trans (D.comp_symm h) hxp))

end Selection

section Coding
variable [StandardBorelSpace X]

private def indexHit (p : X×X) (n : ℕ) : Prop :=
  D.moves n p.1 = p.2 ∨ ((∀ j, D.moves j p.1 ≠ p.2) ∧ n=0)

private theorem exists_indexHit (p : X×X) : ∃ n, D.indexHit p n := by
  by_cases h : ∃ n, D.moves n p.1 = p.2
  · obtain ⟨n,hn⟩ := h
    exact ⟨n,Or.inl hn⟩
  · exact ⟨0,Or.inr ⟨fun j hj => h ⟨j,hj⟩,rfl⟩⟩

private theorem measurableSet_indexHit (n : ℕ) :
    MeasurableSet {p : X×X | D.indexHit p n} := by
  have hm (i : ℕ) : MeasurableSet {p : X×X | D.moves i p.1 = p.2} :=
    measurableSet_eq_fun ((D.measurable_moves i).comp measurable_fst) measurable_snd
  apply (hm n).union
  change MeasurableSet {p : X×X | (∀ j, D.moves j p.1 ≠ p.2) ∧ n=0}
  by_cases h : n = 0
  · have he : {p : X×X | (∀ j, D.moves j p.1 ≠ p.2) ∧ n=0} =
        ⋂ j : ℕ, {p : X×X | D.moves j p.1 = p.2}ᶜ := by
      ext p
      simp [h]
    rw [he]
    exact MeasurableSet.iInter fun j => (hm j).compl
  · simp [h]

private noncomputable def indexOf (p : X×X) : ℕ :=
  @Nat.find (D.indexHit p) (Classical.decPred _) (D.exists_indexHit p)

private theorem measurable_indexOf : Measurable D.indexOf := by
  classical
  exact measurable_find D.exists_indexHit D.measurableSet_indexHit

private theorem moves_indexOf {p : X×X} (h : ∃ j, D.moves j p.1 = p.2) :
    D.moves (D.indexOf p) p.1 = p.2 := by
  classical
  exact (Nat.find_spec (D.exists_indexHit p)).resolve_right (fun q =>
    let ⟨j,hj⟩ := h; q.1 j hj)

private noncomputable def useCode {d : ℕ} (L : List (Fin (d+1))) (p : X×X) :
    Fin (d+1) := L[D.indexOf p]?.getD 0

private theorem measurable_useCode {d : ℕ} (L : List (Fin (d+1))) :
    Measurable (D.useCode L) :=
  (measurable_of_countable (fun n : ℕ => L[n]?.getD 0)).comp D.measurable_indexOf

private def codedRegion {d : ℕ} (W : Set X) (s : ℕ)
    (L : List (Fin (d+1))) (i : Fin (d+1)) : Set (X×X) :=
  {p | D.comp s W p.1 p.2 ∧ D.useCode L p = i}

private theorem measurableSet_codedRegion {d : ℕ} {W : Set X} (hW : MeasurableSet W)
    (s : ℕ) (L : List (Fin (d+1))) (i : Fin (d+1)) :
    MeasurableSet (D.codedRegion W s L i) :=
  (D.measurableSet_comp hW s).inter ((D.measurable_useCode L) (measurableSet_singleton i))

private def validCode {d : ℕ} (W : Set X) (s r R : ℕ)
    (L : List (Fin (d+1))) (p : X) : Prop :=
  ∀ (i : Fin (d+1)) (a b : ℕ),
    (D.parameterNear X).comp r (D.codedRegion W s L i) (p,D.moves a p) (p,D.moves b p) →
    D.near R (D.moves a p) (D.moves b p)

private theorem measurableSet_validCode {d : ℕ} {W : Set X} (hW : MeasurableSet W)
    (s r R : ℕ) (L : List (Fin (d+1))) : MeasurableSet {p | D.validCode W s r R L p} := by
  change MeasurableSet {p | ∀ (i : Fin (d+1)) (a b : ℕ),
    (D.parameterNear X).comp r (D.codedRegion W s L i) (p,D.moves a p) (p,D.moves b p) →
    D.near R (D.moves a p) (D.moves b p)}
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
  have hA : MeasurableSet {p | (D.parameterNear X).comp r (D.codedRegion W s L i)
      (p,D.moves a p) (p,D.moves b p)} :=
    ((D.parameterNear X).measurableSet_comp (D.measurableSet_codedRegion hW s L i) r).preimage
      ((measurable_id.prodMk (D.measurable_moves a)).prodMk (measurable_id.prodMk (D.measurable_moves b)))
  have hB : MeasurableSet {p | D.near R (D.moves a p) (D.moves b p)} :=
    (D.borel R).preimage ((D.measurable_moves a).prodMk (D.measurable_moves b))
  convert hA.compl.union hB using 1
  ext p
  simp [imp_iff_not_or]

private theorem exists_validCode {d s r R HW : ℕ} {A W : Set X}
    (hW : W ⊆ A) (hWc : D.boundComp W s HW)
    (V : Fin (d+1) → Set X) (hVcov : ∀ x ∈ A, ∃ i, x ∈ V i)
    (hVb : ∀ i, D.boundComp (V i) r R) (p : X) :
    ∃ L : List (Fin (d+1)), D.validCode W s r R L p := by
  classical
  let C := {x | D.comp s W p x}
  have hC : C.Finite := (D.ball_finite HW p).subset (fun x hx => hWc hx)
  let B := hC.toFinset.sup (fun x => D.indexOf (p,x))
  let f (x : X) : Fin (d+1) := if hx : x ∈ A then Classical.choose (hVcov x hx) else 0
  have hf {x : X} (hx : x ∈ A) : x ∈ V (f x) := by
    simp only [f,dif_pos hx]
    exact Classical.choose_spec (hVcov x hx)
  let L := List.ofFn (fun i : Fin (B+1) => f (D.moves i.val p))
  have hL {x : X} (hx : x ∈ C) : D.useCode L (p,x) = f x := by
    have hle : D.indexOf (p,x) ≤ B := Finset.le_sup (f := fun x => D.indexOf (p,x))
      (hC.mem_toFinset.mpr hx)
    have hlt : D.indexOf (p,x) < L.length := by simpa only [L,List.length_ofFn] using Nat.lt_succ_of_le hle
    have hmove : D.moves (D.indexOf (p,x)) p = x :=
      D.moves_indexOf (D.moves_cover (hWc hx))
    simp only [useCode,List.getElem?_eq_getElem hlt,Option.getD_some,L,List.getElem_ofFn,hmove]
  refine ⟨L,?_⟩
  intro i a b h
  have hsub : {z | (p,z) ∈ D.codedRegion W s L i} ⊆ V i := by
    rintro x ⟨hx,hix⟩
    rw [hL hx] at hix
    exact hix ▸ hf (hW (D.comp_end hx))
  exact hVb i (D.comp_mono hsub le_rfl ((D.comp_parameter_iff p r _ _).mp h))

/-- A finite-component measurable piece admits the ordinary radius/range
cover bounds with measurable color sets. This realizes Lemma 4.3 by coding
the finite color assignments using the countable possible displacements. -/
theorem borel_cover_on_bounded_components {d r R s B : ℕ} {A W : Set X}
    (hW : W ⊆ A) (hWm : MeasurableSet W) (hWr : D.boundComp W s B) (hrs : r ≤ s)
    (V : Fin (d+1) → Set X) (hVcov : ∀ x ∈ A, ∃ i, x ∈ V i)
    (hVb : ∀ i, D.boundComp (V i) r R) :
    ∃ U : Fin (d+1) → Set X, (∀ i, U i ⊆ W) ∧ (∀ i, MeasurableSet (U i)) ∧
      (∀ x ∈ W, ∃ i, x ∈ U i) ∧ ∀ i, D.boundComp (U i) r R := by
  classical
  obtain ⟨p,hp,hpx,hpe⟩ := D.exists_measurable_component_representative hWm hWr
  obtain ⟨e,he⟩ := exists_surjective_nat (List (Fin (d+1)))
  have hEx (x : X×X) : ∃ n, D.validCode W s r R (e n) x.1 := by
    obtain ⟨L,hL⟩ := D.exists_validCode hW hWr V hVcov hVb x.1
    obtain ⟨n,rfl⟩ := he L
    exact ⟨n,hL⟩
  let idx (x : X×X) := Nat.find (hEx x)
  let c (x : X×X) := D.useCode (e (idx x)) x
  have hcm : Measurable c := Measurable.find (fun n => D.measurable_useCode (e n))
    (fun n => (D.measurableSet_validCode hWm s r R (e n)).preimage measurable_fst) hEx
  have idx_const (q u v : X) : idx (q,u) = idx (q,v) := by
    rfl
  let W' (i : Fin (d+1)) := {x∈W | c (p x,x) = i}
  refine ⟨W',fun _ _ hx => hx.1,fun i => ?_,fun x hx => ⟨c (p x,x),hx,rfl⟩,?_⟩
  · exact hWm.inter ((hcm.comp (hp.prodMk measurable_id)) (measurableSet_singleton i))
  · intro i x y hxy
    have hx : x∈W := (D.comp_start hxy).1
    have hy : y∈W := (D.comp_end hxy).1
    let q := p x
    let T := e (idx (q,x))
    have hq {z : X} (hz : D.comp r (W' i) x z) : p z = q :=
      (hpe (D.comp_mono (fun _ h => h.1) hrs hz)).symm
    have hW' {u : X} (hu : u∈W' i) (hh : p u = q) :
        u ∈ {z | (q,z) ∈ D.codedRegion W s T i} := by
      refine ⟨D.comp_symm (hh ▸ hpx u hu.1),?_⟩
      have hc : c (q,u)=i := hh ▸ hu.2
      simpa only [c,T,idx_const q u x] using hc
    have hpath : D.comp r {z | (q,z) ∈ D.codedRegion W s T i} x y := by
      have hxi : x ∈ W' i := hxy.1
      refine ⟨hW' hxi rfl,?_⟩
      have h := hxy.2
      clear hxy hy
      induction h with
      | refl => exact .refl
      | tail hpath hstep ih =>
        exact ih.tail ⟨hW' hstep.1 (hq ⟨hxi,hpath⟩),
          hW' hstep.2.1 (hq ⟨hxi,hpath.tail hstep⟩),hstep.2.2⟩
    have hvalid : D.validCode W s r R T q := Nat.find_spec (hEx (q,x))
    obtain ⟨a,ha⟩ := D.moves_cover (hWr (D.comp_symm (hpx x hx)))
    obtain ⟨b,hb⟩ := D.moves_cover (hWr (D.comp_symm
      (hq hxy ▸ hpx y hy)))
    change D.moves a q = x at ha
    change D.moves b q = y at hb
    rw [← ha,← hb] at hpath ⊢
    exact hvalid i a b ((D.comp_parameter_iff q r _ _).2 hpath)

end Coding
end BorelNear
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.FiniteComponentColoring

-- BEGIN COMPLETE MODULE HirschProof.DimensionEquality
section
                                          

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

variable {X : Type*} [MeasurableSpace X] (D : BorelNear X)

private theorem union_attach {A B : Set X} {r a b : ℕ}
    (hA : D.boundComp A r a) (hB : D.boundComp B (r+a+r) b)
    {x y : X} (hx : x ∈ B) (h : D.comp r (A∪B) x y) :
    D.near (b+r+a) x y := by
  have haux {z : X} (p : Relation.ReflTransGen (D.edge r (A∪B)) x z) :
      D.comp (r+a+r) B x z ∨ ∃ u v, D.comp (r+a+r) B x u ∧
        D.near r u v ∧ D.comp r A v z := by
    induction p with
    | refl => exact Or.inl (D.comp_refl hx)
    | @tail y z p e ih =>
      have hyz := e.2.2
      by_cases hzB : z ∈ B
      · left
        rcases ih with hxy|⟨u,v,hxu,huv,hvy⟩
        · exact D.comp_trans hxy (D.comp_single (D.comp_end hxy) hzB
            (D.mono (by omega) hyz))
        · exact D.comp_trans hxu (D.comp_single (D.comp_end hxu) hzB
            (D.triangle (D.triangle huv (hA hvy)) hyz))
      · right
        have hzA : z ∈ A := e.2.1.resolve_right hzB
        rcases ih with hxy|⟨u,v,hxu,huv,hvy⟩
        · exact ⟨y,z,hxy,hyz,D.comp_refl hzA⟩
        · exact ⟨u,v,hxu,huv,D.comp_trans hvy (D.comp_single (D.comp_end hvy) hzA hyz)⟩
  rcases haux h.2 with hB' | ⟨u,v,hxu,huv,hvy⟩
  · exact D.mono (by omega) (hB hB')
  · exact D.triangle (D.triangle (hB hxu) huv) (hA hvy)

/-- Glue two bounded-component sets, separating the second set at the
larger scale needed to carry bridges through the first. -/
theorem BorelNear.boundComp_union_larger_scale {A B : Set X} {r a b : ℕ}
    (hA : D.boundComp A r a) (hB : D.boundComp B (r+a+r) b) :
    D.boundComp (A∪B) r (2*(b+r+a)) := by
  classical
  intro x y hxy
  by_cases he : ∃ z ∈ B, D.comp r (A∪B) x z
  · obtain ⟨z,hz,hxz⟩ := he
    have hzx := D.comp_symm hxz
    have hx := union_attach D hA hB hz hzx
    have hy := union_attach D hA hB hz (D.comp_trans hzx hxy)
    exact D.mono (by omega) (D.triangle (D.symm _ hx) hy)
  · have hxA : x ∈ A := hxy.1.resolve_right (fun hxB => he ⟨x,hxB,D.comp_refl hxy.1⟩)
    have hxy' : D.comp r A x y := by
      refine ⟨hxA,?_⟩
      have h0 := hxy.1
      have hp := hxy.2
      clear hxy
      induction hp with
      | refl => exact .refl
      | @tail u v h₁ h₂ ih =>
        have hv : v ∈ A := h₂.2.1.resolve_right (fun hvB => he ⟨v,hvB,h0,h₁.tail h₂⟩)
        exact ih.tail ⟨D.comp_end ⟨hxA,ih⟩,hv,h₂.2.2⟩
    exact D.mono (by omega) (hA hxy')

private def HasCover (d r R : ℕ) (A : Set X) : Prop :=
  ∃ U : Fin (d+1) → Set X, (∀ i, U i ⊆ A) ∧ (∀ i, MeasurableSet (U i)) ∧
    (∀ x ∈ A, ∃ i, x ∈ U i) ∧ ∀ i, D.boundComp (U i) r R

private theorem hasCover_empty (d r R : ℕ) : HasCover D d r R (∅ : Set X) :=
  ⟨fun _ => ∅,fun _ => Subset.rfl,fun _ => MeasurableSet.empty,fun _ h => h.elim,by
    intro i x y hxy
    exact hxy.1.elim⟩

private theorem hasCover_union {d r a b : ℕ} {A B : Set X}
    (hA : HasCover D d r a A) (hB : HasCover D d (r+a+r) b B) :
    HasCover D d r (2*(b+r+a)) (A∪B) := by
  obtain ⟨U,hU,hUm,hUall,hUB⟩ := hA
  obtain ⟨V,hV,hVm,hVall,hVB⟩ := hB
  refine ⟨fun i => U i ∪ V i,fun i => union_subset_union (hU i) (hV i),
    fun i => (hUm i).union (hVm i),?_,fun i => D.boundComp_union_larger_scale (hUB i) (hVB i)⟩
  rintro x (hx|hx)
  · obtain ⟨i,hi⟩ := hUall x hx
    exact ⟨i,Or.inl hi⟩
  · obtain ⟨i,hi⟩ := hVall x hx
    exact ⟨i,Or.inr hi⟩

/-- If the dimension is Borel-finite, an ordinary dimension bound is
also a Borel dimension bound. Theorem 4.2 in the form needed here. -/
theorem BorelNear.asdim_of_ordinary_of_borelFinite [StandardBorelSpace X]
    {d d' : ℕ} {A : Set X} (ho : OrdinaryAsdimLE D d A)
    (hb : BorelAsdimLE D d' A) : BorelAsdimLE D d A := by
  classical
  intro r
  choose U R hU hUa hUb using ho
  let m : ℕ → ℕ := Nat.rec 0 (fun _ a => 2*(R (r+a+r)+r+a))
  let T (n : ℕ) := r+m n+r
  let large := (Finset.range (d'+1)).sup T
  obtain ⟨S,B,hS,hSm,hSa,hSb⟩ := hb large
  let W (n : ℕ) := ⋃ i : Fin (d'+1), ⋃ _ : i.val < n, S i
  have hW0 : W 0 = ∅ := by
    ext x
    simp [W]
  have hWsucc {n : ℕ} (hn : n < d'+1) :
      W (n+1) = W n ∪ S ⟨n,hn⟩ := by
    ext x
    simp only [W,mem_iUnion,mem_union]
    constructor
    · rintro ⟨i,hi,hx⟩
      by_cases h : i.val < n
      · exact Or.inl ⟨i,h,hx⟩
      · have hi' : i = ⟨n,hn⟩ := Fin.ext (by simp; omega)
        exact Or.inr (hi' ▸ hx)
    · rintro (⟨i,hi,hx⟩|hx)
      · exact ⟨i,hi.trans (Nat.lt_succ_self n),hx⟩
      · exact ⟨⟨n,hn⟩,Nat.lt_succ_self n,hx⟩
  have hWA : W (d'+1) = A := by
    ext x
    simp only [W,mem_iUnion]
    constructor
    · rintro ⟨i,_,hx⟩
      exact hS i hx
    · intro hx
      obtain ⟨i,hi⟩ := hSa x hx
      exact ⟨i,i.isLt,hi⟩
  have hc (n : ℕ) (hn : n ≤ d'+1) : HasCover D d r (m n) (W n) := by
    induction n with
    | zero =>
      rw [hW0]
      exact hasCover_empty D d r _
    | succ n ih =>
      have hlt : n < d'+1 := hn
      let i : Fin (d'+1) := ⟨n,hlt⟩
      have hT : T n ≤ large := Finset.le_sup (f := T) (Finset.mem_range.mpr hlt)
      have hnew : HasCover D d (T n) (R (T n)) (S i) :=
        D.borel_cover_on_bounded_components (hS i) (hSm i) (hSb i) hT
          (U (T n)) (hUa (T n)) (hUb (T n))
      rw [hWsucc hlt]
      exact hasCover_union D (ih (Nat.le_of_succ_le hn)) hnew
  have ha := hc (d'+1) le_rfl
  rw [hWA] at ha
  obtain ⟨V,hV,hVm,hVa,hVb⟩ := ha
  exact ⟨V,m (d'+1),hV,hVm,hVa,hVb⟩

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.DimensionEquality

-- BEGIN COMPLETE MODULE HirschProof.FiniteIndexSharp
section
                                    
                                     

set_option autoImplicit false
noncomputable section

namespace LocalHirschHyperfinite

open Set

section OrdinaryPullback

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Ordinary asymptotic dimension pulls back under a controlled finite-fiber map. -/
theorem ordinaryAsdim_pullback_finite_fibers (D : BorelNear X) (B : BorelNear Y)
    {A : Set X} {U : Set Y} (f : X → Y) (hmap : MapsTo f A U)
    (hcontrolled : ∀ r : ℕ, ∃ s : ℕ, ∀ ⦃x y⦄, x ∈ A → y ∈ A →
      D.near r x y → B.near s (f x) (f y))
    (hfinite : ∃ N : ℕ, ∀ y : Y, ∃ t : Finset X, t.card ≤ N ∧
      ∀ x ∈ A, f x = y → x ∈ t)
    {d : ℕ} (hU : OrdinaryAsdimLE B d U) : OrdinaryAsdimLE D d A := by
  classical
  obtain ⟨N,hN⟩ := hfinite
  choose fibers hfcard hfmem using hN
  intro r
  obtain ⟨s,hs⟩ := hcontrolled r
  obtain ⟨V,R,hV,hcov,hcomp⟩ := hU s
  obtain ⟨M,hM⟩ := B.uniformly_finite R
  let W i := A ∩ f ⁻¹' V i
  refine ⟨W,r*(M*N),fun _ => inter_subset_left,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := hcov (f x) (hmap hx)
    exact ⟨i,hx,hi⟩
  · intro i
    apply D.boundComp_of_small
    intro x
    obtain ⟨t,ht,hball⟩ := hM (f x)
    refine ⟨t.biUnion fibers,?_,?_⟩
    · calc
        (t.biUnion fibers).card ≤ ∑ y ∈ t, (fibers y).card := Finset.card_biUnion_le
        _ ≤ t.card * N := Finset.sum_le_card_nsmul _ _ _ (fun y _ => hfcard y)
        _ ≤ M * N := Nat.mul_le_mul_right N ht
    · intro y hxy
      have hp : B.comp s (V i) (f x) (f y) := by
        apply D.comp_map f (fun _ h => h.2) _ hxy
        intro a b ha hb hab
        exact hs ha.1 hb.1 hab
      exact Finset.mem_biUnion.mpr
        ⟨f y,hball _ (hcomp i hp),hfmem _ y (D.comp_end hxy).1 rfl⟩

theorem ordinaryAsdim_of_borel (D : BorelNear X) {A : Set X} {d : ℕ}
    (h : BorelAsdimLE D d A) : OrdinaryAsdimLE D d A := by
  intro r
  obtain ⟨U,R,hU,_,hcov,hbound⟩ := h r
  exact ⟨U,R,hU,hcov,hbound⟩

end OrdinaryPullback

variable {G X : Type*} [Group G] [MulAction G X]

private def actionOrbitSetoid (G : Type*) [Group G] (X : Type*) [MulAction G X] : Setoid X where
  r := orbitRel G
  iseqv := ⟨fun x => ⟨1,one_smul _ _⟩,by
    rintro x y ⟨g,rfl⟩
    exact ⟨g⁻¹,inv_smul_smul _ _⟩,by
    rintro x y z ⟨g,rfl⟩ ⟨h,rfl⟩
    exact ⟨h*g,mul_smul _ _ _⟩⟩

/-- An arbitrary base point chosen once per ambient orbit. -/
private def orbitAnchor (G : Type*) [Group G] {X : Type*} [MulAction G X] (x : X) : X :=
  (Quotient.mk (actionOrbitSetoid G X) x).out

private theorem orbitAnchor_related (x : X) : orbitRel G x (orbitAnchor G x) := by
  apply (actionOrbitSetoid G X).iseqv.symm
  exact Quotient.exact (Quotient.out_eq (Quotient.mk (actionOrbitSetoid G X) x))

private theorem orbitAnchor_eq {x y : X} (h : orbitRel G x y) : orbitAnchor G x = orbitAnchor G y :=
  congrArg Quotient.out (Quotient.sound (s := actionOrbitSetoid G X) h)

variable (H : Subgroup G)

private theorem exists_normalizingCoset (x : X) :
    ∃ i : RightCosets H, ∃ h : H, h • (rightCosetRepresentative H i • x) = orbitAnchor G x := by
  obtain ⟨g,hg⟩ := orbitAnchor_related (G := G) x
  let i : RightCosets H := Quotient.mk _ g
  let r := rightCosetRepresentative H i
  have hh : g*r⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp
    (Quotient.exact (rightCosetRepresentative_spec H i))
  refine ⟨i,⟨g*r⁻¹,hh⟩,?_⟩
  change (g*r⁻¹) • (r • x) = orbitAnchor G x
  rw [mul_smul,inv_smul_smul,hg]

private def normalizingCoset (x : X) : RightCosets H := (exists_normalizingCoset H x).choose

private def orbitToSubgroup (x : X) : X := rightCosetRepresentative H (normalizingCoset H x) • x

private theorem orbitToSubgroup_related {x y : X} (hxy : orbitRel G x y) :
    orbitRel H (orbitToSubgroup H x) (orbitToSubgroup H y) := by
  obtain ⟨a,ha⟩ := (exists_normalizingCoset H x).choose_spec
  obtain ⟨b,hb⟩ := (exists_normalizingCoset H y).choose_spec
  change a • orbitToSubgroup H x = orbitAnchor G x at ha
  change b • orbitToSubgroup H y = orbitAnchor G y at hb
  refine ⟨b⁻¹*a,?_⟩
  rw [mul_smul,ha,orbitAnchor_eq hxy,← hb,inv_smul_smul]

private theorem normalization_displacement_mem
    (hstab : ∀ (x : X) (g : G), g • x = x → g ∈ H) {x y : X} (g : G) (hg : g • x = y) :
    rightCosetRepresentative H (normalizingCoset H y) * g *
      (rightCosetRepresentative H (normalizingCoset H x))⁻¹ ∈ H := by
  let r := rightCosetRepresentative H (normalizingCoset H x)
  let s := rightCosetRepresentative H (normalizingCoset H y)
  let k := s*g*r⁻¹
  have hk : k • orbitToSubgroup H x = orbitToSubgroup H y := by
    change (s*g*r⁻¹) • (r • x) = s • y
    rw [mul_smul,inv_smul_smul,mul_smul,hg]
  obtain ⟨h,hh⟩ := orbitToSubgroup_related H ⟨g,hg⟩
  change (h : G) • orbitToSubgroup H x = orbitToSubgroup H y at hh
  have hfix : ((h : G)⁻¹*k) • orbitToSubgroup H x = orbitToSubgroup H x := by
    rw [mul_smul,hk,← hh,inv_smul_smul]
  have hm := H.mul_mem h.property (hstab _ _ hfix)
  rw [mul_inv_cancel_left] at hm
  exact hm

variable [Countable G] [MeasurableSpace X] [MeasurableEq X] [H.FiniteIndex]

private theorem orbitToSubgroup_controlled (BG : ProperGroupBalls G) (BH : ProperGroupBalls H)
    (hact : BorelAction G X) (hstab : ∀ (x : X) (g : G), g • x = x → g ∈ H)
    (r : ℕ) : ∃ s, ∀ ⦃x y : X⦄, (BG.toBorelNear hact).near r x y →
      (BH.toBorelNear (fun h => hact h.val)).near s (orbitToSubgroup H x) (orbitToSubgroup H y) := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  let C : Finset G := (BG.ball r).biUnion fun g => (Finset.univ : Finset (RightCosets H)).biUnion
    fun i => (Finset.univ : Finset (RightCosets H)).image fun j =>
      rightCosetRepresentative H j * g * (rightCosetRepresentative H i)⁻¹
  have hC : (Subtype.val ⁻¹' (C : Set G) : Set H).Finite :=
    C.finite_toSet.preimage (fun a _ b _ hab => Subtype.ext hab)
  let C' := hC.toFinset
  obtain ⟨s,hs⟩ := BH.finite_subset C'
  refine ⟨s,?_⟩
  rintro x y ⟨g,hg,hxy⟩
  let i := normalizingCoset H x
  let j := normalizingCoset H y
  let w := rightCosetRepresentative H j * g * (rightCosetRepresentative H i)⁻¹
  let h : H := ⟨w,normalization_displacement_mem H hstab g hxy⟩
  have hw : w ∈ C :=
    Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩⟩
  refine ⟨h,hs h ((Set.Finite.mem_toFinset hC).mpr hw),?_⟩
  change w • (rightCosetRepresentative H i • x) = rightCosetRepresentative H j • y
  dsimp [w]
  rw [mul_smul,inv_smul_smul,mul_smul,hxy]

/-- If all stabilizers lie in the subgroup, the bound on ordinary dimension
for induced cores is independent of the finite index. -/
theorem ordinaryAsdim_finiteIndex_action_of_stabilizers (BG : ProperGroupBalls G)
    (BH : ProperGroupBalls H) (hact : BorelAction G X)
    (hstab : ∀ (x : X) (g : G), g • x = x → g ∈ H) {K : Set X} (d : ℕ)
    (hK : BorelAsdimLE (BH.toBorelNear (fun h => hact h.val)) d K) :
    OrdinaryAsdimLE (BG.toBorelNear hact) d (finiteCosetCore H K) := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  apply ordinaryAsdim_pullback_finite_fibers _ _ (orbitToSubgroup H) _ _ _ (ordinaryAsdim_of_borel _ hK)
  · exact fun x hx => hx (normalizingCoset H x)
  · intro r
    obtain ⟨s,hs⟩ := orbitToSubgroup_controlled H BG BH hact hstab r
    exact ⟨s,fun _ _ _ _ h => hs h⟩
  · refine ⟨Fintype.card (RightCosets H),fun y => ?_⟩
    let T : Finset X := (Finset.univ : Finset (RightCosets H)).image fun i =>
      (rightCosetRepresentative H i)⁻¹ • y
    refine ⟨T,Finset.card_image_le.trans_eq Finset.card_univ,fun x _ hxy => ?_⟩
    refine Finset.mem_image.mpr ⟨normalizingCoset H x,Finset.mem_univ _,?_⟩
    rw [← hxy]
    exact inv_smul_smul _ _

variable [StandardBorelSpace X]

/-- The sharp Borel dimension transfer for actual finite-index subgroup actions. -/
theorem asdim_finiteIndex_action_of_stabilizers (BG : ProperGroupBalls G)
    (BH : ProperGroupBalls H) (hact : BorelAction G X)
    (hstab : ∀ (x : X) (g : G), g • x = x → g ∈ H) {K : Set X}
    (hKm : MeasurableSet K) (d : ℕ)
    (hK : BorelAsdimLE (BH.toBorelNear (fun h => hact h.val)) d K) :
    BorelAsdimLE (BG.toBorelNear hact) d (finiteCosetCore H K) :=
  (BG.toBorelNear hact).asdim_of_ordinary_of_borelFinite
    (ordinaryAsdim_finiteIndex_action_of_stabilizers H BG BH hact hstab d hK)
    (asdim_finiteIndex_action H BG BH hact hKm d hK)

theorem coreExhaustion_finiteIndex_action_of_stabilizers (BG : ProperGroupBalls G)
    (BH : ProperGroupBalls H) (hact : BorelAction G X)
    (hstab : ∀ (x : X) (g : G), g • x = x → g ∈ H)
    (hcores : HasCoreExhaustion (BH.toBorelNear (fun h => hact h.val))) :
    HasCoreExhaustion (BG.toBorelNear hact) := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨d,K,hKm,hK,hKcov,hKd⟩ := hcores
  refine ⟨d,fun n => finiteCosetCore H (K n),
    (finiteCosetCore_mono H).comp hKm, fun n => measurableSet_finiteCosetCore H hact (hK n),?_,
    fun n => asdim_finiteIndex_action_of_stabilizers H BG BH hact hstab (hK n) d (hKd n)⟩
  intro x
  choose n hn using fun i : RightCosets H => hKcov (rightCosetRepresentative H i • x)
  exact ⟨Finset.univ.sup n,fun i => hKm (Finset.le_sup (Finset.mem_univ i)) (hn i)⟩

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.FiniteIndexSharp

-- BEGIN COMPLETE MODULE HirschProof.ProjectedStabilizers
section
                                   

set_option autoImplicit false
noncomputable section

namespace LocalHirschHyperfinite

open Set

variable {G A X : Type*} [Group G] [CommGroup A] [MulAction G X]

def projectedStabilizer (projection : G →* A) (x : X) : Subgroup A :=
  (MulAction.stabilizer G x).map projection

theorem mem_projectedStabilizer (projection : G →* A) (x : X) (a : A) :
    a ∈ projectedStabilizer projection x ↔ ∃ g : G, g • x = x ∧ projection g = a := Iff.rfl

theorem projectedStabilizer_smul (projection : G →* A) (x : X) (k : G) :
    projectedStabilizer projection (k • x) = projectedStabilizer projection x := by
  have Hincl (x : X) (k : G) : projectedStabilizer projection x ≤ projectedStabilizer projection (k • x) := by
    intro a ha
    rcases (mem_projectedStabilizer projection x a).mp ha with ⟨g,hg,hga⟩
    refine ⟨k*g*k⁻¹, ?_, ?_⟩
    · apply MulAction.mem_stabilizer_iff.mpr
      rw [mul_smul,inv_smul_smul,mul_smul,hg]
    · rw [map_mul,map_mul,map_inv, mul_right_comm (projection k) (projection g) (projection k)⁻¹, mul_inv_cancel, one_mul, hga]
  exact le_antisymm (by simpa only [inv_smul_smul] using Hincl (k • x) k⁻¹) (Hincl x k)

def stabilizerFixedSet (D : Subgroup G) : Set X :=
  {x | D ≤ MulAction.stabilizer G x}

theorem mem_stabilizerFixedSet_iff (D : Subgroup G) (x : X) :
    x ∈ (stabilizerFixedSet D : Set X) ↔ ∀ g : D, g.val • x = x := by
  exact ⟨fun h g => h g.property,fun h g hg => h ⟨g,hg⟩⟩

theorem exists_fg_projected_witness (projection : G →* A) {x : X}
    {P : Subgroup A} (hP : P.FG) (hx : projectedStabilizer projection x = P) :
    ∃ D : Subgroup G, D.FG ∧ D ≤ MulAction.stabilizer G x ∧ D.map projection = P := by
  classical
  obtain ⟨S,hS⟩ := hP
  have hpre (a : ↑S) : ∃ g : G, g • x = x ∧ projection g = a.val := by
    apply (mem_projectedStabilizer projection x a.val).mp
    rw [hx,← hS]
    exact Subgroup.subset_closure a.property
  choose g hfix hmap using hpre
  let T : Finset G := S.attach.image g
  refine ⟨Subgroup.closure (T : Set G),⟨T,rfl⟩,(Subgroup.closure_le (MulAction.stabilizer G x)).mpr ?_,?_⟩
  · intro v hv
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
    exact hfix a
  · rw [projection.map_closure,← hS]
    congr 1
    ext a
    constructor
    · rintro ⟨v,hv,rfl⟩
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
      rw [hmap]
      exact u.property
    · intro ha
      let u : ↑S := ⟨a,ha⟩
      exact ⟨g u,Finset.mem_image_of_mem g (Finset.mem_attach _ _),hmap u⟩

theorem countable_fg_subgroups (G : Type*) [Group G] [Countable G] :
    Countable {D : Subgroup G // D.FG} := by
  let f (t : Finset G) : {D : Subgroup G // D.FG} := ⟨Subgroup.closure (t : Set G), ⟨t,rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨D,⟨t,ht⟩⟩
    exact ⟨t,Subtype.ext ht⟩
  exact hf.countable

theorem countable_subgroups_of_all_fg (A : Type*) [Group A] [Countable A]
    (hfg : ∀ P : Subgroup A, P.FG) : Countable (Subgroup A) := by
  letI := countable_fg_subgroups A
  have h : Function.Surjective (fun D : {D : Subgroup A // D.FG} => D.val) :=
    fun P => ⟨⟨P,hfg P⟩,rfl⟩
  exact h.countable

section Measurable
variable [Countable G] [Countable A] [MeasurableSpace X] [MeasurableEq X]

omit [Countable A] in
theorem measurableSet_mem_projectedStabilizer (projection : G →* A) (hact : BorelAction G X) (a : A) :
    MeasurableSet {x : X | a ∈ projectedStabilizer projection x} := by
  have heq : {x : X | a ∈ projectedStabilizer projection x} =
      ⋃ g : G, {x : X | g • x = x ∧ projection g = a} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, mem_projectedStabilizer]
  rw [heq]
  apply MeasurableSet.iUnion
  intro g
  by_cases hg : projection g = a
  · simpa only [hg,and_true] using measurableSet_eq_fun (hact g) measurable_id
  · simp [hg]

theorem measurableSet_projectedStabilizer_eq (projection : G →* A) (hact : BorelAction G X) (P : Subgroup A) :
    MeasurableSet {x : X | projectedStabilizer projection x = P} := by
  have heq : {x : X | projectedStabilizer projection x = P} =
      ⋂ a : A, {x : X | a ∈ projectedStabilizer projection x ↔ a ∈ P} := by
    ext x
    simp only [mem_setOf_eq,mem_iInter]
    exact ⟨fun h a => by rw [h],fun h => Subgroup.ext h⟩
  rw [heq]
  apply MeasurableSet.iInter
  intro a
  by_cases ha : a ∈ P
  · simpa only [ha,iff_true] using measurableSet_mem_projectedStabilizer projection hact a
  · have he : {x : X | a ∈ projectedStabilizer projection x ↔ a ∈ P} =
        {x : X | a ∈ projectedStabilizer projection x}ᶜ := by ext x; simp [ha]
    rw [he]
    exact (measurableSet_mem_projectedStabilizer projection hact a).compl

omit [Countable A] in
theorem measurableSet_stabilizerFixedSet (hact : BorelAction G X) (D : Subgroup G) :
    MeasurableSet (stabilizerFixedSet D : Set X) := by
  have heq : (stabilizerFixedSet D : Set X) = ⋂ g : D, {x : X | g.val • x = x} := by
    ext x
    simp only [mem_stabilizerFixedSet_iff,mem_iInter,mem_setOf_eq]
  rw [heq]
  exact MeasurableSet.iInter fun g => measurableSet_eq_fun (hact g.val) measurable_id

end Measurable

def projectedSup (projection : G →* A) (P P' : Subgroup A) : Subgroup G := (P ⊔ P').comap projection

def projectedComplement (projection : G →* A) (P' : Subgroup A) : Subgroup G := P'.comap projection

omit [MulAction G X] in
theorem projectedComplement_le (projection : G →* A) (P P' : Subgroup A) :
    projectedComplement projection P' ≤ projectedSup projection P P' := fun _ h => Subgroup.mem_sup_right h

omit [MulAction G X] in
theorem finiteIndex_projectedSup (projection : G →* A) (hprojection : Function.Surjective projection)
    (P P' : Subgroup A) [(P ⊔ P').FiniteIndex] : (projectedSup projection P P').FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, projectedSup, Subgroup.index_comap_of_surjective _ hprojection]
  exact Subgroup.index_ne_zero_of_finite

theorem stabilizer_le_projectedSup (projection : G →* A) {P P' : Subgroup A} {x : X}
    (hx : projectedStabilizer projection x = P) : MulAction.stabilizer G x ≤ projectedSup projection P P' := by
  intro g hg
  change projection g ∈ P ⊔ P'
  apply Subgroup.mem_sup_left
  rw [← hx]
  exact Subgroup.mem_map_of_mem projection hg

/-- Cancellation by one stabilizing element works uniformly on the whole fixed set. -/
theorem exists_cancellation_move (projection : G →* A) {P P' : Subgroup A} {D : Subgroup G}
    (hD : D.map projection = P) (g : projectedSup projection P P') :
    ∃ h : projectedComplement projection P', ∀ x ∈ (stabilizerFixedSet D : Set X), h • x = g • x := by
  have hg : projection g.val ∈ P ⊔ P' := g.property
  obtain ⟨a,ha,b,hb,hab⟩ := Subgroup.mem_sup.mp hg
  have hmap : a ∈ D.map projection := hD.symm ▸ ha
  obtain ⟨d,hd,hdproject⟩ := Subgroup.mem_map.mp hmap
  have hmem : g.val*d⁻¹ ∈ projectedComplement projection P' := by
    change projection (g.val*d⁻¹) ∈ P'
    rw [map_mul,map_inv,hdproject,← hab, mul_right_comm a b a⁻¹,mul_inv_cancel,one_mul]
    exact hb
  refine ⟨⟨g.val*d⁻¹,hmem⟩,fun x hx => ?_⟩
  change (g.val*d⁻¹) • x = g.val • x
  have hfix := (mem_stabilizerFixedSet_iff D x).mp hx ⟨d⁻¹,D.inv_mem hd⟩
  simp only [mul_smul,hfix]

theorem orbitRel_projectedSup_iff (projection : G →* A) {P P' : Subgroup A} {x y : X}
    (hx : projectedStabilizer projection x = P) :
    orbitRel (projectedSup projection P P') x y ↔ orbitRel (projectedComplement projection P') x y := by
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨h,hh⟩ := exists_cancellation_move (X := X) projection (P' := P') hx g
    have hf : x ∈ (stabilizerFixedSet (MulAction.stabilizer G x) : Set X) :=
      (mem_stabilizerFixedSet_iff (MulAction.stabilizer G x) x).mpr fun g => g.property
    exact ⟨h,(hh x hf).trans hg⟩
  · rintro ⟨g,hg⟩
    exact ⟨⟨g.val,projectedComplement_le projection P P' g.property⟩,hg⟩

theorem projectedComplement_stabilizer_image (projection : G →* A) {P P' : Subgroup A} {x : X}
    (hx : projectedStabilizer projection x = P) (hdisj : Disjoint P P')
    (g : projectedComplement projection P') (hg : g • x = x) : projection g.val = 1 := by
  have hP : projection g.val ∈ P := hx ▸ (Subgroup.mem_map_of_mem projection hg)
  have hmem : projection g.val ∈ P ⊓ P' := ⟨hP,g.property⟩
  rw [disjoint_iff_inf_le] at hdisj
  exact Subgroup.mem_bot.mp (hdisj hmem)

variable [Countable G] [MeasurableSpace X] [MeasurableEq X]

/-- The two subgroup metrics coarsely agree on the chosen fixed set. Their test
elements are still taken in the whole acting groups. -/
theorem asdim_projectedSup_of_fixedSet (projection : G →* A) {P P' : Subgroup A} {D : Subgroup G}
    (hD : D.map projection = P)
    (B₀ : ProperGroupBalls (projectedSup projection P P')) (B₁ : ProperGroupBalls (projectedComplement projection P'))
    (hact : BorelAction G X) {K : Set X} (hfix : K ⊆ stabilizerFixedSet D) (d : ℕ)
    (hK : BorelAsdimLE (B₁.toBorelNear (fun g => hact g.val)) d K) :
    BorelAsdimLE (B₀.toBorelNear (fun g => hact g.val)) d K := by
  classical
  let DB := B₀.toBorelNear (fun g => hact g.val)
  let B := B₁.toBorelNear (fun g => hact g.val)
  choose c hc using fun g : projectedSup projection P P' => exists_cancellation_move (X := X) projection hD g
  let incl (g : projectedComplement projection P') : projectedSup projection P P' :=
    ⟨g.val,projectedComplement_le projection P P' g.property⟩
  intro r
  obtain ⟨s,hs⟩ := B₁.finite_subset ((B₀.ball r).image c)
  obtain ⟨U,R,hU,hUm,hUcov,hUb⟩ := hK s
  obtain ⟨R',hR'⟩ := B₀.finite_subset ((B₁.ball R).image incl)
  refine ⟨U,R',hU,hUm,hUcov,?_⟩
  intro i x y hxy
  have hm : B.comp s (U i) x y := by
    apply DB.comp_mono_near B _ hxy
    rintro u v hu hv ⟨g,hg,rfl⟩
    exact ⟨c g,hs _ (Finset.mem_image_of_mem _ hg),hc g u (hfix (hU i hu))⟩
  obtain ⟨g,hg,hgy⟩ := hUb i hm
  exact ⟨incl g,hR' _ (Finset.mem_image_of_mem _ hg),hgy⟩

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.ProjectedStabilizers

-- BEGIN COMPLETE MODULE HirschProof.PhysicalIsolators
section
                                    
                                       

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite

variable {G Q X : Type*} [Group G] [Group Q] [MulAction G X]

def stabilizerImageIn (π : G →* Q) (N : Subgroup Q) (x : X) : Subgroup N :=
  ((MulAction.stabilizer G x).map π).subgroupOf N

theorem mem_stabilizerImageIn (π : G →* Q) (N : Subgroup Q) (x : X) (a : N) :
    a ∈ stabilizerImageIn π N x ↔ ∃ g : G, g • x = x ∧ π g = a.val := Iff.rfl

variable (π : G →* Q) (N : Subgroup Q) [Group.IsNilpotent N]

def physicalIsolator (x : X) : Subgroup N := nilpotentIsolator (stabilizerImageIn π N x)

theorem stabilizerImageIn_smul [N.Normal] (g : G) (x : X) :
    stabilizerImageIn π N (g • x) =
      (stabilizerImageIn π N x).map (MulAut.conjNormal (π g)).toMonoidHom := by
  let e : MulAut N := MulAut.conjNormal (π g)
  ext a
  rw [Subgroup.mem_map_equiv]
  constructor
  · rintro ⟨h,hh,hp⟩
    change h • (g • x) = g • x at hh
    refine ⟨g⁻¹*h*g,?_,?_⟩
    · change (g⁻¹*h*g) • x = x
      simp only [mul_smul,hh,inv_smul_smul]
    · rw [map_mul,map_mul,map_inv,hp]
      exact (MulAut.conjNormal_symm_apply (π g) a).symm
  · rintro ⟨h,hh,hp⟩
    change h • x = x at hh
    refine ⟨g*h*g⁻¹,?_,?_⟩
    · change (g*h*g⁻¹) • (g • x) = g • x
      simp only [mul_smul,inv_smul_smul,hh]
    · rw [map_mul,map_mul,map_inv,hp]
      change π g * (↑((MulAut.conjNormal (π g)).symm a) : Q) * (π g)⁻¹ = a.val
      rw [MulAut.conjNormal_symm_apply]
      group

theorem physicalIsolator_smul [N.Normal] (g : G) (x : X) :
    physicalIsolator π N (g • x) = (physicalIsolator π N x).map
      (MulAut.conjNormal (π g)).toMonoidHom := by
  unfold physicalIsolator
  rw [stabilizerImageIn_smul π N g x,nilpotentIsolator_map_equiv]

theorem countable_physicalIsolators [Countable Q] (h : HasFiniteIsolatorWitness N) :
    (range (physicalIsolator (X := X) π N)).Countable := by
  apply (countable_range_nilpotentIsolator h).mono
  rintro y ⟨x,hx⟩
  exact ⟨stabilizerImageIn π N x,hx⟩

theorem measurableSet_physicalIsolator [Countable G] [Countable Q]
    [MeasurableSpace X] [StandardBorelSpace X] (hact : BorelAction G X) (I : Subgroup N) :
    MeasurableSet {x : X | physicalIsolator π N x = I} := by
  apply measurableSet_eq_nilpotentIsolator (stabilizerImageIn π N) _ I
  intro a
  have he : {x : X | a ∈ stabilizerImageIn π N x} =
      ⋃ g : G, ⋃ _ : π g = a.val, {x : X | g • x = x} := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion,mem_stabilizerImageIn]
    exact exists_congr (fun _ => ⟨fun h => ⟨h.2,h.1⟩,fun ⟨hp,hs⟩ => ⟨hs,hp⟩⟩)
  rw [he]
  exact MeasurableSet.iUnion (fun g => MeasurableSet.iUnion (fun _ =>
    measurableSet_eq_fun (hact g) measurable_id))

/-- Every physical displacement inside one isolator fiber lies in its projected
normalizer. -/
theorem projected_mem_normalizer_of_same_isolator [N.Normal] {g : G} {x : X}
    {I : Subgroup N} (hx : physicalIsolator π N x = I)
    (hy : physicalIsolator π N (g • x) = I) :
    π g ∈ Subgroup.normalizer (I.map N.subtype : Set Q) := by
  rw [physicalIsolator_smul π N g x,hx] at hy
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  let f := (MulAut.conj (π g)).toMonoidHom
  change ((I.map N.subtype).map f : Set Q) = _
  rw [Subgroup.map_map]
  have hcomp : f.comp N.subtype = N.subtype.comp (MulAut.conjNormal (π g)).toMonoidHom := by
    ext a
    exact (MulAut.conjNormal_apply (π g) a).symm
  rw [hcomp,← Subgroup.map_map,hy]

/-- A finite isolator witness lifts to a finitely generated stabilizing
subgroup of the physical acting group. -/
theorem exists_fg_stabilizer_isolator_witness (hN : HasFiniteIsolatorWitness N) (x : X) :
    ∃ D : Subgroup G, D.FG ∧ D ≤ MulAction.stabilizer G x ∧
      nilpotentIsolator ((D.map π).subgroupOf N) = physicalIsolator π N x := by
  obtain ⟨J,hJ,hJf,hJiso⟩ := hN (stabilizerImageIn π N x)
  have hm : J.map N.subtype ≤ (MulAction.stabilizer G x).map π := by
    rintro _ ⟨a,ha,rfl⟩
    exact hJ ha
  obtain ⟨D,hD,hDf,hDm⟩ := exists_fg_subgroup_map_eq π (MulAction.stabilizer G x)
    (J.map N.subtype) hm (IsLocallyFiniteGroup.fg_map N.subtype J hJf)
  refine ⟨D,hDf,hD,?_⟩
  rwa [hDm,← Subgroup.comap_subtype,Subgroup.comap_map_eq_self_of_injective N.subtype_injective]

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.PhysicalIsolators

-- BEGIN COMPLETE MODULE HirschProof.LatticeComplements
section
                                       
                                          
                                      
                                                    
                                           
                                                          

set_option autoImplicit false
noncomputable section

namespace LocalHirschHyperfinite

open Set Module
open scoped BigOperators

variable {M I : Type*} [AddCommGroup M] [Fintype I]

theorem lattice_subgroup_fg (b : Basis I ℤ M) (P : AddSubgroup M) : P.FG := by
  obtain ⟨n, snf⟩ := P.toIntSubmodule.smithNormalForm b
  have hfinite : Module.Finite ℤ P.toIntSubmodule := Module.Finite.of_basis snf.bN
  have hfg : P.toIntSubmodule.FG := Module.Finite.iff_fg.mp hfinite
  exact (Submodule.fg_iff_addSubgroup_fg P.toIntSubmodule).mp hfg

/-- The unused directions of a Smith basis give an independent complement
whose sum with the given lattice subgroup has finite index. -/
theorem lattice_exists_finiteIndex_complement (b : Basis I ℤ M) (P : AddSubgroup M) :
    ∃ Q : AddSubgroup M, Disjoint P Q ∧ (P ⊔ Q).FiniteIndex := by
  classical
  let N := P.toIntSubmodule
  obtain ⟨n,snf⟩ := N.smithNormalForm b
  let Q : Submodule ℤ M := ⨅ j : Fin n, LinearMap.ker (snf.bM.coord (snf.f j))
  let V := N ⊔ Q
  let m : ℤ := ∏ j : Fin n, snf.a j
  have ha (j : Fin n) : snf.a j ≠ 0 := by
    intro h
    have he := snf.snf j
    rw [h, zero_smul] at he
    exact snf.bN.ne_zero j (Subtype.ext he)
  have hm : m ≠ 0 := by
    dsimp [m]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => ha j
  have hdisj : Disjoint P Q.toAddSubgroup := by
    rw [disjoint_iff_inf_le]
    intro x hx
    change x ∈ P ∧ x ∈ Q at hx
    have hxN : x ∈ N := hx.1
    have hxQ := (Submodule.mem_iInf _).mp hx.2
    apply AddSubgroup.mem_bot.mpr
    apply snf.bM.repr.injective
    ext i
    simp only [map_zero, Finsupp.zero_apply]
    by_cases hi : i ∈ range snf.f
    · obtain ⟨j,rfl⟩ := hi
      exact hxQ j
    · exact snf.repr_eq_zero_of_notMem_range ⟨x,hxN⟩ hi
  have hscaled (i : I) : m • snf.bM i ∈ V := by
    by_cases hi : i ∈ range snf.f
    · obtain ⟨j,rfl⟩ := hi
      obtain ⟨c,hc⟩ := Finset.dvd_prod_of_mem snf.a (Finset.mem_univ j)
      change m = snf.a j*c at hc
      have hj : snf.a j • snf.bM (snf.f j) ∈ N := by
        rw [← snf.snf j]
        exact (snf.bN j).property
      rw [hc,mul_comm,mul_smul]
      exact (show N ≤ V from le_sup_left) (N.smul_mem c hj)
    · apply (show Q ≤ V from le_sup_right)
      apply Q.smul_mem
      apply (Submodule.mem_iInf _).mpr
      intro j
      change snf.bM.repr (snf.bM i) (snf.f j) = 0
      have he : snf.f j ≠ i := fun h => hi ⟨j,h⟩
      simp [snf.bM.repr_self, he]
  let D : AddSubgroup (I → ℤ) := AddSubgroup.pi Set.univ (fun _ => AddSubgroup.zmultiples m)
  let e : M ≃+ (I → ℤ) := snf.bM.equivFun.toAddEquiv
  let E : AddSubgroup M := D.comap e.toAddMonoidHom
  have hEidx : E.index ≠ 0 := by
    change (D.comap e.toAddMonoidHom).index ≠ 0
    rw [AddSubgroup.index_comap_of_surjective D e.surjective]
    dsimp [D]
    rw [AddSubgroup.index_pi, Int.index_zmultiples]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => Int.natAbs_ne_zero.mpr hm
  have hEV : E ≤ V.toAddSubgroup := by
    intro x hx
    have htest (i : I) : snf.bM.repr x i ∈ AddSubgroup.zmultiples m := by
      exact ((AddSubgroup.mem_pi Set.univ).mp (show e x ∈ D from hx)) i (mem_univ i)
    change x ∈ V
    rw [← snf.bM.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    obtain ⟨c,hc⟩ := AddSubgroup.mem_zmultiples_iff.mp (htest i)
    rw [← hc, zsmul_eq_mul, mul_smul]
    exact V.smul_mem c (hscaled i)
  have hVindex : V.toAddSubgroup.index ≠ 0 := by
    intro h
    have hd := AddSubgroup.index_dvd_of_le hEV
    rw [h, zero_dvd_iff] at hd
    exact hEidx hd
  have heq : V.toAddSubgroup = P ⊔ Q.toAddSubgroup := by
    simpa only [AddSubgroup.toIntSubmodule_symm,AddSubgroup.toIntSubmodule_toAddSubgroup,N,V] using
      (AddSubgroup.toIntSubmodule.symm : Submodule ℤ M ≃o AddSubgroup M).map_sup N Q
  exact ⟨Q.toAddSubgroup,hdisj,AddSubgroup.finiteIndex_iff.mpr (heq ▸ hVindex)⟩

theorem multiplicative_lattice_exists_finiteIndex_complement (b : Basis I ℤ M)
    (P : Subgroup (Multiplicative M)) :
    ∃ Q : Subgroup (Multiplicative M), Disjoint P Q ∧ (P ⊔ Q).FiniteIndex := by
  let p : AddSubgroup M := AddSubgroup.toSubgroup.symm P
  obtain ⟨q,hdisj,hidx⟩ := lattice_exists_finiteIndex_complement b p
  refine ⟨q.toSubgroup,?_,?_⟩
  · rw [disjoint_iff_inf_le] at hdisj ⊢
    intro x hx
    apply Subgroup.mem_bot.mpr
    change x.toAdd = 0
    exact AddSubgroup.mem_bot.mp (hdisj (show x.toAdd ∈ p ⊓ q from hx))
  · have heq : (p ⊔ q).toSubgroup = P ⊔ q.toSubgroup := by
      simpa only [p, OrderIso.apply_symm_apply] using AddSubgroup.toSubgroup.map_sup p q
    apply Subgroup.finiteIndex_iff.mpr
    rw [← heq,AddSubgroup.index_toSubgroup]
    exact AddSubgroup.finiteIndex_iff.mp hidx

theorem multiplicative_lattice_subgroup_fg (b : Basis I ℤ M)
    (P : Subgroup (Multiplicative M)) : P.FG := by
  let p : AddSubgroup M := AddSubgroup.toSubgroup.symm P
  have hp := (AddSubgroup.fg_iff_mul_fg p).mp (lattice_subgroup_fg b p)
  simpa only [p,OrderIso.apply_symm_apply] using hp

theorem integerLattice_subgroup_fg (e : ℕ) (P : Subgroup (Multiplicative (Fin e → ℤ))) : P.FG :=
  multiplicative_lattice_subgroup_fg (Basis.ofEquivFun (LinearEquiv.refl ℤ (Fin e → ℤ))) P

theorem integerLattice_exists_finiteIndex_complement (e : ℕ)
    (P : Subgroup (Multiplicative (Fin e → ℤ))) :
    ∃ Q : Subgroup (Multiplicative (Fin e → ℤ)), Disjoint P Q ∧ (P ⊔ Q).FiniteIndex :=
  multiplicative_lattice_exists_finiteIndex_complement
    (Basis.ofEquivFun (LinearEquiv.refl ℤ (Fin e → ℤ))) P

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.LatticeComplements

-- BEGIN COMPLETE MODULE HirschProof.ProjectedCoreTransfer
section
                                     
                                

set_option autoImplicit false
noncomputable section

namespace LocalHirschHyperfinite

open Set

variable {G A X : Type*} [Group G] [CommGroup A] [MulAction G X]
variable [Countable G] [MeasurableSpace X] [MeasurableEq X]

/-- A controlled exhaustion that retains its particular dimension bound. -/
def HasCoreExhaustionLE (D : BorelNear X) (d : ℕ) : Prop :=
  ∃ K : ℕ → Set X, Monotone K ∧ (∀ n, MeasurableSet (K n)) ∧
    (∀ x, ∃ n, x ∈ K n) ∧ ∀ n, BorelAsdimLE D d (K n)

omit [MeasurableEq X] in
theorem coreExhaustion_of_le (D : BorelNear X) (d : ℕ) (h : HasCoreExhaustionLE D d) :
    HasCoreExhaustion D := ⟨d,h⟩

omit [MeasurableEq X] in
/-- Exhaust finitely many of the invariant pieces at each step, retaining their common bound. -/
theorem coreExhaustionLE_of_invariant_pieces (D : BorelNear X)
    (d : ℕ) (P : ℕ → Set X) (V : ℕ → ℕ → Set X)
    (hVP : ∀ j n, V j n ⊆ P j)
    (hsep : ∀ j k, ∀ x ∈ P j, ∀ y ∈ P k, (∃ r, D.near r x y) → j = k)
    (hVmono : ∀ j, Monotone (V j)) (hVm : ∀ j n, MeasurableSet (V j n))
    (hcov : ∀ x : X, ∃ j n, x ∈ V j n) (hV : ∀ j n, BorelAsdimLE D d (V j n)) :
    HasCoreExhaustionLE D d := by
  let W (n : ℕ) := ⋃ j ∈ Finset.range (n+1), V j n
  refine ⟨W,?_,fun n => MeasurableSet.iUnion (fun j =>
    MeasurableSet.iUnion (fun _ : j ∈ Finset.range (n+1) => hVm j n)),?_,?_⟩
  · intro n m hnm x hx
    simp only [W,mem_iUnion] at hx ⊢
    obtain ⟨j,hj,hx⟩ := hx
    exact ⟨j,Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le (Nat.succ_le_succ hnm)),
      hVmono j hnm hx⟩
  · intro x
    obtain ⟨j,n,hx⟩ := hcov x
    refine ⟨max j n,?_⟩
    simp only [W,mem_iUnion]
    exact ⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le (le_max_left j n)),
      hVmono j (le_max_right j n) hx⟩
  · intro n
    exact asdim_finset_invariant_union D (Finset.range (n+1)) P (fun j => V j n)
      (fun j _ => hVP j n) (fun j _ k _ => hsep j k) d (fun j _ => hV j n)

omit [MeasurableEq X] in
theorem asdim_empty (D : BorelNear X) (d : ℕ) : BorelAsdimLE D d (∅ : Set X) := by
  intro r
  refine ⟨fun _ => ∅,0,fun _ => subset_rfl,fun _ => MeasurableSet.empty,?_,?_⟩
  · intro x hx
    exact hx.elim
  · intro i x y h
    exact h.1.elim

def orbitSaturation (G : Type*) [Group G] {X : Type*} [MulAction G X] (F : Set X) : Set X :=
  {x | ∃ g : G, g • x ∈ F}

omit [Countable G] [MeasurableSpace X] [MeasurableEq X] in
theorem orbitSaturation_smul_iff (F : Set X) (g : G) (x : X) :
    g • x ∈ orbitSaturation G F ↔ x ∈ orbitSaturation G F := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k*g,?_⟩
    simpa only [mul_smul] using hk
  · rintro ⟨k,hk⟩
    refine ⟨k*g⁻¹,?_⟩
    simpa only [mul_smul,inv_smul_smul] using hk

omit [MeasurableEq X] in
theorem measurableSet_orbitSaturation (hact : BorelAction G X) {F : Set X}
    (hF : MeasurableSet F) : MeasurableSet (orbitSaturation G F) := by
  have heq : orbitSaturation G F = ⋃ g : G, (fun x : X => g • x) ⁻¹' F := by
    ext x
    simp only [orbitSaturation,mem_iUnion,mem_preimage,mem_setOf_eq]
  rw [heq]
  exact MeasurableSet.iUnion fun g => hF.preimage (hact g)

/-- Undo projected-stabilizer cancellation without changing the dimension bound. -/
theorem coreExhaustionLE_projectedSup_of_complement (projection : G →* A)
    (P P' : Subgroup A) (hP : P.FG) (hproj : ∀ x : X, projectedStabilizer projection x = P)
    (B₀ : ProperGroupBalls (projectedSup projection P P'))
    (B₁ : ProperGroupBalls (projectedComplement projection P'))
    (hact : BorelAction G X) (d : ℕ)
    (hcore : HasCoreExhaustionLE (B₁.toBorelNear (fun g => hact g.val)) d) :
    HasCoreExhaustionLE (B₀.toBorelNear (fun g => hact g.val)) d := by
  classical
  obtain ⟨K,hKm,hMK,hKcov,hKd⟩ := hcore
  let G₀ := projectedSup projection P P'
  let act₀ : BorelAction G₀ X := fun g => hact g.val
  let D₀ := B₀.toBorelNear act₀
  let D₁ := B₁.toBorelNear (fun g => hact g.val)
  letI : Countable {H : Subgroup G // H.FG} := countable_fg_subgroups G
  letI : Nonempty {H : Subgroup G // H.FG} :=
    ⟨⟨⊥,⟨∅,by simp⟩⟩⟩
  obtain ⟨L,hL⟩ := exists_surjective_nat {H : Subgroup G // H.FG}
  let F (n : ℕ) : Set X :=
    if (L n).val.map projection = P then stabilizerFixedSet (L n).val else ∅
  let S (n : ℕ) := orbitSaturation G₀ (F n)
  let W (n : ℕ) := S n \ ⋃ j : ℕ, ⋃ _ : j < n, S j
  let U (n j : ℕ) := F n ∩ W n ∩ K j
  let V (n j : ℕ) := D₀.thicken (U n j) j
  have hF (n : ℕ) : MeasurableSet (F n) := by
    by_cases hp : (L n).val.map projection = P
    · simpa only [F,if_pos hp] using measurableSet_stabilizerFixedSet hact (L n).val
    · simp [F,hp]
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_orbitSaturation act₀ (hF n)
  have hW (n : ℕ) : MeasurableSet (W n) :=
    (hS n).diff (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ : j < n => hS j)
  have hU (n j : ℕ) : MeasurableSet (U n j) := ((hF n).inter (hW n)).inter (hMK j)
  have hS_inv (n : ℕ) (g : G₀) (x : X) : g • x ∈ S n ↔ x ∈ S n :=
    orbitSaturation_smul_iff (F n) g x
  have hW_inv (n : ℕ) (g : G₀) (x : X) : g • x ∈ W n ↔ x ∈ W n := by
    simp only [W,mem_diff,mem_iUnion,hS_inv n g x,hS_inv _ g x]
  have hUdim (n j : ℕ) : BorelAsdimLE D₀ d (U n j) := by
    by_cases hp : (L n).val.map projection = P
    · have hfix : U n j ⊆ stabilizerFixedSet (L n).val := by
        intro x hx
        have hx := hx.1.1
        simpa only [F,if_pos hp] using hx
      exact asdim_projectedSup_of_fixedSet projection hp B₀ B₁ hact hfix d
        (D₁.asdim_restrict (hKd j) (hU n j) inter_subset_right)
    · have hu : U n j = ∅ := by simp [U,F,hp]
      rw [hu]
      exact asdim_empty D₀ d
  apply coreExhaustionLE_of_invariant_pieces D₀ d W V
  · intro n j x hx
    obtain ⟨y,hy,⟨g,_,rfl⟩⟩ := hx
    exact (hW_inv n g x).mp hy.1.2
  · intro n m x hx y hy hn
    obtain ⟨r,hnear⟩ := hn
    obtain ⟨g,_,hg⟩ := (B₀.toBorelNear_iff act₀ r x y).mp hnear
    subst y
    have hy' := (hW_inv m g x).mp hy
    have hn : x ∈ S n := hx.1
    have hm : x ∈ S m := hy'.1
    by_contra hnm
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · exact hy'.2 (mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨hlt,hn⟩⟩)
    · exact hx.2 (mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨hgt,hm⟩⟩)
  · intro n j k hjk
    exact (D₀.thicken_mono_set (inter_subset_inter_right _ (hKm hjk)) j).trans (D₀.thicken_mono_radius _ hjk)
  · exact fun n j => D₀.measurableSet_thicken (hU n j) j
  · intro x
    have hall : ∃ n, x ∈ S n := by
      obtain ⟨H,hH,hfix,hmap⟩ := exists_fg_projected_witness projection hP (hproj x)
      obtain ⟨n,hn⟩ := hL ⟨H,hH⟩
      refine ⟨n,1,?_⟩
      simpa only [one_smul,F,hn,if_pos hmap] using (show x ∈ stabilizerFixedSet H from hfix)
    let n := Nat.find hall
    have hxS : x ∈ S n := Nat.find_spec hall
    have hxW : x ∈ W n := by
      refine ⟨hxS,?_⟩
      rintro hx
      obtain ⟨k,hk⟩ := mem_iUnion.mp hx
      obtain ⟨hkj,hk⟩ := mem_iUnion.mp hk
      exact (Nat.find_min hall hkj) hk
    obtain ⟨g,hg⟩ := hxS
    obtain ⟨j,hj⟩ := hKcov (g • x)
    obtain ⟨r,hr⟩ := B₀.exhaustive g
    refine ⟨n,max j r,g • x,⟨⟨hg,(hW_inv n g x).mpr hxW⟩,hKm (le_max_left _ _) hj⟩,?_⟩
    exact B₀.near_smul act₀ (B₀.mono (le_max_right _ _) hr) x
  · exact fun n j => D₀.asdim_thicken (hUdim n j)

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.ProjectedCoreTransfer

-- BEGIN COMPLETE MODULE HirschProof.FixedIsolatorCores
section
                                    
                                        

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite

variable {G Q X : Type*} [Group G] [Group Q] [Countable G] [MulAction G X]
  [MeasurableSpace X] [StandardBorelSpace X]

/-- Countably many Borel sections meeting all orbits give cores with the
same dimension bound. First-hit saturation ensures that the pieces are invariant. -/
theorem coreExhaustionLE_of_orbit_sections (B : ProperGroupBalls G) (hact : BorelAction G X)
    (d : ℕ) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (hHit : ∀ x, ∃ n, x ∈ orbitSaturation G (U n))
    (hDim : ∀ n, BorelAsdimLE (B.toBorelNear hact) d (U n)) :
    HasCoreExhaustionLE (B.toBorelNear hact) d := by
  classical
  let D := B.toBorelNear hact
  let S (n : ℕ) := orbitSaturation G (U n)
  let W (n : ℕ) := S n \ ⋃ m : ℕ, ⋃ _ : m<n, S m
  let K (n j : ℕ) := D.thicken (U n ∩ W n) j
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_orbitSaturation hact (hU n)
  have hW (n : ℕ) : MeasurableSet (W n) := (hS n).diff
    (.iUnion fun m => .iUnion fun _ : m<n => hS m)
  have hInv (n : ℕ) (g : G) (x : X) : g • x ∈ W n ↔ x ∈ W n := by
    simp only [W,S,mem_diff,mem_iUnion,orbitSaturation_smul_iff]
  have hsep (n m : ℕ) (x : X) (hx : x ∈ W n) (hy : x ∈ W m) : n=m := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hh | hh
    · exact hy.2 (mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨hh,hx.1⟩⟩)
    · exact hx.2 (mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨hh,hy.1⟩⟩)
  refine coreExhaustionLE_of_invariant_pieces D d W K ?_ ?_ ?_ ?_ ?_ ?_
  · intro n j x hx
    obtain ⟨y,hy,⟨g,_,rfl⟩⟩ := hx
    exact (hInv n g x).mp hy.2
  · intro n m x hx y hy hNear
    obtain ⟨r,g,_,rfl⟩ := hNear
    exact hsep n m x hx ((hInv m g x).mp hy)
  · intro n i j hij
    exact D.thicken_mono_radius _ hij
  · intro n j
    exact D.measurableSet_thicken ((hU n).inter (hW n)) j
  · intro x
    let n := Nat.find (hHit x)
    have hx : x ∈ W n := by
      refine ⟨Nat.find_spec (hHit x),?_⟩
      simp only [mem_iUnion,not_exists]
      exact fun m hm => Nat.find_min (hHit x) hm
    obtain ⟨g,hg⟩ := hx.1
    have hyW : g • x ∈ W n := (hInv n g x).mpr hx
    obtain ⟨j,hj⟩ := B.exhaustive g
    exact ⟨n,j,g • x,⟨hg,hyW⟩,g,hj,rfl⟩
  · intro n j
    exact D.asdim_thicken (D.asdim_restrict (hDim n) ((hU n).inter (hW n)) inter_subset_left)

/-- In one isolator fiber, it suffices to bound the restricted metric on
the fixed sections of finitely generated stabilizer witnesses. -/
theorem coreExhaustionLE_of_fixed_isolator (π : G →* Q) (N : Subgroup Q) [Group.IsNilpotent N]
    (I : Subgroup N) (hN : HasFiniteIsolatorWitness N)
    (hI : ∀ x : X, physicalIsolator π N x = I)
    (B : ProperGroupBalls G) (hact : BorelAction G X) (d : ℕ)
    (hStage : ∀ D : Subgroup G, D.FG → nilpotentIsolator ((D.map π).subgroupOf N) = I →
      BorelAsdimLE (B.toBorelNear hact) d (stabilizerFixedSet D)) :
    HasCoreExhaustionLE (B.toBorelNear hact) d := by
  classical
  letI : Countable {D : Subgroup G // D.FG} := countable_fg_subgroups G
  letI : Nonempty {D : Subgroup G // D.FG} := ⟨⟨⊥,⟨∅,by simp⟩⟩⟩
  obtain ⟨D,hD⟩ := exists_surjective_nat {D : Subgroup G // D.FG}
  let U (n : ℕ) : Set X := if nilpotentIsolator (((D n).val.map π).subgroupOf N) = I
    then stabilizerFixedSet (D n).val else ∅
  apply coreExhaustionLE_of_orbit_sections B hact d U
  · intro n
    dsimp only [U]
    split
    · exact measurableSet_stabilizerFixedSet hact (D n).val
    · exact MeasurableSet.empty
  · intro x
    obtain ⟨H,hHf,hHx,hHiso⟩ := exists_fg_stabilizer_isolator_witness π N hN x
    obtain ⟨n,hn⟩ := hD ⟨H,hHf⟩
    refine ⟨n,1,?_⟩
    simp only [U,one_smul,hn,Subtype.coe_mk,hHiso,hI x,if_pos rfl]
    exact hHx
  · intro n
    by_cases h : nilpotentIsolator (((D n).val.map π).subgroupOf N) = I
    · simpa only [U,if_pos h] using hStage (D n).val (D n).property h
    · simpa only [U,if_neg h] using asdim_empty (B.toBorelNear hact) d

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.FixedIsolatorCores

-- BEGIN COMPLETE MODULE HirschProof.InvariantSubspaces
section
                                     

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]

/-- Restrict an action to a set preserved by every group element. -/
@[reducible] def invariantSubtypeAction (U : Set X)
    (hU : ∀ g : G, ∀ x ∈ U, g • x ∈ U) : MulAction G U where
  smul g x := ⟨g • x.val,hU g x.val x.property⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

theorem borelAction_invariantSubtype (U : Set X) (hU : ∀ g : G, ∀ x ∈ U, g • x ∈ U)
    (hact : BorelAction G X) :
    letI : MulAction G U := invariantSubtypeAction U hU
    BorelAction G U := by
  intro g
  exact ((hact g).comp measurable_subtype_coe).subtype_mk

theorem measurableEq_subtype (U : Set X) [MeasurableEq X] : MeasurableEq U := by
  constructor
  change MeasurableSet {p : U × U | p.1 = p.2}
  have h := measurableSet_eq_fun
    ((measurable_subtype_coe : Measurable (Subtype.val : U → X)).comp measurable_fst)
    ((measurable_subtype_coe : Measurable (Subtype.val : U → X)).comp measurable_snd)
  simpa only [Function.comp_apply,Subtype.coe_inj] using h

/-- Compare ambient and subtype covers along the measurable inclusion. -/
theorem asdim_image_subtype (D : BorelNear X) {U : Set X} (hU : MeasurableSet U)
    (B : BorelNear U) {V : Set U} (hV : MeasurableSet V) (d : ℕ)
    (hCompare : ∀ r : ℕ, ∃ s : ℕ, ∀ x y : U, D.near r x.val y.val → B.near s x y)
    (hDim : BorelAsdimLE B d V) : BorelAsdimLE D d (Subtype.val '' V) := by
  classical
  by_cases hNon : U.Nonempty
  · let e := MeasurableEmbedding.subtype_coe hU
    obtain ⟨f,hf,hfe⟩ := e.exists_measurable_extend measurable_id
      (fun _ => ⟨⟨hNon.some,hNon.some_mem⟩⟩)
    have hf₀ (x : U) : f x.val = x := congrFun hfe x
    have hin (x : X) (hx : x ∈ Subtype.val '' V) : (f x).val = x := by
      rcases hx with ⟨u,_,rfl⟩
      rw [hf₀]
    refine asdim_pullback_finite_fibers D B f hf (e.measurableSet_image.2 hV) ?_ ?_ ?_ hDim
    · rintro _ ⟨x,hx,rfl⟩
      simpa only [hf₀] using hx
    · intro r
      obtain ⟨s,hs⟩ := hCompare r
      refine ⟨s,?_⟩
      rintro _ _ ⟨x,_,rfl⟩ ⟨y,_,rfl⟩ hxy
      simpa only [hf₀] using hs x y hxy
    · refine ⟨1,fun y => ⟨{y.val},by simp,?_⟩⟩
      intro x hx he
      exact Finset.mem_singleton.mpr ((hin x hx).symm.trans (congrArg Subtype.val he))
  · have hImage : Subtype.val '' V = (∅ : Set X) := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨_,x,_,rfl⟩
      exact hNon ⟨x.val,x.property⟩
    rw [hImage]
    exact asdim_empty D d

variable [Countable G] [StandardBorelSpace X]

/-- A countable cover by bounded-dimensional Borel sets gives a controlled
exhaustion, allowing thickening on the first-hit orbit pieces. -/
theorem coreExhaustionLE_of_countable_cover {A : Type*} [Countable A]
    (B : ProperGroupBalls G) (hact : BorelAction G X) (d : ℕ)
    (V : A → Set X) (hV : ∀ i, MeasurableSet (V i))
    (hCover : ∀ x, ∃ i, x ∈ V i)
    (hDim : ∀ i, BorelAsdimLE (B.toBorelNear hact) d (V i)) :
    HasCoreExhaustionLE (B.toBorelNear hact) d := by
  obtain ⟨e,he⟩ := exists_surjective_nat (Option A)
  let U (n : ℕ) := (e n).elim ∅ V
  apply coreExhaustionLE_of_orbit_sections B hact d U
  · intro n
    cases h : e n with
    | none => simpa only [U,h,Option.elim_none] using MeasurableSet.empty (α := X)
    | some i => simpa only [U,h,Option.elim_some] using hV i
  · intro x
    obtain ⟨i,hi⟩ := hCover x
    obtain ⟨n,hn⟩ := he (some i)
    exact ⟨n,1,by simpa only [U,hn,Option.elim_some,one_smul] using hi⟩
  · intro n
    cases h : e n with
    | none => simpa only [U,h,Option.elim_none] using asdim_empty (B.toBorelNear hact) d
    | some i => simpa only [U,h,Option.elim_some] using hDim i

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.InvariantSubspaces

-- BEGIN COMPLETE MODULE HirschProof.IsolatorStrata
section
                                     
                                   

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite

variable {G Q X : Type*} [Group G] [Group Q] [MulAction G X]
variable (π : G →* Q) (N : Subgroup Q) [N.Normal] [Group.IsNilpotent N]

/-- Physical moves that normalize the chosen isolator in the quotient. -/
def physicalNormalizer (I : Subgroup N) : Subgroup G :=
  (Subgroup.normalizer (I.map N.subtype : Set Q)).comap π

/-- The physical points with the indicated projected stabilizer isolator. -/
def isolatorFiber (I : Subgroup N) : Set X := {x | physicalIsolator π N x = I}

private theorem map_conj_of_normalizer (I : Subgroup N) {a : Q}
    (ha : a ∈ Subgroup.normalizer (I.map N.subtype : Set Q)) :
    I.map (MulAut.conjNormal a).toMonoidHom = I := by
  let f := (MulAut.conj a).toMonoidHom
  have hS := Subgroup.mem_normalizer_iff_conj_image_eq.mp ha
  change ((I.map N.subtype).map f : Set Q) = _ at hS
  have hC : f.comp N.subtype = N.subtype.comp (MulAut.conjNormal a).toMonoidHom := by
    ext x
    exact (MulAut.conjNormal_apply a x).symm
  rw [Subgroup.map_map,hC,← Subgroup.map_map] at hS
  have he : (I.map (MulAut.conjNormal a).toMonoidHom).map N.subtype = I.map N.subtype := SetLike.coe_injective hS
  have h := congrArg (fun S : Subgroup Q => S.comap N.subtype) he
  simpa only [Subgroup.comap_map_eq_self_of_injective N.subtype_injective] using h

theorem isolatorFiber_invariant (I : Subgroup N) (g : physicalNormalizer π N I)
    (x : X) (hx : x ∈ isolatorFiber π N I) : g.val • x ∈ isolatorFiber π N I := by
  change physicalIsolator π N (g.val • x) = I
  rw [physicalIsolator_smul π N g.val x,show physicalIsolator π N x = I from hx]
  exact map_conj_of_normalizer N I g.property

@[reducible] def isolatorFiberAction (I : Subgroup N) :
    MulAction (physicalNormalizer π N I) (isolatorFiber (X := X) π N I) :=
  invariantSubtypeAction (isolatorFiber π N I) (isolatorFiber_invariant π N I)

variable [MeasurableSpace X]

instance isolatorFiber_measurableEq [MeasurableEq X] (I : Subgroup N) :
    MeasurableEq (isolatorFiber (X := X) π N I) := measurableEq_subtype _

theorem borelAction_isolatorFiber (I : Subgroup N) (hact : BorelAction G X) :
    @BorelAction (physicalNormalizer π N I) (isolatorFiber (X := X) π N I)
      _ (isolatorFiberAction (X := X) π N I) _ := by
  intro g
  exact ((hact g.val).comp measurable_subtype_coe).subtype_mk

variable [Countable G] [Countable Q] [StandardBorelSpace X]

private theorem compare_isolatorFiber_near (I : Subgroup N) (B : ProperGroupBalls G)
    (B' : ProperGroupBalls (physicalNormalizer π N I)) (hact : BorelAction G X) :
    letI := isolatorFiberAction (X := X) π N I
    ∀ r, ∃ s, ∀ (x y : isolatorFiber π N I), (B.toBorelNear hact).near r x.val y.val →
      (B'.toBorelNear (borelAction_isolatorFiber π N I hact)).near s x y := by
  classical
  letI := isolatorFiberAction (X := X) π N I
  intro r
  let A := (B.ball r).preimage (Subtype.val : physicalNormalizer π N I → G) Subtype.val_injective.injOn
  obtain ⟨s,hs⟩ := B'.finite_subset A
  refine ⟨s,?_⟩
  rintro x y ⟨g,hg,hxy⟩
  have hNorm : g ∈ physicalNormalizer π N I := projected_mem_normalizer_of_same_isolator π N
    x.property (hxy.symm ▸ y.property)
  let g' : physicalNormalizer π N I := ⟨g,hNorm⟩
  exact ⟨g',hs g' (Finset.mem_preimage.mpr hg),Subtype.ext hxy⟩

/-- Restrict on each Borel isolator fiber to its normalizing subgroup, then
reassemble its controlled cores in the original metric. -/
theorem coreExhaustionLE_of_isolator_strata (hN : HasFiniteIsolatorWitness N)
    (B : ProperGroupBalls G) (hact : BorelAction G X) (d : ℕ)
    (hEach : ∀ I : Subgroup N,
      letI := isolatorFiberAction (X := X) π N I
      HasCoreExhaustionLE ((ProperGroupBalls.ofCountable (physicalNormalizer π N I)).toBorelNear
        (borelAction_isolatorFiber π N I hact)) d) :
    HasCoreExhaustionLE (B.toBorelNear hact) d := by
  classical
  let A := range (physicalIsolator (X := X) π N)
  letI : Countable A := countable_coe_iff.mpr (countable_physicalIsolators π N hN)
  have hC (I : A) : ∃ V : ℕ → Set (isolatorFiber (X := X) π N I.val),
      (∀ j, MeasurableSet (V j)) ∧ (∀ x, ∃ j, x ∈ V j) ∧
      ∀ j, BorelAsdimLE (B.toBorelNear hact) d (Subtype.val '' V j) := by
    letI := isolatorFiberAction (X := X) π N I.val
    obtain ⟨V,_,hV,hCov,hDim⟩ := hEach I.val
    have hS : MeasurableSet (isolatorFiber (X := X) π N I.val) := measurableSet_physicalIsolator π N hact _
    refine ⟨V,hV,hCov,fun j => ?_⟩
    exact asdim_image_subtype _ hS _ (hV j) d
      (compare_isolatorFiber_near π N I.val B _ hact) (hDim j)
  choose V hV hCov hDim using hC
  let W (j : A × ℕ) := Subtype.val '' V j.1 j.2
  refine coreExhaustionLE_of_countable_cover B hact d W ?_ ?_ (fun j => hDim j.1 j.2)
  · intro j
    exact (MeasurableEmbedding.subtype_coe (measurableSet_physicalIsolator π N hact j.1.val)).measurableSet_image.2
      (hV j.1 j.2)
  · intro x
    let i : A := ⟨physicalIsolator π N x,mem_range_self x⟩
    let y : isolatorFiber π N i.val := ⟨x,rfl⟩
    obtain ⟨j,hj⟩ := hCov i y
    exact ⟨(i,j),y,hj,rfl⟩

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.IsolatorStrata

-- BEGIN COMPLETE MODULE HirschProof.NormalizerQuotients
section
                                 

set_option autoImplicit false

namespace LocalHirschHyperfinite

open Set

variable {G Q X : Type*} [Group G] [Group Q] [MulAction G X]
variable (π : G →* Q) (N : Subgroup Q) [N.Normal] [Group.IsNilpotent N]

abbrev matrixNormalizer (I : Subgroup N) := Subgroup.normalizer (I.map N.subtype : Set Q)

abbrev normalizerIsolator (I : Subgroup N) : Subgroup (matrixNormalizer N I) :=
  (I.map N.subtype).subgroupOf (matrixNormalizer N I)

instance normalizerIsolator_normal (I : Subgroup N) : (normalizerIsolator N I).Normal :=
  Subgroup.normal_in_normalizer

/-- The copy of the isolator inside its normalizer is isomorphic to the
original subgroup of the nilpotent kernel. -/
noncomputable def normalizerIsolatorEquiv (I : Subgroup N) : I ≃* normalizerIsolator N I :=
  (I.equivMapOfInjective N.subtype N.subtype_injective).trans
    (Subgroup.subgroupOfEquivOfLe (I.map N.subtype).le_normalizer).symm

instance normalizerIsolator_nilpotent (I : Subgroup N) : Group.IsNilpotent (normalizerIsolator N I) :=
  Group.nilpotent_of_mulEquiv (normalizerIsolatorEquiv N I)

def normalizerProjection (I : Subgroup N) : physicalNormalizer π N I →* matrixNormalizer N I :=
  { toFun := fun g => ⟨π g.val,g.property⟩
    map_one' := Subtype.ext (map_one π)
    map_mul' := fun g h => Subtype.ext (map_mul π g.val h.val) }

theorem normalizerProjection_surjective (I : Subgroup N) (hπ : Function.Surjective π) :
    Function.Surjective (normalizerProjection π N I) := by
  intro a
  obtain ⟨g,hg⟩ := hπ a.val
  have hG : g ∈ physicalNormalizer π N I := by
    change π g ∈ matrixNormalizer N I
    rw [hg]
    exact a.property
  exact ⟨⟨g,hG⟩,Subtype.ext hg⟩

theorem normalizerProjection_locallyFinite (I : Subgroup N) (hL : IsLocallyFiniteGroup π.ker) :
    IsLocallyFiniteGroup (normalizerProjection π N I).ker := by
  let f : (normalizerProjection π N I).ker →* π.ker :=
    { toFun := fun g => ⟨g.val.val,congrArg Subtype.val g.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply IsLocallyFiniteGroup.of_injective f _ hL
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : π.ker => x.val) h

theorem physicalIsolator_restrict_normalizer (I : Subgroup N) :
    letI := isolatorFiberAction (X := X) π N I
    ∀ x : isolatorFiber (X := X) π N I,
      physicalIsolator (π.comp (physicalNormalizer π N I).subtype) N x = I := by
  letI := isolatorFiberAction (X := X) π N I
  intro x
  have hEq : stabilizerImageIn (π.comp (physicalNormalizer π N I).subtype) N x =
      stabilizerImageIn π N x.val := by
    ext a
    rw [mem_stabilizerImageIn,mem_stabilizerImageIn]
    constructor
    · rintro ⟨g,hx,hg⟩
      exact ⟨g.val,congrArg Subtype.val hx,hg⟩
    · rintro ⟨g,hx,hg⟩
      have hn : g ∈ physicalNormalizer π N I := projected_mem_normalizer_of_same_isolator π N
        x.property (hx.symm ▸ x.property)
      exact ⟨⟨g,hn⟩,Subtype.ext hx,hg⟩
  unfold physicalIsolator
  rw [hEq]
  exact x.property

theorem normalizerProjection_stabilizers_in_isolator (I : Subgroup N)
    (hStab : ∀ g : G, ∀ x : X, g • x = x → π g ∈ N) :
    letI := isolatorFiberAction (X := X) π N I
    ∀ (g : physicalNormalizer π N I) (x : isolatorFiber (X := X) π N I),
      g • x = x → normalizerProjection π N I g ∈ normalizerIsolator N I := by
  intro g x hx
  have hx' : g.val • x.val = x.val := congrArg Subtype.val hx
  let a : N := ⟨π g.val,hStab g.val x.val hx'⟩
  have ha : a ∈ stabilizerImageIn π N x.val := ⟨g.val,hx',rfl⟩
  have hA : a ∈ I := x.property ▸ le_nilpotentIsolator _ ha
  exact ⟨a,hA,rfl⟩

variable [Countable G] [Countable Q] [MeasurableSpace X] [StandardBorelSpace X]

set_option maxHeartbeats 1800000 in
/-- Controlled covers on the fixed sections of the normalizer action
assemble into controlled cores on the whole isolator fiber. -/
theorem coreExhaustionLE_of_normalizer_fixed_witnesses (I : Subgroup N)
    (hN : HasFiniteIsolatorWitness N)
    (hStab : ∀ g : G, ∀ x : X, g • x = x → π g ∈ N)
    (hact : BorelAction G X) (d : ℕ)
    (hStage : letI := isolatorFiberAction (X := X) π N I
      ∀ (Z : Set (isolatorFiber (X := X) π N I)), MeasurableSet Z →
        ∀ (H : Subgroup (normalizerIsolator N I)), H.FG → nilpotentIsolator H = ⊤ →
        (∀ a ∈ H, ∃ g : physicalNormalizer π N I,
          normalizerProjection π N I g = a.val ∧ ∀ x : Z, g • x.val = x.val) →
        BorelAsdimLE ((ProperGroupBalls.ofCountable (physicalNormalizer π N I)).toBorelNear
          (borelAction_isolatorFiber π N I hact)) d Z) :
    letI := isolatorFiberAction (X := X) π N I
    HasCoreExhaustionLE ((ProperGroupBalls.ofCountable (physicalNormalizer π N I)).toBorelNear
      (borelAction_isolatorFiber π N I hact)) d := by
  classical
  let Y := isolatorFiber (X := X) π N I
  let G' := physicalNormalizer π N I
  let Q' := matrixNormalizer N I
  let J := normalizerIsolator N I
  letI : MulAction G' Y := isolatorFiberAction (X := X) π N I
  letI : StandardBorelSpace Y := (measurableSet_physicalIsolator π N hact I).standardBorel
  let π₀ := π.comp G'.subtype
  let p := normalizerProjection π N I
  let hY := borelAction_isolatorFiber π N I hact
  let B := ProperGroupBalls.ofCountable G'
  have hStab' (g : G') (x : Y) : g • x = x → p g ∈ J :=
    normalizerProjection_stabilizers_in_isolator π N I hStab g x
  apply coreExhaustionLE_of_fixed_isolator π₀ N I hN
    (physicalIsolator_restrict_normalizer π N I) B hY d
  intro D hDFG hDI
  let Z : Set Y := stabilizerFixedSet D
  by_cases hNon : Z.Nonempty
  · let x₀ : Z := ⟨hNon.some,hNon.some_mem⟩
    have hFix (g : D) (x : Z) : g.val • x.val = x.val := x.property g.property
    let f : D →* J := (p.comp D.subtype).codRestrict J (fun g => hStab' g.val x₀.val (hFix g x₀))
    let H := f.range
    letI : Group.FG D := (Group.fg_iff_subgroup_fg D).2 hDFG
    have hH : H.FG := by
      change f.range.FG
      rw [MonoidHom.range_eq_map]
      exact IsLocallyFiniteGroup.fg_map f ⊤ Group.FG.out
    have hRoot : nilpotentIsolator H = ⊤ := by
      apply (Subgroup.eq_top_iff' _).2
      intro a
      obtain ⟨b,hb,hba⟩ := a.property
      have hb' : b ∈ nilpotentIsolator ((D.map π₀).subgroupOf N) := hDI.symm ▸ hb
      obtain ⟨m,hm,ha⟩ := (mem_nilpotentIsolator _ b).mp hb'
      obtain ⟨g,hg,heq⟩ := ha
      apply (mem_nilpotentIsolator H a).mpr
      refine ⟨m,hm,⟨⟨g,hg⟩,?_⟩⟩
      apply Subtype.ext
      apply Subtype.ext
      change π g.val = a.val.val^m
      calc
        _ = (b^m).val := heq
        _ = _ := by rw [Subgroup.coe_pow,show b.val = a.val.val from hba]
    have hHfix (a : J) (ha : a ∈ H) : ∃ g : G', p g = a.val ∧ ∀ x : Z, g • x.val = x.val := by
      obtain ⟨g,hg⟩ := ha
      exact ⟨g.val,congrArg Subtype.val hg,hFix g⟩
    exact hStage Z (measurableSet_stabilizerFixedSet hY D) H hH hRoot hHfix
  · change BorelAsdimLE (B.toBorelNear hY) d Z
    rw [Set.not_nonempty_iff_eq_empty.mp hNon]
    exact asdim_empty _ d

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.NormalizerQuotients

-- BEGIN COMPLETE MODULE HirschProof.ProjectedLatticeReassembly
section
                                     
                                        

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite

variable {G A X : Type*} [Group G] [CommGroup A] [MulAction G X]

/-- The invariant fiber on which the projected stabilizer is exactly `P`. -/
def projectedStabilizerSlice (projection : G →* A) (P : Subgroup A) : Set X :=
  {x | projectedStabilizer projection x = P}

theorem projectedStabilizerSlice_invariant (projection : G →* A) (P : Subgroup A)
    (g : G) (x : X) (hx : x ∈ projectedStabilizerSlice projection P) :
    g • x ∈ projectedStabilizerSlice projection P := by
  change projectedStabilizer projection (g • x) = P
  rwa [projectedStabilizer_smul]

@[implicit_reducible] def projectedSliceAction (projection : G →* A) (P : Subgroup A) :
    MulAction G (projectedStabilizerSlice (X := X) projection P) :=
  invariantSubtypeAction _ (projectedStabilizerSlice_invariant projection P)

theorem projectedStabilizer_on_slice (projection : G →* A) (P : Subgroup A) :
    letI := projectedSliceAction (X := X) projection P
    ∀ x : projectedStabilizerSlice (X := X) projection P,
      projectedStabilizer projection x = P := by
  letI := projectedSliceAction (X := X) projection P
  intro x
  have h : projectedStabilizer projection x = projectedStabilizer projection x.val := by
    ext a
    simp only [mem_projectedStabilizer]
    constructor
    · rintro ⟨g,hg,he⟩
      exact ⟨g,congrArg Subtype.val hg,he⟩
    · rintro ⟨g,hg,he⟩
      exact ⟨g,Subtype.ext hg,he⟩
  exact h.trans x.property

variable [Countable G] [MeasurableSpace X] [StandardBorelSpace X]

local instance measurableEqSubtype (U : Set X) : MeasurableEq U where
  measurableSet_diagonal := by
    have hh : MeasurableSet {p : U × U | p.1.val = p.2.val} :=
      measurableSet_eq_fun (measurable_subtype_coe.comp measurable_fst)
        (measurable_subtype_coe.comp measurable_snd)
    convert hh using 1
    ext p
    exact ⟨fun h => congrArg Subtype.val h,Subtype.ext⟩

omit [Countable G] [StandardBorelSpace X] in
theorem borelAction_projectedSlice (projection : G →* A) (P : Subgroup A)
    (hact : BorelAction G X) :
    letI := projectedSliceAction (X := X) projection P
    BorelAction G (projectedStabilizerSlice (X := X) projection P) :=
  borelAction_invariantSubtype _ (projectedStabilizerSlice_invariant projection P) hact

/-- The complement theorem needed on each projected stabilizer fiber. -/
def HasProjectedComplementCores (projection : G →* A)
    (hact : BorelAction G X) (d : ℕ) : Prop :=
  ∀ (P P' : Subgroup A), Disjoint P P' → (P ⊔ P').FiniteIndex →
    ∀ B₁ : ProperGroupBalls (projectedComplement projection P'),
      letI := projectedSliceAction (X := X) projection P
      HasCoreExhaustionLE (B₁.toBorelNear (fun g =>
        borelAction_projectedSlice projection P hact g.val)) d

section FiniteIndex

/-- Sharp finite-index transfer at the given dimension bound. -/
theorem coreExhaustionLE_finiteIndex_action_of_stabilizers (H : Subgroup G)
    [H.FiniteIndex] (B : ProperGroupBalls G) (BH : ProperGroupBalls H) (hact : BorelAction G X)
    (hstab : ∀ (x : X) (g : G), g • x = x → g ∈ H)
    (d : ℕ) (hcores : HasCoreExhaustionLE (BH.toBorelNear (fun h => hact h.val)) d) :
    HasCoreExhaustionLE (B.toBorelNear hact) d := by
  classical
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨K,hKm,hK,hKcov,hKd⟩ := hcores
  refine ⟨fun n => finiteCosetCore H (K n), (finiteCosetCore_mono H).comp hKm,
    fun n => measurableSet_finiteCosetCore H hact (hK n), ?_,
    fun n => asdim_finiteIndex_action_of_stabilizers H B BH hact hstab (hK n) d (hKd n)⟩
  intro x
  choose n hn using fun i : RightCosets H => hKcov (rightCosetRepresentative H i • x)
  exact ⟨Finset.univ.sup n,fun i => hKm (Finset.le_sup (Finset.mem_univ i)) (hn i)⟩

end FiniteIndex

/-- Reassemble the bounded-dimensional complement cores after cancelling
the stabilizer directions and transferring across the finite-index
subgroup. The common dimension bound is retained. -/
theorem coreExhaustionLE_of_projected_complements (projection : G →* A)
    (hπ : Function.Surjective projection)
    (hFG : ∀ P : Subgroup A, P.FG)
    (hComplement : ∀ P : Subgroup A, ∃ P' : Subgroup A,
      Disjoint P P' ∧ (P ⊔ P').FiniteIndex)
    (B : ProperGroupBalls G) (hact : BorelAction G X) (d : ℕ)
    (hCore : HasProjectedComplementCores projection hact d) :
    HasCoreExhaustionLE (B.toBorelNear hact) d := by
  classical
  letI : Countable A := hπ.countable
  letI : Countable (Subgroup A) := countable_subgroups_of_all_fg A hFG
  let Y (P : Subgroup A) := projectedStabilizerSlice (X := X) projection P
  have hY (P : Subgroup A) : MeasurableSet (Y P) :=
    measurableSet_projectedStabilizer_eq projection hact P
  have hFull (P : Subgroup A) :
      letI := projectedSliceAction (X := X) projection P
      HasCoreExhaustionLE (B.toBorelNear (borelAction_projectedSlice projection P hact)) d := by
    letI : MulAction G (Y P) := projectedSliceAction projection P
    letI : StandardBorelSpace (Y P) := (hY P).standardBorel
    let act : BorelAction G (Y P) := borelAction_projectedSlice projection P hact
    obtain ⟨P',hDisj,hF⟩ := hComplement P
    let G₀ := projectedSup projection P P'
    let G₁ := projectedComplement projection P'
    letI : (P ⊔ P').FiniteIndex := hF
    letI : G₀.FiniteIndex := finiteIndex_projectedSup projection hπ P P'
    let B₀ := ProperGroupBalls.ofCountable G₀
    let B₁ := ProperGroupBalls.ofCountable G₁
    have hproj := projectedStabilizer_on_slice (X := X) projection P
    have h₁ : HasCoreExhaustionLE (B₁.toBorelNear (fun g => act g.val)) d :=
      hCore P P' hDisj hF B₁
    have h₀ := coreExhaustionLE_projectedSup_of_complement projection P P'
      (hFG P) hproj B₀ B₁ act d h₁
    exact coreExhaustionLE_finiteIndex_action_of_stabilizers G₀ B B₀ act
      (fun x g hg => stabilizer_le_projectedSup projection (hproj x) hg) d h₀
  have hCover (P : Subgroup A) :
      ∃ V : ℕ → Set X, (∀ n, MeasurableSet (V n)) ∧
        (∀ x ∈ Y P, ∃ n, x ∈ V n) ∧
        (∀ n, BorelAsdimLE (B.toBorelNear hact) d (V n)) := by
    letI : MulAction G (Y P) := projectedSliceAction projection P
    let act : BorelAction G (Y P) := borelAction_projectedSlice projection P hact
    obtain ⟨K,_,hK,hKcov,hKd⟩ := hFull P
    refine ⟨fun n => Subtype.val '' K n, fun n => (MeasurableEmbedding.subtype_coe (hY P)).measurableSet_image.mpr (hK n),
      fun x hx => ?_, fun n => ?_⟩
    · obtain ⟨n,hn⟩ := hKcov ⟨x,hx⟩
      exact ⟨n,⟨⟨x,hx⟩, hn, rfl⟩⟩
    · refine asdim_image_subtype (B.toBorelNear hact) (hY P) (B.toBorelNear act) (hK n) d
        (fun r => ⟨r,fun x y h => ?_⟩) (hKd n)
      obtain ⟨g,hg,he⟩ := (B.toBorelNear_iff hact r x.val y.val).mp h
      exact (B.toBorelNear_iff act r x y).mpr ⟨g,hg,Subtype.ext he⟩
  choose V hMeas hCov hDim using hCover
  apply coreExhaustionLE_of_countable_cover B hact d (fun p : Subgroup A × ℕ => V p.1 p.2)
    (fun p => hMeas p.1 p.2) _ (fun p => hDim p.1 p.2)
  intro x
  obtain ⟨n,hn⟩ := hCov (projectedStabilizer projection x) x rfl
  exact ⟨(projectedStabilizer projection x,n),hn⟩

/-- For the free abelian projection all subgroups are finitely generated
and have a disjoint complement up to finite index. -/
theorem coreExhaustionLE_of_integer_lattice_complements (e : ℕ)
    (projection : G →* Multiplicative (Fin e → ℤ)) (hπ : Function.Surjective projection)
    (B : ProperGroupBalls G) (hact : BorelAction G X) (d : ℕ)
    (hCore : HasProjectedComplementCores projection hact d) :
    HasCoreExhaustionLE (B.toBorelNear hact) d :=
  coreExhaustionLE_of_projected_complements projection hπ
    (integerLattice_subgroup_fg e) (integerLattice_exists_finiteIndex_complement e) B hact d hCore

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.ProjectedLatticeReassembly

-- BEGIN COMPLETE MODULE HirschProof.QuotientRestrictions
section
                                       
                                    

set_option autoImplicit false

namespace LocalHirschHyperfinite

variable {G Q : Type*} [Group G] [Group Q]

def subgroupPreimageProjection (π : G →* Q) (H : Subgroup Q) : H.comap π →* H where
  toFun g := ⟨π g.val,g.property⟩
  map_one' := Subtype.ext (map_one π)
  map_mul' a b := Subtype.ext (map_mul π a.val b.val)

theorem subgroupPreimageProjection_surjective (π : G →* Q) (H : Subgroup Q)
    (hπ : Function.Surjective π) : Function.Surjective (subgroupPreimageProjection π H) := by
  intro x
  obtain ⟨a,ha⟩ := hπ x.val
  have h : a ∈ H.comap π := by change π a ∈ H; rw [ha]; exact x.property
  exact ⟨⟨a,h⟩,Subtype.ext ha⟩

/-- A kernel inherited through a group embedding is locally finite whenever
the original kernel is locally finite. -/
theorem locallyFinite_kernel_of_restriction {A C : Type*} [Group A] [Group C]
    (π : G →* Q) (p : A →* C) (i : A →* G) (hi : Function.Injective i)
    (j : C →* Q) (hcomm : ∀ a, π (i a) = j (p a)) (hL : IsLocallyFiniteGroup π.ker) :
    IsLocallyFiniteGroup p.ker := by
  let f : p.ker →* π.ker :=
    { toFun := fun a => ⟨i a.val,(hcomm a.val).trans ((congrArg j a.property).trans (map_one j))⟩
      map_one' := Subtype.ext (map_one i)
      map_mul' := fun a b => Subtype.ext (map_mul i a.val b.val) }
  apply IsLocallyFiniteGroup.of_injective f _ hL
  intro a b h
  exact Subtype.ext (hi (congrArg (fun x : π.ker => x.val) h))

theorem nilpotent_of_embedding [Group.IsNilpotent Q] (f : G →* Q) (hf : Function.Injective f) :
    Group.IsNilpotent G := Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hf).symm

theorem nilpotent_kernel_of_embedding {A : Type*} [Group A] (q : Q →* A)
    [Group.IsNilpotent q.ker] (ι : G →* Q) (hι : Function.Injective ι) :
    Group.IsNilpotent (q.comp ι).ker := by
  let f : (q.comp ι).ker →* q.ker :=
    { toFun := fun x => ⟨ι x.val,x.property⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun x y => Subtype.ext (map_mul ι x.val y.val) }
  exact nilpotent_of_embedding f (fun _ _ h => Subtype.ext (hι (congrArg (fun z : q.ker => z.val) h)))

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.QuotientRestrictions

-- BEGIN COMPLETE MODULE HirschProof.ChartModel
section
                                 
                                           
                                          
                              
                             
                               
                               

set_option autoImplicit false

open Set Topology TopologicalSpace

namespace LocalHirschHyperfinite
namespace ChartModel

variable {Γ : Type*} [Group Γ] [Countable Γ]

abbrev Layer (Γ : Type*) [Group Γ] := {S : Finset Γ // (1 : Γ) ∉ S}
abbrev Addr (Γ : Type*) [Group Γ] := Layer Γ × Γ
abbrev Palette (cap : Layer Γ → ℕ) (j : Layer Γ) :=
  Fin (max (cap j) (2 * j.val.card) + 1)
abbrev Patterns (cap : Layer Γ → ℕ) := (a : Addr Γ) → Palette cap a.1

def Proper (cap : Layer Γ → ℕ) (p : Patterns cap) : Prop :=
  ∀ (j : Layer Γ) (u : Γ), u ∈ j.val → ∀ v : Γ, p (j,u*v) ≠ p (j,v)

abbrev Space (cap : Layer Γ → ℕ) := {p : Patterns cap // Proper cap p}

variable (cap : Layer Γ → ℕ)

theorem isClosed_proper : IsClosed {p : Patterns cap | Proper cap p} := by
  have he : {p : Patterns cap | Proper cap p} =
      ⋂ j : Layer Γ, ⋂ u : ↥j.val, ⋂ v : Γ,
        {p : Patterns cap | p (j,u.val*v) ≠ p (j,v)} := by
    ext p
    simp [Proper, Subtype.forall]
  rw [he]
  refine isClosed_iInter fun j => isClosed_iInter fun u => isClosed_iInter fun v => ?_
  let f : Patterns cap → Palette cap j × Palette cap j :=
    fun p => (p (j,u.val*v), p (j,v))
  have hf : Continuous f := (continuous_apply (j,u.val*v)).prodMk (continuous_apply (j,v))
  exact (isClosed_discrete {p : Palette cap j × Palette cap j | p.1 ≠ p.2}).preimage hf

instance : CompactSpace (Space cap) :=
  isCompact_iff_compactSpace.mp (isClosed_proper cap).isCompact

instance : SecondCountableTopology (Space cap) := by
  letI : Countable (Addr Γ) := inferInstanceAs (Countable ({s : Finset Γ // (1 : Γ) ∉ s} × Γ))
  letI : SecondCountableTopology (Patterns cap) :=
    inferInstanceAs (SecondCountableTopology ((a : Addr Γ) → Palette cap a.1))
  exact Subtype.secondCountableTopology ({p : Patterns cap | Proper cap p} : Set (Patterns cap))

instance : MetrizableSpace (Space cap) := metrizableSpace_of_t3_secondCountable _

instance : MeasurableSpace (Space cap) := borel _
instance : BorelSpace (Space cap) := ⟨rfl⟩

instance : MulAction Γ (Space cap) where
  smul g z := ⟨fun a => z.val (a.1,a.2*g), by
    intro j u hu v
    change z.val (j,(u*v)*g) ≠ z.val (j,v*g)
    rw [mul_assoc]
    exact z.property j u hu (v*g)⟩
  one_smul z := by
    apply Subtype.ext
    funext a
    change z.val (a.1,a.2 * 1) = z.val a
    rw [mul_one]
  mul_smul g h z := by
    apply Subtype.ext
    funext a
    change z.val (a.1,a.2 * (g*h)) = z.val (a.1,(a.2*g)*h)
    rw [mul_assoc]

@[simp] theorem smul_val (g : Γ) (z : Space cap) (a : Addr Γ) :
    (g • z).val a = z.val (a.1, a.2*g) := rfl

theorem continuous_translate (g : Γ) : Continuous (fun z : Space cap => g • z) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun a => (continuous_apply (a.1,a.2*g)).comp continuous_subtype_val

theorem free (g : Γ) (z : Space cap) (h : g • z = z) : g = 1 := by
  classical
  by_contra! hg
  let j : Layer Γ := ⟨{g}, by simpa using hg.symm⟩
  have hp := z.property j g (Finset.mem_singleton_self _) 1
  apply hp
  have he := congrArg (fun p : Space cap => p.val (j,1)) h
  change z.val (j,1*g) = z.val (j,1) at he
  rwa [mul_one, ← one_mul g]

/-- A finite word pattern at each layer is fixed by requiring equality at its observed sites. -/
def cylinder (a : Finset (Addr Γ)) (z : Space cap) : Set (Space cap) :=
  {y | ∀ i ∈ a, y.val i = z.val i}

theorem isClopen_cylinder (a : Finset (Addr Γ)) (z : Space cap) : IsClopen (cylinder cap a z) := by
  have he : cylinder cap a z =
      ⋂ i : ↥a, (fun y : Space cap => y.val i.val) ⁻¹' {z.val i.val} := by
    ext y
    simp [cylinder, Subtype.forall]
  rw [he]
  apply isClopen_iInter_of_finite
  intro i
  exact ⟨(isClosed_discrete _).preimage ((continuous_apply i.val).comp continuous_subtype_val),
    (isOpen_discrete _).preimage ((continuous_apply i.val).comp continuous_subtype_val)⟩

theorem cylinder_in_open {O : Set (Space cap)} (hO : IsOpen O) {z : Space cap}
    (hz : z ∈ O) : ∃ a : Finset (Addr Γ), cylinder cap a z ⊆ O := by
  classical
  obtain ⟨U,hU,rfl⟩ := isOpen_induced_iff.mp hO
  let B (a : Addr Γ) : Set (Set (Palette cap a.1)) := {s | ∃ x, s = {x}}
  have hB (a : Addr Γ) : IsTopologicalBasis (B a) := isTopologicalBasis_singletons _
  obtain ⟨U',⟨V,T,hV,rfl⟩,hz',hsub⟩ :=
    (isTopologicalBasis_pi hB).exists_subset_of_mem_open hz hU
  refine ⟨T, fun y hy => hsub ?_⟩
  intro i hi
  simpa only [show y.val i = z.val i from hy i hi] using hz' i hi

theorem clopen_basis :
    IsTopologicalBasis {U : Set (Space cap) | IsClopen U} := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · exact fun U hU => hU.2
  · intro z U hz hU
    obtain ⟨a,ha⟩ := cylinder_in_open cap hU hz
    exact ⟨cylinder cap a z, isClopen_cylinder cap a z, fun _ _ => rfl, ha⟩

/-- On the compact chart every continuous discrete-valued rule has a finite window. -/
theorem finite_window {V : Type*} [TopologicalSpace V] [DiscreteTopology V]
    (f : Space cap → V) (hf : Continuous f) :
    ∃ a : Finset (Addr Γ), ∀ x y : Space cap,
      (∀ i ∈ a, x.val i = y.val i) → f x = f y := by
  classical
  have hcell (z : Space cap) : ∃ a : Finset (Addr Γ),
      cylinder cap a z ⊆ f ⁻¹' {f z} :=
    cylinder_in_open cap ((isOpen_discrete _).preimage hf) rfl
  choose supp hsupp using hcell
  have hcover : (univ : Set (Space cap)) ⊆ ⋃ z : Space cap, cylinder cap (supp z) z := by
    intro z _
    exact mem_iUnion.mpr ⟨z,fun _ _ => rfl⟩
  obtain ⟨T,hT⟩ := isCompact_univ.elim_finite_subcover
    (fun z : Space cap => cylinder cap (supp z) z)
    (fun z => (isClopen_cylinder cap (supp z) z).2) hcover
  refine ⟨T.biUnion supp, fun x y hxy => ?_⟩
  have h := hT (mem_univ x)
  simp only [mem_iUnion] at h
  obtain ⟨z,hz,hxz⟩ := h
  have hyz : y ∈ cylinder cap (supp z) z := fun i hi =>
    (hxy i (Finset.mem_biUnion.mpr ⟨z,hz,hi⟩)).symm.trans (hxz i hi)
  exact (hsupp z hxz).trans (hsupp z hyz).symm

end ChartModel
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.ChartModel

-- BEGIN COMPLETE MODULE HirschProof.ChartExtensions
section
                             

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite.ChartModel

variable {Γ : Type*} [Group Γ] [Countable Γ]
variable (cap : Layer Γ → ℕ) (j : Layer Γ)

def ProperOn (D : Finset Γ) (c : Γ → Palette cap j) : Prop :=
  ∀ a ∈ j.val, ∀ v ∈ D, a*v ∈ D → c (a*v) ≠ c v

private noncomputable def neighbors (v : Γ) : Finset Γ := by
  classical
  exact (j.val.image (fun t => t*v)) ∪ (j.val.image (fun t => t⁻¹*v))

private theorem neighbors_card (v : Γ) : (neighbors j v).card ≤ 2 * j.val.card := by
  classical
  unfold neighbors
  have h := Finset.card_union_le (j.val.image (fun t => t*v))
    (j.val.image (fun t => t⁻¹*v))
  exact h.trans ((Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans_eq (by omega))

private theorem exists_fresh (c : Γ → Palette cap j) (v : Γ) :
    ∃ i : Palette cap j, ∀ t ∈ neighbors j v, i ≠ c t := by
  classical
  by_contra! h
  have hs : (Finset.univ : Finset (Palette cap j)) ⊆ (neighbors j v).image c := by
    intro i _
    obtain ⟨t,ht,rfl⟩ := h i
    exact Finset.mem_image.mpr ⟨t,ht,rfl⟩
  have hc := ((Finset.card_le_card hs).trans Finset.card_image_le).trans (neighbors_card j v)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  omega

private theorem extend_one (D : Finset Γ) (c : Γ → Palette cap j) (hc : ProperOn cap j D c)
    (x : Γ) :
    ∃ d : Γ → Palette cap j, ProperOn cap j (by classical exact insert x D) d ∧
      ∀ v ∈ D, d v = c v := by
  classical
  by_cases hx : x ∈ D
  · exact ⟨c, by simpa [hx] using hc, fun _ _ => rfl⟩
  obtain ⟨q,hq⟩ := exists_fresh cap j c x
  let d := Function.update c x q
  have hother (v : Γ) (hv : v ≠ x) : d v = c v := Function.update_of_ne hv q c
  have hat : d x = q := Function.update_self _ _ _
  refine ⟨d, ?_, fun v hv => hother v (fun h => hx (h ▸ hv))⟩
  intro a ha v hv hav
  have ha1 : a ≠ 1 := fun h => j.prop (h ▸ ha)
  by_cases hvx : v = x
  · subst v
    have hne : a*x ≠ x := by simpa using ha1
    rw [hat, hother (a*x) hne, ne_comm]
    exact hq _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
  · by_cases hax : a*v = x
    · rw [hax, hat, hother _ hvx]
      have hv' : a⁻¹*x = v := by rw [← hax, inv_mul_cancel_left]
      exact hq _ (hv' ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
    · rw [hother _ hax, hother _ hvx]
      exact hc a ha v ((Finset.mem_insert.mp hv).resolve_left hvx)
        ((Finset.mem_insert.mp hav).resolve_left hax)

/-- A finite proper pattern extends to the entire Cayley graph of the layer. -/
theorem extend_layer (D : Finset Γ) (c : Γ → Palette cap j) (hc : ProperOn cap j D c) :
    ∃ q : Γ → Palette cap j, (∀ u ∈ j.val, ∀ v, q (u*v) ≠ q v) ∧ ∀ v ∈ D, q v = c v := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat Γ
  let Stage := {s : Finset Γ × (Γ → Palette cap j) // ProperOn cap j s.1 s.2}
  let s₀ : Stage := ⟨(D,c),hc⟩
  let step (n : ℕ) (s : Stage) := extend_one cap j s.val.1 s.val.2 s.prop (e n)
  let next (n : ℕ) (s : Stage) : Stage :=
    ⟨(insert (e n) s.val.1,(step n s).choose),(step n s).choose_spec.1⟩
  let S : ℕ → Stage := Nat.rec s₀ next
  have hDomain (n : ℕ) : (S (n+1)).val.1 = insert (e n) (S n).val.1 := rfl
  have hStable (n : ℕ) (v : Γ) (hv : v ∈ (S n).val.1) :
      (S (n+1)).val.2 v = (S n).val.2 v := (step n (S n)).choose_spec.2 v hv
  have hDom : Monotone (fun n => (S n).val.1) :=
    monotone_nat_of_le_succ fun n => by
      change (S n).val.1 ⊆ (S (n+1)).val.1
      rw [hDomain]
      exact Finset.subset_insert _ _
  have hEq (n m : ℕ) (hnm : n ≤ m) (v : Γ) (hv : v ∈ (S n).val.1) :
      (S m).val.2 v = (S n).val.2 v := by
    refine Nat.le_induction rfl (fun r hnr ih => ?_) m hnm
    exact (hStable r v (hDom hnr hv)).trans ih
  have occurs (v : Γ) : ∃ n, v ∈ (S n).val.1 := by
    obtain ⟨n,rfl⟩ := he v
    exact ⟨n+1,by rw [hDomain]; exact Finset.mem_insert_self _ _⟩
  let q (v : Γ) := (S (occurs v).choose).val.2 v
  have hq (n : ℕ) (v : Γ) (hv : v ∈ (S n).val.1) : q v = (S n).val.2 v := by
    let m := max n (occurs v).choose
    exact (hEq _ m (le_max_right _ _) v (occurs v).choose_spec).symm.trans
      (hEq n m (le_max_left _ _) v hv)
  refine ⟨q,?_,fun v hv => hq 0 v hv⟩
  intro u hu v
  let m := max (occurs v).choose (occurs (u*v)).choose
  have hv : v ∈ (S m).val.1 := hDom (le_max_left _ _) (occurs v).choose_spec
  have huv : u*v ∈ (S m).val.1 := hDom (le_max_right _ _) (occurs (u*v)).choose_spec
  rw [hq m v hv, hq m (u*v) huv]
  exact (S m).prop u hu v hv huv

/-- The complete compact chart realizes any finite family of valid partial layer patterns. -/
theorem extend_patterns (D : Layer Γ → Finset Γ) (c : Patterns cap)
    (hc : ∀ j, ProperOn cap j (D j) (fun v => c (j,v))) :
    ∃ z : Space cap, ∀ j v, v ∈ D j → z.val (j,v) = c (j,v) := by
  classical
  have hext (i : Layer Γ) := extend_layer cap i (D i) (fun v => c (i,v)) (hc i)
  choose q hq hEq using hext
  let z : Space cap := ⟨fun a => q a.1 a.2, fun j u hu v => hq j u hu v⟩
  exact ⟨z,hEq⟩

end LocalHirschHyperfinite.ChartModel

end
-- END COMPLETE MODULE HirschProof.ChartExtensions

-- BEGIN COMPLETE MODULE HirschProof.ChartComponents
section
                                  
                                          

set_option autoImplicit false

open Set Topology TopologicalSpace

namespace LocalHirschHyperfinite
universe u

section Moves
variable {G X : Type*} [Group G] [MulAction G X]

def TestEdge (K : Finset G) (U : Set X) (x y : X) : Prop :=
  x ∈ U ∧ y ∈ U ∧ ∃ g ∈ K, g • x = y

def TestComponent (K : Finset G) (U : Set X) (x y : X) : Prop :=
  x ∈ U ∧ Relation.ReflTransGen (TestEdge K U) x y

variable [Countable G] [MeasurableSpace X] [MeasurableEq X]

theorem wordNear_one_iff_move (K : Finset G) (hK : SymmetricMoves K) (h1 : (1 : G) ∈ K)
    (hact : BorelAction G X) {x y : X} :
    (wordNear K hK hact).near 1 x y ↔ ∃ g ∈ K, g • x = y := by
  constructor
  · rintro ⟨a,ha,h⟩
    cases h with
    | nil => exact ⟨1,h1,one_smul _ _⟩
    | @cons u v w a b hstep htail =>
      have hap : a = 1 := hstep.1
      have hz : b = 0 := by omega
      have hvw := htail.zero_eq (fun e => by have := e.1; omega) hz
      obtain ⟨g,hg,heq⟩ := hstep.2
      exact ⟨g,hg,heq.trans hvw⟩
  · rintro ⟨g,hg,he⟩
    rw [← he]
    exact wordNear_generator K hK hact hg x

theorem wordNear_comp_iff_testComponent (K : Finset G) (hK : SymmetricMoves K) (h1 : (1 : G) ∈ K)
    (hact : BorelAction G X) (U : Set X) (x y : X) :
    (wordNear K hK hact).comp 1 U x y ↔ TestComponent K U x y := by
  have he : (wordNear K hK hact).edge 1 U = TestEdge K U := by
    funext x y
    apply propext
    exact and_congr_right fun _ => and_congr_right fun _ => wordNear_one_iff_move K hK h1 hact
  change x ∈ U ∧ Relation.ReflTransGen ((wordNear K hK hact).edge 1 U) x y ↔ _
  rw [he]
  rfl

end Moves

/-- The clopen finite-component form of the dynamic dimension bound for compact free actions. -/
def CompactClopenDADLE (G : Type u) [Group G] (d : ℕ) : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] [CompactSpace Z] [MetrizableSpace Z] [MulAction G Z],
    IsTopologicalBasis {U : Set Z | IsClopen U} →
    (∀ g : G, Continuous (fun z : Z => g • z)) →
    (∀ g : G, ∀ z : Z, g • z = z → g = 1) →
    ∀ (K : Finset G), SymmetricMoves K →
    ∃ U : Fin (d+1) → Set Z,
      (∀ i, IsClopen (U i)) ∧ (∀ z, ∃ i, z ∈ U i) ∧
      ∃ N : ℕ, ∀ i z, ∃ F : Finset Z, F.card ≤ N ∧
        ∀ w, TestComponent K (U i) z w → w ∈ F

namespace ChartModel
variable {Γ : Type*} [Group Γ] [Countable Γ] (cap : Layer Γ → ℕ)

theorem smul_injective (z : Space cap) :
    Function.Injective (fun g : Γ => g • z) := by
  intro g h he
  change g • z = h • z at he
  have hh : (h⁻¹*g) • z = z := by rw [mul_smul,he,inv_smul_smul]
  have hp := free cap _ _ hh
  have hp' := congrArg (fun q : Γ => h*q) hp
  simpa using hp'

theorem components_in_wordBall (K : Finset Γ) (hK : SymmetricMoves K) (h1 : (1 : Γ) ∈ K)
    {U : Set (Space cap)} {N : ℕ}
    (hsmall : ∀ z, ∃ F : Finset (Space cap), F.card ≤ N ∧
      ∀ w, TestComponent K U z w → w ∈ F)
    {z w : Space cap} (h : TestComponent K U z w) :
    ∃ g ∈ wordBall K N, g • z = w := by
  have hact : BorelAction Γ (Space cap) := fun g => (continuous_translate cap g).measurable
  let D : BorelNear (Space cap) := wordNear K hK hact
  have small (z : Space cap) : ∃ F : Finset (Space cap), F.card ≤ N ∧
      ∀ w, D.comp 1 U z w → w ∈ F := by
    obtain ⟨F,hF,hh⟩ := hsmall z
    exact ⟨F,hF,fun w h => hh w ((wordNear_comp_iff_testComponent K hK h1 hact U z w).mp h)⟩
  have hn : D.near (1*N) z w := D.boundComp_of_small small
    ((wordNear_comp_iff_testComponent K hK h1 hact U z w).mpr h)
  obtain ⟨a,ha,hw⟩ := hn
  obtain ⟨g,hg,he⟩ := hw.exists_wordBall K (fun h => ⟨by have := h.1; omega,h.2⟩)
  exact ⟨g,wordBall_mono K (by simpa using ha) hg,he⟩

theorem test_trans {K : Finset Γ} {U : Set (Space cap)} {z w y : Space cap}
    (h : TestComponent K U z w) (h' : TestComponent K U w y) : TestComponent K U z y :=
  ⟨h.1,h.2.trans h'.2⟩

theorem test_symm {K : Finset Γ} (hK : SymmetricMoves K) {U : Set (Space cap)}
    {z w : Space cap} (h : TestComponent K U z w) : TestComponent K U w z := by
  have he : Symmetric (TestEdge K U) := fun x y e => by
    obtain ⟨g,hg,he⟩ := e.2.2
    exact ⟨e.2.1,e.1,g⁻¹,hK hg,by rw [← he,inv_smul_smul]⟩
  have hh : w ∈ U := by
    obtain ⟨hz,p⟩ := h
    cases p with
    | refl => exact hz
    | tail _ e => exact e.2.1
  have rev {a b : Space cap} (p : Relation.ReflTransGen (TestEdge K U) a b) :
      Relation.ReflTransGen (TestEdge K U) b a := by
    induction p with
    | refl => exact .refl
    | tail _ e ih => exact (Relation.ReflTransGen.single (he e)).trans ih
  exact ⟨hh,rev h.2⟩

/-- A finite displacement table determines components from finitely many membership tests. -/
theorem components_agree (K V : Finset Γ) (h1 : (1 : Γ) ∈ V)
    (U : Set (Space cap))
    (hV : ∀ x y, TestComponent K U x y → ∃ g ∈ V, g • x = y)
    {z z' : Space cap} (hs : ∀ g ∈ V, g • z ∈ U ↔ g • z' ∈ U)
    (g : Γ) :
    TestComponent K U z (g • z) ↔ TestComponent K U z' (g • z') := by
  suffices move : ∀ (z z' : Space cap),
      (∀ g ∈ V, g • z ∈ U ↔ g • z' ∈ U) →
      TestComponent K U z (g • z) → TestComponent K U z' (g • z') by
    exact ⟨move z z' hs,move z' z (fun g hg => (hs g hg).symm)⟩
  intro z z' hh h
  have hz' : z' ∈ U := by
    have he := hh 1 h1
    simpa only [one_smul] using he.mp (by simpa only [one_smul] using h.1)
  obtain ⟨hz,p⟩ := h
  have transfer {w : Space cap} (p : Relation.ReflTransGen (TestEdge K U) z w) :
      ∀ a : Γ, a • z = w → Relation.ReflTransGen (TestEdge K U) z' (a • z') := by
    induction p with
    | refl =>
      intro a ha
      rw [free cap a z ha,one_smul]
    | @tail x y p e ih =>
      intro b hb
      obtain ⟨a,ha,haz⟩ := hV z x ⟨hz,p⟩
      obtain ⟨t,ht,hte⟩ := e.2.2
      have hbV : b ∈ V := by
        obtain ⟨v,hv,hve⟩ := hV z y ⟨hz,p.tail e⟩
        exact (smul_injective cap z (hve.trans hb.symm)) ▸ hv
      have hba : t*a = b := smul_injective cap z (by
        change (t*a) • z = b • z
        rw [mul_smul,haz,hte,hb])
      apply (ih a haz).tail
      refine ⟨(hh a ha).mp (haz ▸ e.1),(hh b hbV).mp (hb ▸ e.2.1),t,ht,?_⟩
      rw [← mul_smul,hba]
  exact ⟨hz',transfer p g rfl⟩

end ChartModel
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.ChartComponents

-- BEGIN COMPLETE MODULE HirschProof.ClopenDimension
section
                                  
                                    
                                     

set_option autoImplicit false
noncomputable section

open Set Topology TopologicalSpace

namespace LocalHirschHyperfinite

section FiniteTests

variable {G X : Type*} [Group G] [MulAction G X]

theorem testComponent_mono {K L : Finset G} (hKL : K ⊆ L) {A B : Set X} (hAB : A ⊆ B)
    {x y : X} (h : TestComponent K A x y) : TestComponent L B x y := by
  refine ⟨hAB h.1,h.2.mono ?_⟩
  rintro u v ⟨hu,hv,g,hg,he⟩
  exact ⟨hAB hu,hAB hv,g,hKL hg,he⟩

theorem testComponent_end {K : Finset G} {A : Set X} {x y : X}
    (h : TestComponent K A x y) : y ∈ A := by
  obtain ⟨hx,p⟩ := h
  cases p with
  | refl => exact hx
  | tail _ he => exact he.2.1

theorem testComponent_symm {K : Finset G} (hK : SymmetricMoves K)
    {A : Set X} {x y : X} (h : TestComponent K A x y) : TestComponent K A y x := by
  refine ⟨testComponent_end h,?_⟩
  have he : Symmetric (TestEdge K A) := by
    rintro u v ⟨hu,hv,g,hg,rfl⟩
    exact ⟨hv,hu,g⁻¹,hK hg,inv_smul_smul _ _⟩
  have rev {u v : X} (p : Relation.ReflTransGen (TestEdge K A) u v) :
      Relation.ReflTransGen (TestEdge K A) v u := by
    induction p with
    | refl => exact .refl
    | tail _ e ih => exact (Relation.ReflTransGen.single (he e)).trans ih
  exact rev h.2

theorem testComponent_trans {K : Finset G} {A : Set X} {x y z : X}
    (h : TestComponent K A x y) (h' : TestComponent K A y z) :
    TestComponent K A x z := ⟨h.1,h.2.trans h'.2⟩

theorem free_smul_injective
    (hfree : ∀ g : G, ∀ x : X, g • x = x → g = 1) (x : X) :
    Function.Injective (fun g : G => g • x) := by
  intro g h he
  change g • x = h • x at he
  have hg := hfree (h⁻¹*g) x (by rw [mul_smul,he,inv_smul_smul])
  simpa using congrArg (fun a : G => h*a) hg

section Topology
variable [TopologicalSpace X]
variable (hact : ∀ g : G, Continuous (fun x : X => g • x))
variable (hfree : ∀ g : G, ∀ x : X, g • x = x → g = 1)

include hact in
theorem isClopen_translate (g : G) {A : Set X} (hA : IsClopen A) :
    IsClopen ((fun x : X => g • x) '' A) := by
  have he : (fun x : X => g • x) '' A = (fun x : X => g⁻¹ • x) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [mem_preimage,inv_smul_smul] using hy
    · intro hx
      exact ⟨g⁻¹ • x,hx,smul_inv_smul _ _⟩
  rw [he]
  exact hA.preimage (hact _)

include hact hfree in
/-- A bounded component is determined by the membership pattern of its finite displacement set. -/
theorem isClopen_testComponent {K V : Finset G} {A : Set X} (hA : IsClopen A)
    (hV : ∀ x y, TestComponent K A x y → ∃ g ∈ V, g • x = y)
    (g : G) : IsClopen {x | TestComponent K A x (g • x)} := by
  classical
  let I := ({1} ∪ V : Finset G)
  let C (x : X) : Set X := ⋂ t : (I : Set G),
    if t.val • x ∈ A then (fun y : X => t.val • y) ⁻¹' A
    else ((fun y : X => t.val • y) ⁻¹' A)ᶜ
  have hC (x : X) : IsClopen (C x) := by
    apply isClopen_iInter_of_finite
    intro t
    split
    · exact hA.preimage (hact _)
    · exact (hA.preimage (hact _)).compl
  have hxC (x : X) : x ∈ C x := by
    apply Set.mem_iInter.mpr
    intro t
    by_cases ht : t.val • x ∈ A <;> simp [ht]
  have agree {x y : X} (h : y ∈ C x) (t : G) (ht : t ∈ I) : t • x ∈ A ↔ t • y ∈ A := by
    have hh := Set.mem_iInter.mp h ⟨t,ht⟩
    by_cases htx : t • x ∈ A <;> simp_all
  have move {x y : X} (h : y ∈ C x) :
      TestComponent K A x (g • x) ↔ TestComponent K A y (g • y) := by
    suffices aux : ∀ (u v : X),
        (∀ t ∈ I, t • u ∈ A ↔ t • v ∈ A) →
        TestComponent K A u (g • u) → TestComponent K A v (g • v) by
      exact ⟨aux x y (agree h),aux y x (fun t ht => (agree h t ht).symm)⟩
    intro u v hp hu
    have hv : v ∈ A := by
      have h1 := hp 1 (by simp [I])
      simpa only [one_smul] using h1.mp (by simpa only [one_smul] using hu.1)
    refine ⟨hv,?_⟩
    have tr {w : X} (p : Relation.ReflTransGen (TestEdge K A) u w) :
        ∀ a : G, a • u = w → Relation.ReflTransGen (TestEdge K A) v (a • v) := by
      induction p with
      | refl =>
        intro a ha
        rw [hfree a u ha,one_smul]
      | @tail z w p e ih =>
        intro b hb
        obtain ⟨a,ha,haz⟩ := hV _ _ ⟨hu.1,p⟩
        obtain ⟨t,ht,hte⟩ := e.2.2
        have hbV : b ∈ V := by
          obtain ⟨j,hj,hje⟩ := hV _ _ ⟨hu.1,p.tail e⟩
          exact (free_smul_injective hfree u (hje.trans hb.symm)) ▸ hj
        have hba : t*a = b := free_smul_injective hfree u (by
          change (t*a) • u = b • u
          rw [mul_smul,haz,hte,hb])
        apply (ih a haz).tail
        refine ⟨(hp a (Finset.mem_union_right _ ha)).mp (haz ▸ e.1),
          (hp b (Finset.mem_union_right _ hbV)).mp (hb ▸ e.2.1),t,ht,?_⟩
        rw [← mul_smul,hba]
    exact tr hu.2 g rfl
  constructor
  · rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact Filter.mem_of_superset ((hC x).2.mem_nhds (hxC x)) (fun y hy => fun h =>
      hx ((move hy).mpr h))
  · apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact Filter.mem_of_superset ((hC x).2.mem_nhds (hxC x)) (fun y hy => (move hy).mp hx)

variable [T2Space X] [CompactSpace X]

include hact hfree in
/-- A finite clopen cover separates every point from its translates by a finite set of
nonidentity moves. -/
theorem exists_clopen_move_separation
    (hbasis : IsTopologicalBasis {U : Set X | IsClopen U}) (V : Finset G) :
    ∃ n : ℕ, ∃ U : Fin n → Set X, (∀ i, IsClopen (U i)) ∧
      (∀ x, ∃ i, x ∈ U i) ∧
      ∀ i x, x ∈ U i → ∀ g ∈ V, g ≠ 1 → g • x ∉ U i := by
  classical
  have localCover (x : X) : ∃ U : Set X, IsClopen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ g ∈ V, g ≠ 1 → g • y ∉ U := by
    have oneMove (g : {g : (V : Set G) // g.val ≠ 1}) :
        ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ ∀ y ∈ U, (g.val.val : G) • y ∉ U := by
      have hne : x ≠ (g.val.val : G) • x := fun h => g.property (hfree _ _ h.symm)
      obtain ⟨A,B,hA,hB,hxA,hxB,hd⟩ := t2_separation hne
      have hxAB : x ∈ A ∩ (fun y : X => (g.val.val : G) • y) ⁻¹' B := ⟨hxA,hxB⟩
      obtain ⟨U,hU,hxU,hu⟩ :=
        hbasis.exists_subset_of_mem_open hxAB (hA.inter (hB.preimage (hact _)))
      exact ⟨U,hU,hxU,fun y hy hgy => Set.disjoint_left.mp hd (hu hgy).1 (hu hy).2⟩
    choose T hT hxT ht using oneMove
    refine ⟨⋂ g, T g,isClopen_iInter_of_finite hT,Set.mem_iInter.mpr hxT,?_⟩
    intro y hy g hg hne hgy
    exact ht ⟨⟨g,hg⟩,hne⟩ y (Set.mem_iInter.mp hy _) (Set.mem_iInter.mp hgy _)
  choose U hU hxU ht using localCover
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U (fun x => (hU x).2)
    (fun x _ => Set.mem_iUnion.mpr ⟨x,hxU x⟩)
  let e := s.equivFin
  refine ⟨s.card,fun i => U (e.symm i).val,fun i => hU _,fun x => ?_,?_⟩
  · obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨e ⟨y,hy⟩,by simpa using hxy⟩
  · intro i
    exact ht _


include hact hfree in
/-- Bounded clopen components have a clopen transversal. -/
theorem exists_clopen_component_transversal
    (hbasis : IsTopologicalBasis {U : Set X | IsClopen U})
    {K V : Finset G} (hK : SymmetricMoves K) {A : Set X} (hA : IsClopen A)
    (hV : ∀ x y, TestComponent K A x y → ∃ g ∈ V, g • x = y) :
    ∃ S : Set X, IsClopen S ∧ S ⊆ A ∧ ∀ x ∈ A, ∃! y, y ∈ S ∧ TestComponent K A x y := by
  classical
  obtain ⟨n,C,hC,hcov,hsep⟩ := exists_clopen_move_separation hact hfree hbasis V
  let L (i : Fin n) := ⋃ j : {j : Fin n // j < i}, C j.val
  let T (i : Fin n) := (A ∩ C i) ∩
    ⋂ g : (V : Set G), ({x | TestComponent K A x (g.val • x)} ∩
      (fun x : X => g.val • x) ⁻¹' L i)ᶜ
  let S := ⋃ i, T i
  have hL (i : Fin n) : IsClopen (L i) := isClopen_iUnion_of_finite fun j => hC j.val
  have hm {x : X} : x ∈ S ↔ x ∈ A ∧ ∃ i, x ∈ C i ∧
      ∀ y, TestComponent K A x y → ∀ j < i, y ∉ C j := by
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      refine ⟨hi.1.1,i,hi.1.2,?_⟩
      intro y hy j hj hyj
      obtain ⟨g,hg,rfl⟩ := hV _ _ hy
      exact Set.mem_iInter.mp hi.2 ⟨g,hg⟩ ⟨hy,Set.mem_iUnion.mpr ⟨⟨j,hj⟩,hyj⟩⟩
    · rintro ⟨hx,i,hi,h⟩
      refine Set.mem_iUnion.mpr ⟨i,⟨hx,hi⟩,Set.mem_iInter.mpr ?_⟩
      rintro g ⟨hg,hl⟩
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hl
      exact h _ hg _ j.property hj
  refine ⟨S,?_,fun x hx => (hm.mp hx).1,?_⟩
  · exact isClopen_iUnion_of_finite fun i => (hA.inter (hC i)).inter
      (isClopen_iInter_of_finite fun g =>
        ((isClopen_testComponent hact hfree hA hV g.val).inter
          ((hL i).preimage (hact _))).compl)
  · intro x hx
    let p (m : ℕ) := ∃ (i : Fin n) (y : X), i.val = m ∧ TestComponent K A x y ∧ y ∈ C i
    have he : ∃ m, p m := by
      obtain ⟨i,hi⟩ := hcov x
      exact ⟨i.val,i,x,rfl,⟨hx,.refl⟩,hi⟩
    obtain ⟨i,y,hmin,hxy,hyi⟩ := Nat.find_spec he
    have hsmall : ∀ z, TestComponent K A y z → ∀ j < i, z ∉ C j := by
      intro z hyz j hj hz
      exact Nat.find_min he (show j.val < Nat.find he from hmin ▸ hj)
        ⟨j,z,rfl,testComponent_trans hxy hyz,hz⟩
    refine ⟨y,⟨hm.mpr ⟨testComponent_end hxy,i,hyi,hsmall⟩,hxy⟩,?_⟩
    rintro z ⟨hzS,hxz⟩
    obtain ⟨_,j,hzj,hj⟩ := hm.mp hzS
    have hyz := testComponent_trans (testComponent_symm hK hxy) hxz
    have hzy := testComponent_symm hK hyz
    have hij : i = j := le_antisymm (le_of_not_gt (fun hlt => hsmall z hyz j hlt hzj))
      (le_of_not_gt (fun hlt => hj y hzy i hlt hyi))
    subst j
    obtain ⟨g,hg,hgz⟩ := hV y z hyz
    have h1 : g = 1 := by
      by_contra hn
      exact hsep i y hyi g hg hn (hgz ▸ hzj)
    simpa only [h1,one_smul] using hgz.symm

end Topology
end FiniteTests

section OrbitCovers

variable {G X : Type*} [Group G] [MulAction G X]

/-- The ordinary finite-cover definition for the left translation action of the group. -/
def OrdinaryGroupAsdimLE (B : ProperGroupBalls G) (d : ℕ) : Prop :=
  ∀ r : ℕ, ∃ U : Fin (d+1) → Set G, ∃ R : ℕ,
    (∀ g, ∃ i, g ∈ U i) ∧ ∀ i g h, TestComponent (B.ball r) (U i) g h →
      ∃ k ∈ B.ball R, k*g = h

variable [TopologicalSpace X]

/-- A finite clopen cover whose components are bounded in a specified orbit metric. -/
def ClopenBallCover (B : ProperGroupBalls G) (d r R : ℕ) (A : Set X) : Prop :=
  ∃ U : Fin (d+1) → Set X, (∀ i, IsClopen (U i)) ∧ (∀ i, U i ⊆ A) ∧
    (∀ x ∈ A, ∃ i, x ∈ U i) ∧ ∀ i x y, TestComponent (B.ball r) (U i) x y →
      ∃ g ∈ B.ball R, g • x = y

variable [T2Space X] [CompactSpace X]

/-- On a clopen set of bounded components, a clopen transversal makes an ordinary
group cover usable with the same number of colors. -/
theorem clopen_cover_on_bounded_components (B : ProperGroupBalls G)
    (hact : ∀ g : G, Continuous (fun x : X => g • x))
    (hfree : ∀ g : G, ∀ x : X, g • x = x → g = 1)
    (hbasis : IsTopologicalBasis {U : Set X | IsClopen U})
    {A : Set X} (hA : IsClopen A) {s t r R d : ℕ} (hrs : r ≤ s)
    (hAcomp : ∀ x y, TestComponent (B.ball s) A x y → ∃ g ∈ B.ball t, g • x = y)
    (U : Fin (d+1) → Set G) (hU : ∀ g, ∃ i, g ∈ U i)
    (hUR : ∀ i g h, TestComponent (B.ball r) (U i) g h → ∃ k ∈ B.ball R, k*g = h) :
    ClopenBallCover B d r R A := by
  classical
  let K := B.ball s
  have hK : SymmetricMoves K := fun _ h => B.inv_mem h
  obtain ⟨S,hS,hSA,hSuni⟩ := exists_clopen_component_transversal hact hfree hbasis hK hA hAcomp
  let Q (g : G) : Set X := {x | TestComponent K A x (g • x)}
  let V (i : Fin (d+1)) : Set X := ⋃ g : {g : (B.ball t : Set G) // g.val ∈ U i},
    (fun x : X => g.val.val • x) '' (S ∩ Q g.val.val)
  have hV (i : Fin (d+1)) {x : X} : x ∈ V i ↔ ∃ g ∈ B.ball t, g ∈ U i ∧
      ∃ a ∈ S, TestComponent K A a (g • a) ∧ g • a = x := by
    constructor
    · intro hx
      obtain ⟨g,a,ha,he⟩ := Set.mem_iUnion.mp hx
      exact ⟨g.val.val,g.val.property,g.property,a,ha.1,ha.2,he⟩
    · rintro ⟨g,hg,hgi,a,ha,haq,hax⟩
      exact Set.mem_iUnion.mpr ⟨⟨⟨g,hg⟩,hgi⟩,a,⟨ha,haq⟩,hax⟩
  have hVA (i : Fin (d+1)) : V i ⊆ A := by
    intro x hx
    obtain ⟨g,_,_,a,_,hac,rfl⟩ := (hV i).mp hx
    exact testComponent_end hac
  refine ⟨V,fun i => isClopen_iUnion_of_finite (fun g =>
    isClopen_translate hact g.val.val (hS.inter (isClopen_testComponent hact hfree hA hAcomp _))),
    hVA,?_,?_⟩
  · intro x hx
    obtain ⟨a,⟨ha,hxa⟩,_⟩ := hSuni x hx
    have hax := testComponent_symm hK hxa
    obtain ⟨g,hg,hgx⟩ := hAcomp _ _ hax
    obtain ⟨i,hi⟩ := hU g
    exact ⟨i,(hV i).mpr ⟨g,hg,hi,a,ha,hgx.symm ▸ hax,hgx⟩⟩
  · intro i x y hxy
    have hs (w : X) (h : TestComponent (B.ball r) (V i) x w) : TestComponent K A x w :=
      testComponent_mono (B.mono hrs) (hVA i) h
    obtain ⟨a,_,huni⟩ := hSuni x (hVA i hxy.1)
    have hc (w : X) (hw : TestComponent (B.ball r) (V i) x w) :
        ∃ g ∈ U i, g • a = w := by
      obtain ⟨g,_,hgi,b,hb,hbw,hgb⟩ := (hV i).mp (testComponent_end hw)
      have hwb : TestComponent K A w b := testComponent_symm hK (hgb ▸ hbw)
      have hba := huni b ⟨hb,testComponent_trans (hs w hw) hwb⟩
      exact ⟨g,hgi,by simpa only [hba] using hgb⟩
    obtain ⟨g,hgi,hgx⟩ := hc x ⟨hxy.1,.refl⟩
    obtain ⟨l,hli,hly⟩ := hc y hxy
    have geodesic {w : X} (p : Relation.ReflTransGen (TestEdge (B.ball r) (V i)) x w) :
        ∀ j : G, j • a = w → Relation.ReflTransGen (TestEdge (B.ball r) (U i)) g j := by
      induction p with
      | refl =>
        intro j hj
        have hgj := free_smul_injective hfree a (hgx.trans hj.symm)
        rw [← hgj]
      | @tail w z p e ih =>
        intro j hj
        obtain ⟨k,hki,hkw⟩ := hc w ⟨hxy.1,p⟩
        obtain ⟨l,hli',hlz⟩ := hc z ⟨hxy.1,p.tail e⟩
        obtain ⟨t,ht,htz⟩ := e.2.2
        have hjl := free_smul_injective hfree a (hj.trans hlz.symm)
        have htk := free_smul_injective hfree a (show (t*k) • a = j • a by
          rw [mul_smul,hkw,htz,hj])
        exact (ih k hkw).tail ⟨hki,hjl.symm ▸ hli',t,ht,htk⟩
    obtain ⟨k,hk,hkl⟩ := hUR i g l ⟨hgi,geodesic hxy.2 l hly⟩
    exact ⟨k,hk,by rw [← hgx,← mul_smul,hkl,hly]⟩

end OrbitCovers

section Sharpening
variable {G X : Type*} [Group G] [Countable G] [MulAction G X]
variable [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
variable (B : ProperGroupBalls G)

omit [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] in
private theorem orbitBall_component_iff [MeasurableSpace X] [MeasurableEq X]
    (hact : BorelAction G X) (r : ℕ) (A : Set X) (x y : X) :
    (B.toBorelNear hact).comp r A x y ↔ TestComponent (B.ball r) A x y := Iff.rfl

omit [Countable G] [T2Space X] [SecondCountableTopology X] in
private theorem clopenBallCover_empty (d r R : ℕ) : ClopenBallCover B d r R (∅ : Set X) :=
  ⟨fun _ => ∅,fun _ => isClopen_empty,fun _ => Subset.rfl,fun _ h => h.elim,
    fun _ _ _ h => h.1.elim⟩

private theorem clopenBallCover_union (hact : ∀ g : G, Continuous (fun x : X => g • x))
    {d r a b : ℕ} {A C : Set X}
    (hA : ClopenBallCover B d r a A) (hC : ClopenBallCover B d (r+a+r) b C) :
    ClopenBallCover B d r (2*(b+r+a)) (A ∪ C) := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  have hm : BorelAction G X := fun g => (hact g).measurable
  obtain ⟨U,hU,hUA,hAU,hUb⟩ := hA
  obtain ⟨V,hV,hVC,hCV,hVb⟩ := hC
  refine ⟨fun i => U i ∪ V i,fun i => (hU i).union (hV i),
    fun i => union_subset_union (hUA i) (hVC i),?_,?_⟩
  · rintro x (hx|hx)
    · obtain ⟨i,hi⟩ := hAU x hx
      exact ⟨i,Or.inl hi⟩
    · obtain ⟨i,hi⟩ := hCV x hx
      exact ⟨i,Or.inr hi⟩
  · intro i x y hxy
    let D := B.toBorelNear hm
    have hUb' : D.boundComp (U i) r a := fun {u v} h =>
      hUb i u v ((orbitBall_component_iff B hm r (U i) u v).mp h)
    have hVb' : D.boundComp (V i) (r+a+r) b := fun {u v} h =>
      hVb i u v ((orbitBall_component_iff B hm (r+a+r) (V i) u v).mp h)
    exact D.boundComp_union_larger_scale hUb' hVb'
      ((orbitBall_component_iff B hm r (U i ∪ V i) x y).mpr hxy)

end Sharpening

universe u

/-- CJMST's clopen dimension sharpening for compact metrizable spaces.
A finite strong bound can be sharpened to an ordinary group dimension bound. -/
theorem compactClopenDADLE_of_ordinary_of_finite {G : Type u} [Group G] [Countable G]
    (B : ProperGroupBalls G) {d d' : ℕ} (ho : OrdinaryGroupAsdimLE B d)
    (hf : CompactClopenDADLE G d') : CompactClopenDADLE G d := by
  classical
  intro X _ _ _ _ hbasis hact hfree K hK
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  have hm : BorelAction G X := fun g => (hact g).measurable
  obtain ⟨r,hr⟩ := B.finite_subset K
  choose U R hU hUR using ho
  let m : ℕ → ℕ := Nat.rec 0 (fun _ a => 2*(R (r+a+r)+r+a))
  let T (n : ℕ) := r+m n+r
  let M := (Finset.range (d'+1)).sup T
  obtain ⟨W,hW,hWcover,N,hN⟩ := hf X hbasis hact hfree (B.ball M) (fun _ h => B.inv_mem h)
  let D := B.toBorelNear hm
  have hw (i : Fin (d'+1)) (x y : X) (h : TestComponent (B.ball M) (W i) x y) :
      ∃ g ∈ B.ball (M*N), g • x = y := by
    have finiteBound (z : X) : ∃ F : Finset X, F.card ≤ N ∧
        ∀ w, D.comp M (W i) z w → w ∈ F := by
      obtain ⟨F,hF,hh⟩ := hN i z
      exact ⟨F,hF,fun w hw => hh w ((orbitBall_component_iff B hm M (W i) z w).mp hw)⟩
    exact D.boundComp_of_small finiteBound ((orbitBall_component_iff B hm M (W i) x y).mpr h)
  let A (n : ℕ) := ⋃ i : Fin (d'+1), ⋃ _ : i.val < n, W i
  have hA0 : A 0 = ∅ := by
    ext x
    simp [A]
  have hAsucc {n : ℕ} (hn : n < d'+1) : A (n+1) = A n ∪ W ⟨n,hn⟩ := by
    ext x
    simp only [A,Set.mem_iUnion,Set.mem_union]
    constructor
    · rintro ⟨i,hi,hx⟩
      by_cases h : i.val < n
      · exact Or.inl ⟨i,h,hx⟩
      · have hi' : i = ⟨n,hn⟩ := Fin.ext (by simp; omega)
        exact Or.inr (hi' ▸ hx)
    · rintro (⟨i,hi,hx⟩|hx)
      · exact ⟨i,hi.trans (Nat.lt_succ_self n),hx⟩
      · exact ⟨⟨n,hn⟩,Nat.lt_succ_self n,hx⟩
  have hAtop : A (d'+1) = (Set.univ : Set X) := by
    ext x
    simp only [A,Set.mem_iUnion,Set.mem_univ,iff_true]
    obtain ⟨i,hi⟩ := hWcover x
    exact ⟨i,i.isLt,hi⟩
  have grow (n : ℕ) (hn : n ≤ d'+1) : ClopenBallCover B d r (m n) (A n) := by
    induction n with
    | zero => rw [hA0]; exact clopenBallCover_empty B d r _
    | succ n ih =>
      have hlt : n < d'+1 := hn
      let i : Fin (d'+1) := ⟨n,hlt⟩
      have hT : T n ≤ M := Finset.le_sup (f := T) (Finset.mem_range.mpr hlt)
      have hnew : ClopenBallCover B d (T n) (R (T n)) (W i) :=
        clopen_cover_on_bounded_components B hact hfree hbasis (hW i) hT (hw i)
          (U (T n)) (hU (T n)) (hUR (T n))
      rw [hAsucc hlt]
      exact clopenBallCover_union B hact (ih (Nat.le_of_succ_le hn)) hnew
  have htop := grow (d'+1) le_rfl
  rw [hAtop] at htop
  obtain ⟨V,hV,_,hVcover,hVcomp⟩ := htop
  refine ⟨V,hV,fun x => hVcover x (Set.mem_univ _),(B.ball (m (d'+1))).card,fun i x => ?_⟩
  refine ⟨(B.ball (m (d'+1))).image (fun g => g • x),Finset.card_image_le,?_⟩
  intro y hxy
  obtain ⟨g,hg,rfl⟩ := hVcomp i x y (testComponent_mono hr Subset.rfl hxy)
  exact Finset.mem_image_of_mem _ hg

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.ClopenDimension

-- BEGIN COMPLETE MODULE HirschProof.ClopenPacking
section
                                  
                                       

set_option autoImplicit false
noncomputable section

open Set Topology TopologicalSpace

namespace LocalHirschHyperfinite

section Translates
variable {G X : Type*} [Group G] [MulAction G X]

/-- The union of translates by a finite collection of group elements. -/
def moveThickening (B : Finset G) (A : Set X) : Set X :=
  {x | ∃ g ∈ B, ∃ z ∈ A, g • z = x}

theorem moveThickening_mono {B : Finset G} {A C : Set X}
    (h : A ⊆ C) : moveThickening B A ⊆ moveThickening B C := by
  rintro x ⟨g,hg,z,hz,rfl⟩
  exact ⟨g,hg,z,h hz,rfl⟩

theorem moveThickening_mono_moves {B C : Finset G} (h : B ⊆ C) (A : Set X) :
    moveThickening B A ⊆ moveThickening C A := by
  rintro x ⟨g,hg,z,hz,rfl⟩
  exact ⟨g,h hg,z,hz,rfl⟩

theorem subset_moveThickening {B : Finset G} (h1 : 1 ∈ B) (A : Set X) :
    A ⊆ moveThickening B A := fun x hx => ⟨1,h1,x,hx,one_smul _ _⟩

theorem isClopen_moveThickening [TopologicalSpace X]
    (hact : ∀ g : G, Continuous (fun x : X => g • x))
    (B : Finset G) {A : Set X} (hA : IsClopen A) :
    IsClopen (moveThickening B A) := by
  have he : moveThickening B A = ⋃ g : (B : Set G), (fun x : X => g.val • x) '' A := by
    ext x
    simp only [moveThickening,Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_image]
    exact ⟨fun ⟨g,hg,h⟩ => ⟨⟨g,hg⟩,h⟩,fun ⟨g,h⟩ => ⟨g.val,g.property,h⟩⟩
  rw [he]
  exact isClopen_iUnion_of_finite fun g => isClopen_translate hact g.val hA

def MoveIndependent (B : Finset G) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ g ∈ B, g ≠ 1 → g • x ∉ A

theorem MoveIndependent.mono {B : Finset G} {A C : Set X} (h : MoveIndependent B C)
    (hs : A ⊆ C) : MoveIndependent B A :=
  fun x hx g hg hn he => h x (hs hx) g hg hn (hs he)

private def separatedCenterSet (B : Finset G) : List (Set X) → Set X
  | [] => ∅
  | U::V =>
    let S := separatedCenterSet B V
    S ∪ (U \ moveThickening B S)

private theorem separatedCenterSet_spec [TopologicalSpace X]
    (hact : ∀ g : G, Continuous (fun x : X => g • x))
    {B : Finset G} (hB : SymmetricMoves B) (h1 : 1 ∈ B)
    {L : List (Set X)} (hcl : ∀ U ∈ L, IsClopen U)
    (hsep : ∀ U ∈ L, MoveIndependent B U) :
    IsClopen (separatedCenterSet B L) ∧ MoveIndependent B (separatedCenterSet B L) ∧
      ∀ U ∈ L, U ⊆ moveThickening B (separatedCenterSet B L) := by
  induction L with
  | nil =>
    exact ⟨isClopen_empty,fun _ hx => hx.elim,fun _ h => (List.not_mem_nil h).elim⟩
  | cons U L ih =>
    obtain ⟨hclS,hsepS,hcover⟩ := ih
      (fun A hA => hcl A (List.mem_cons_of_mem U hA))
      (fun A hA => hsep A (List.mem_cons_of_mem U hA))
    let S := separatedCenterSet B L
    let T := U \ moveThickening B S
    change IsClopen (S ∪ T) ∧ MoveIndependent B (S ∪ T) ∧
      ∀ A ∈ U::L, A ⊆ moveThickening B (S ∪ T)
    refine ⟨hclS.union ((hcl U List.mem_cons_self).diff (isClopen_moveThickening hact B hclS)),?_,?_⟩
    · rintro x (hx|hx) g hg hne (hgx|hgx)
      · exact hsepS x hx g hg hne hgx
      · exact hgx.2 ⟨g,hg,x,hx,rfl⟩
      · exact hx.2 ⟨g⁻¹,hB hg,g • x,hgx,inv_smul_smul _ _⟩
      · exact hsep U List.mem_cons_self x hx.1 g hg hne hgx.1
    · intro A hA x hx
      rcases List.mem_cons.mp hA with rfl|hA
      · by_cases he : x ∈ moveThickening B S
        · exact moveThickening_mono subset_union_left he
        · exact subset_moveThickening h1 (S ∪ T) (Or.inr ⟨hx,he⟩)
      · exact moveThickening_mono subset_union_left (hcover _ hA hx)

/-- A finite symmetric neighborhood admits a clopen separated and covering center set. -/
theorem exists_clopen_separated_centers [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (hact : ∀ g : G, Continuous (fun x : X => g • x))
    (hfree : ∀ g : G, ∀ x : X, g • x = x → g = 1)
    (hbasis : IsTopologicalBasis {U : Set X | IsClopen U})
    {B : Finset G} (hB : SymmetricMoves B) (h1 : 1 ∈ B) :
    ∃ S : Set X, IsClopen S ∧ MoveIndependent B S ∧ moveThickening B S = univ := by
  classical
  obtain ⟨n,U,hU,hcover,hind⟩ := exists_clopen_move_separation hact hfree hbasis B
  let L := List.ofFn U
  have hL : ∀ A ∈ L, ∃ i, U i = A := fun A hA => List.mem_ofFn.mp hA
  obtain ⟨hcl,hsep,hcov⟩ := separatedCenterSet_spec hact hB h1
    (fun A hA => by obtain ⟨i,rfl⟩ := hL A hA; exact hU i)
    (fun A hA => by obtain ⟨i,rfl⟩ := hL A hA; exact hind i)
  refine ⟨separatedCenterSet B L,hcl,hsep,Set.eq_univ_of_forall fun x => ?_⟩
  obtain ⟨i,hi⟩ := hcover x
  exact hcov (U i) (List.mem_ofFn.mpr ⟨i,rfl⟩) hi

end Translates

section Coloring

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]

def activeMoves (L : Finset G) (A : Set X) (x : X) : Finset G := by
  classical
  exact L.filter fun g => g ≠ 1 ∧ g • x ∈ A

omit [TopologicalSpace X] in
theorem mem_activeMoves {L : Finset G} {A : Set X} {x : X} {g : G} :
    g ∈ activeMoves L A x ↔ g ∈ L ∧ g ≠ 1 ∧ g • x ∈ A := by
  classical
  exact Finset.mem_filter

private structure ClopenMoveColoring (L : Finset G) (k : ℕ) (A : Set X) where
  color : Fin (k+1) → Set X
  clopen : ∀ i, IsClopen (color i)
  inside : ∀ i, color i ⊆ A
  covers : ∀ x ∈ A, ∃ i, x ∈ color i
  independent : ∀ i, MoveIndependent L (color i)
  disjoint : ∀ i j, i ≠ j → Disjoint (color i) (color j)

private def ClopenMoveColoring.empty (L : Finset G) (k : ℕ) :
    ClopenMoveColoring (X := X) L k ∅ where
  color := fun _ => ∅
  clopen := fun _ => isClopen_empty
  inside := fun _ => Set.Subset.rfl
  covers := fun _ h => h.elim
  independent := fun _ _ h => h.elim
  disjoint := fun _ _ _ => Set.disjoint_left.mpr fun _ h => h.elim

open scoped Pointwise in
private theorem ClopenMoveColoring.extend
    (hact : ∀ g : G, Continuous (fun x : X => g • x))
    {L : Finset G} (hL : SymmetricMoves L) {k : ℕ} {A V : Set X}
    (C : ClopenMoveColoring L k A) (hVc : IsClopen V) (hVi : MoveIndependent L V)
    (hdeg : ∀ x ∈ V, (activeMoves L A x).card ≤ k) :
    Nonempty (ClopenMoveColoring L k (A ∪ V)) := by
  classical
  let W (i : Fin (k+1)) : Set X := ⋂ g : {g : (L : Set G) // g.val ≠ 1},
    ((fun x : X => g.val.val • x) ⁻¹' C.color i)ᶜ
  let Cpast (i : Fin (k+1)) := ⋃ j : {j : Fin (k+1) // j < i}, W j.val
  let Vnew : Set X := V \ A
  let Q (i : Fin (k+1)) : Set X := (Vnew ∩ W i) \ Cpast i
  let D (i : Fin (k+1)) : Set X := C.color i ∪ Q i
  have hA : A = ⋃ i, C.color i := by
    ext x
    exact ⟨fun hx => Set.mem_iUnion.mpr (C.covers x hx),fun hx => by
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      exact C.inside i hi⟩
  have hAc : IsClopen A := hA ▸ isClopen_iUnion_of_finite C.clopen
  have hW (i : Fin (k+1)) {x : X} : x ∈ W i ↔
      ∀ g ∈ L, g ≠ 1 → g • x ∉ C.color i := by
    constructor
    · intro hx g hg hne
      exact Set.mem_iInter.mp hx ⟨⟨g,hg⟩,hne⟩
    · intro hx
      exact Set.mem_iInter.mpr fun g => hx _ g.val.property g.property
  have hWc (i : Fin (k+1)) : IsClopen (W i) := isClopen_iInter_of_finite fun g =>
    ((C.clopen i).preimage (hact g.val.val)).compl
  have hasFresh (x : X) (hx : x ∈ V) : ∃ i : Fin (k+1), x ∈ W i := by
    by_contra! hn
    have used (i : Fin (k+1)) : ∃ g, g ∈ L ∧ g ≠ 1 ∧ g • x ∈ C.color i := by
      simpa only [hW,not_forall,not_not,exists_prop] using hn i
    choose f hfL hfne hfC using used
    let moves := activeMoves L A x
    have hm : Set.MapsTo f (↑(Finset.univ : Finset (Fin (k+1)))) (↑moves : Set G) :=
      fun i _ => mem_activeMoves.mpr ⟨hfL i,hfne i,C.inside i (hfC i)⟩
    have hi : Set.InjOn f (↑(Finset.univ : Finset (Fin (k+1)))) := by
      intro i _ j _ he
      by_contra hne
      exact Set.disjoint_left.mp (C.disjoint i j hne) (hfC i) (he.symm ▸ hfC j)
    have hcard := (Finset.card_le_card_of_injOn f hm hi).trans (hdeg x hx)
    simp at hcard
  refine ⟨⟨D,?_,?_,?_,?_,?_⟩⟩
  · intro i
    exact (C.clopen i).union (((hVc.diff hAc).inter (hWc i)).diff
      (isClopen_iUnion_of_finite fun j => hWc j.val))
  · rintro i x (hx|hx)
    · exact Or.inl (C.inside i hx)
    · exact Or.inr hx.1.1.1
  · intro x hx
    by_cases hxA : x ∈ A
    · obtain ⟨i,hi⟩ := C.covers x hxA
      exact ⟨i,Or.inl hi⟩
    · have hxV : x ∈ V := hx.resolve_left hxA
      let p (m : ℕ) := ∃ i : Fin (k+1), i.val = m ∧ x ∈ W i
      have he : ∃ m, p m := by
        obtain ⟨i,hi⟩ := hasFresh x hxV
        exact ⟨i.val,i,rfl,hi⟩
      obtain ⟨i,hi,hiW⟩ := Nat.find_spec he
      refine ⟨i,Or.inr ⟨⟨⟨hxV,hxA⟩,hiW⟩,?_⟩⟩
      intro hp
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hp
      exact Nat.find_min he (show j.val.val < Nat.find he from hi ▸ j.property) ⟨j.val,rfl,hj⟩
  · rintro i x (hx|hx) g hg hne (hgx|hgx)
    · exact C.independent i x hx g hg hne hgx
    · exact (hW i).mp hgx.1.2 g⁻¹ (hL hg) (inv_ne_one.mpr hne)
        (by simpa only [inv_smul_smul] using hx)
    · exact (hW i).mp hx.1.2 g hg hne hgx
    · exact hVi x hx.1.1.1 g hg hne hgx.1.1.1
  · intro i j hne
    apply Set.disjoint_left.mpr
    rintro x (hxi|hxi) (hxj|hxj)
    · exact Set.disjoint_left.mp (C.disjoint i j hne) hxi hxj
    · exact hxj.1.1.2 (C.inside i hxi)
    · exact hxi.1.1.2 (C.inside j hxj)
    · rcases lt_or_gt_of_ne hne with hij|hji
      · exact hxj.2 (Set.mem_iUnion.mpr ⟨⟨i,hij⟩,hxi.1.2⟩)
      · exact hxi.2 (Set.mem_iUnion.mpr ⟨⟨j,hji⟩,hxj.1.2⟩)

private theorem clopenMoveColoring_on_union
    (hact : ∀ g : G, Continuous (fun x : X => g • x))
    {L : Finset G} (hL : SymmetricMoves L) {k : ℕ} {Y : Set X}
    {l : List (Set X)} (hcl : ∀ U ∈ l, IsClopen U)
    (hsub : ∀ U ∈ l, U ⊆ Y) (hind : ∀ U ∈ l, MoveIndependent L U)
    (hdeg : ∀ x ∈ Y, (activeMoves L Y x).card ≤ k) :
    Nonempty (ClopenMoveColoring L k {x | ∃ A ∈ l, x ∈ A}) := by
  induction l with
  | nil =>
    have he : {x : X | ∃ A ∈ ([] : List (Set X)), x ∈ A} = ∅ := by
      ext x
      simp
    rw [he]
    exact ⟨ClopenMoveColoring.empty L k⟩
  | cons V l ih =>
    let A := {x : X | ∃ U ∈ l, x ∈ U}
    obtain ⟨C⟩ := ih (fun U hu => hcl U (List.mem_cons_of_mem V hu))
      (fun U hu => hsub U (List.mem_cons_of_mem V hu))
      (fun U hu => hind U (List.mem_cons_of_mem V hu))
    have hAY : A ⊆ Y := by
      rintro x ⟨u,hu,hxu⟩
      exact hsub u (List.mem_cons_of_mem V hu) hxu
    have hdeg' (x : X) (hx : x ∈ V) :
        (activeMoves L A x).card ≤ k := by
      have hsub' : activeMoves L A x ⊆ activeMoves L Y x := by
        intro g hg
        obtain ⟨hgL,hne,hgx⟩ := mem_activeMoves.mp hg
        exact mem_activeMoves.mpr ⟨hgL,hne,hAY hgx⟩
      exact (Finset.card_le_card hsub').trans (hdeg x (hsub V List.mem_cons_self hx))
    have he : {x : X | ∃ U ∈ V::l, x ∈ U} = A ∪ V := by
      ext x
      constructor
      · rintro ⟨U,hu,hxu⟩
        rcases List.mem_cons.mp hu with rfl|hu
        · exact Or.inr hxu
        · exact Or.inl ⟨U,hu,hxu⟩
      · rintro (⟨U,hu,hxu⟩|hx)
        · exact ⟨U,List.mem_cons_of_mem V hu,hxu⟩
        · exact ⟨V,List.mem_cons_self,hx⟩
    rw [he]
    exact C.extend hact hL (hcl V List.mem_cons_self) (hind V List.mem_cons_self) hdeg'

/-- A finite set of continuous move maps admits a clopen coloring using one more than
the maximum degree on a clopen subspace. -/
theorem exists_clopen_bounded_degree_coloring [T2Space X] [CompactSpace X]
    (hact : ∀ g : G, Continuous (fun x : X => g • x))
    (hfree : ∀ g : G, ∀ x : X, g • x = x → g = 1)
    (hbasis : IsTopologicalBasis {U : Set X | IsClopen U}) {L : Finset G} (hL : SymmetricMoves L)
    {Y : Set X} (hY : IsClopen Y) {k : ℕ}
    (hdeg : ∀ x ∈ Y, (activeMoves L Y x).card ≤ k) :
    ∃ C : Fin (k+1) → Set X, (∀ i, IsClopen (C i)) ∧ (∀ i, C i ⊆ Y) ∧
      (∀ x ∈ Y, ∃ i, x ∈ C i) ∧ ∀ i, MoveIndependent L (C i) := by
  classical
  obtain ⟨n,U,hUc,hcover,hind⟩ := exists_clopen_move_separation hact hfree hbasis L
  let V (i : Fin n) := U i ∩ Y
  let l := List.ofFn V
  have hLmem : ∀ A ∈ l, ∃ i, V i = A := fun A hA => List.mem_ofFn.mp hA
  have he : {x : X | ∃ A ∈ l, x ∈ A} = Y := by
    ext x
    constructor
    · rintro ⟨A,hA,hx⟩
      obtain ⟨i,rfl⟩ := hLmem A hA
      exact hx.2
    · intro hx
      obtain ⟨i,hi⟩ := hcover x
      exact ⟨V i,List.mem_ofFn.mpr ⟨i,rfl⟩,hi,hx⟩
  have cc := clopenMoveColoring_on_union hact hL
    (fun A hA => by obtain ⟨i,rfl⟩ := hLmem A hA; exact (hUc i).inter hY)
    (fun A hA x hx => by obtain ⟨i,rfl⟩ := hLmem A hA; exact hx.2)
    (fun A hA => by
      obtain ⟨i,rfl⟩ := hLmem A hA
      exact MoveIndependent.mono (hind i) Set.inter_subset_left) hdeg
  rw [he] at cc
  obtain ⟨C⟩ := cc
  exact ⟨C.color,C.clopen,C.inside,C.covers,C.independent⟩

end Coloring

section Packing

open scoped Pointwise
attribute [local instance] Classical.propDecidable

/-- Uniform control of separated configurations in a cubed finite neighborhood. -/
def UniformCubicPacking (G : Type*) [Group G] (k : ℕ) : Prop :=
  ∀ K : Finset G, ∃ B : Finset G, K ⊆ B ∧ 1 ∈ B ∧ SymmetricMoves B ∧
    ∀ T : Finset G, T ⊆ B*B*B →
      (∀ g ∈ T, ∀ h ∈ T, g ≠ h → g*h⁻¹ ∉ B) → T.card ≤ k

universe u

/-- The separated-center construction yields finite dynamic dimension from uniform
cubic packing, with all colors clopen. -/
theorem compactClopenDADLE_of_cubicPacking {G : Type u} [Group G] {k : ℕ}
    (hp : UniformCubicPacking G k) : CompactClopenDADLE G k := by
  classical
  intro X _ _ _ _ hbasis hact hfree K hK
  obtain ⟨B,hKB,h1,hB,hpack⟩ := hp K
  obtain ⟨A,hA,hAi,hAtop⟩ := exists_clopen_separated_centers hact hfree hbasis hB h1
  let L := B*K*B
  have memL (a b c : G) (ha : a ∈ B) (hb : b ∈ K) (hc : c ∈ B) :
      a*b*c ∈ L :=
    Finset.mem_mul.mpr ⟨a*b,Finset.mem_mul.mpr ⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩
  have listL {g : G} (hg : g ∈ L) : ∃ a ∈ B, ∃ b ∈ K, ∃ c ∈ B, a*b*c = g := by
    obtain ⟨d,hd,c,hc,rfl⟩ := Finset.mem_mul.mp hg
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hd
    exact ⟨a,ha,b,hb,c,hc,rfl⟩
  have hL : SymmetricMoves L := by
    intro g hg
    obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := listL hg
    simpa only [mul_inv_rev,mul_assoc] using memL _ _ _ (hB hc) (hK hb) (hB ha)
  have hdeg (x : X) (_ : x ∈ A) : (activeMoves L A x).card ≤ k := by
    apply hpack
    · intro g hg
      obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := listL (mem_activeMoves.mp hg).1
      exact Finset.mem_mul.mpr ⟨a*b,Finset.mem_mul.mpr ⟨a,ha,b,hKB hb,rfl⟩,c,hc,rfl⟩
    · intro g hg h hh hne hin
      have hgA := (mem_activeMoves.mp hg).2.2
      have hhA := (mem_activeMoves.mp hh).2.2
      have hgh : g*h⁻¹ ≠ 1 := by
        intro he
        apply hne
        simpa using congrArg (fun z : G => z*h) he
      exact hAi (h • x) hhA (g*h⁻¹) hin hgh (by rwa [mul_smul,inv_smul_smul])
  obtain ⟨C,hC,_,hCcover,hCi⟩ := exists_clopen_bounded_degree_coloring hact hfree hbasis hL hA hdeg
  refine ⟨fun i => moveThickening B (C i),fun i => isClopen_moveThickening hact B (hC i),?_,
    B.card,?_⟩
  · intro x
    have hx : x ∈ moveThickening B A := hAtop.symm ▸ Set.mem_univ _
    obtain ⟨g,hg,z,hz,rfl⟩ := hx
    obtain ⟨i,hi⟩ := hCcover z hz
    exact ⟨i,g,hg,z,hi,rfl⟩
  · intro i x
    by_cases hx : x ∈ moveThickening B (C i)
    · obtain ⟨g0,hg0,a,ha,ha0⟩ := hx
      refine ⟨B.image (fun g => g • a),Finset.card_image_le,?_⟩
      intro y hy
      have hc {w : X} (p : Relation.ReflTransGen (TestEdge K (moveThickening B (C i))) x w) :
          ∃ g ∈ B, g • a = w := by
        induction p with
        | refl => exact ⟨g0,hg0,ha0⟩
        | @tail v w p e ih =>
          obtain ⟨g,hg,hgv⟩ := ih
          obtain ⟨j,hj,b,hb,hjw⟩ := e.2.1
          obtain ⟨t,ht,htw⟩ := e.2.2
          have hmove : (j⁻¹*t*g) • a = b := by
            rw [mul_smul,mul_smul,hgv,← mul_smul,mul_smul,htw,← hjw,inv_smul_smul]
          have hIdentity : j⁻¹*t*g = 1 := by
            by_contra hne
            exact hCi i a ha _ (memL _ _ _ (hB hj) ht hg) hne (hmove.symm ▸ hb)
          have hab : a = b := by simpa only [hIdentity,one_smul] using hmove
          exact ⟨j,hj,hab.symm ▸ hjw⟩
      obtain ⟨g,hg,hgy⟩ := hc hy.2
      exact Finset.mem_image.mpr ⟨g,hg,hgy⟩
    · exact ⟨∅,by simp,fun _ h => (hx h.1).elim⟩

/-- Every action of a locally finite group has the one-set finite-component bound. -/
theorem compactClopenDADLE_zero_of_locallyFinite {G : Type u} [Group G]
    (h : IsLocallyFiniteGroup G) : CompactClopenDADLE G 0 := by
  classical
  intro X _ _ _ _ _ _ _ K _
  let H := Subgroup.closure (K : Set G)
  letI : Finite H := h H ⟨K,rfl⟩
  letI := Fintype.ofFinite H
  refine ⟨fun _ => univ,fun _ => isClopen_univ,fun x => ⟨0,Set.mem_univ x⟩,
    Fintype.card H,fun i x => ?_⟩
  refine ⟨Finset.univ.image (fun g : H => (g.val : G) • x),
    Finset.card_image_le.trans (by simp),?_⟩
  intro y hy
  have reach {z : X} (p : Relation.ReflTransGen (TestEdge K univ) x z) :
      ∃ a : H, (a.val : G) • x = z := by
    induction p with
    | refl => exact ⟨1,one_smul _ _⟩
    | @tail v w p e ih =>
      obtain ⟨a,ha⟩ := ih
      obtain ⟨g,hg,hgw⟩ := e.2.2
      let b : H := ⟨g,Subgroup.subset_closure hg⟩
      exact ⟨b*a,by change (g*a.val) • x = w; rw [mul_smul,ha,hgw]⟩
  obtain ⟨a,ha⟩ := reach hy.2
  exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha⟩

end Packing

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.ClopenPacking

-- BEGIN COMPLETE MODULE HirschProof.ClopenSaturation
section
                                

set_option autoImplicit false
noncomputable section

open Set Topology TopologicalSpace
open scoped Pointwise

namespace LocalHirschHyperfinite

section Saturation

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]

/-- One component can be viewed through several finite displacement charts. -/
def translatedComponentHit (K : Finset G) (A : Set X) (E : Finset G)
    (U : Set X) : Set X :=
  {x | ∃ a ∈ E, ∃ b ∈ E, ∃ y ∈ U, TestComponent K A (a⁻¹ • x) (b⁻¹ • y)}

omit [TopologicalSpace X] in
theorem translatedComponentHit_mono {K E : Finset G} {A U V : Set X} (h : U ⊆ V) :
    translatedComponentHit K A E U ⊆ translatedComponentHit K A E V := by
  rintro x ⟨a,ha,b,hb,y,hy,he⟩
  exact ⟨a,ha,b,hb,y,h hy,he⟩

/-- Saturating a clopen region by finitely many translates of bounded components is
a clopen operation. -/
theorem isClopen_translatedComponentHit
    (hact : ∀ g : G, Continuous (fun x : X => g • x))
    (hfree : ∀ g : G, ∀ x : X, g • x = x → g = 1)
    {K E V : Finset G} {A U : Set X} (hA : IsClopen A) (hU : IsClopen U)
    (hV : ∀ x y, TestComponent K A x y → ∃ g ∈ V, g • x = y) :
    IsClopen (translatedComponentHit K A E U) := by
  let R (a b g : G) : Set X := ((fun x : X => a⁻¹ • x) ⁻¹'
    {x | TestComponent K A x (g • x)}) ∩
    (fun x : X => b • (g • (a⁻¹ • x))) ⁻¹' U
  have he : translatedComponentHit K A E U =
      ⋃ a : (E : Set G), ⋃ b : (E : Set G), ⋃ g : (V : Set G), R a.val b.val g.val := by
    ext x
    constructor
    · rintro ⟨a,ha,b,hb,y,hy,h⟩
      obtain ⟨g,hg,he⟩ := hV _ _ h
      refine Set.mem_iUnion.mpr ⟨⟨a,ha⟩,Set.mem_iUnion.mpr ⟨⟨b,hb⟩,
        Set.mem_iUnion.mpr ⟨⟨g,hg⟩,?_⟩⟩⟩
      refine ⟨?_,?_⟩
      · change TestComponent K A (a⁻¹ • x) (g • (a⁻¹ • x))
        rw [he]
        exact h
      · change b • (g • (a⁻¹ • x)) ∈ U
        rw [he,smul_inv_smul]
        exact hy
    · intro hx
      obtain ⟨a,hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨b,hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨g,hx⟩ := Set.mem_iUnion.mp hx
      refine ⟨a.val,a.property,b.val,b.property,b.val • (g.val • (a.val⁻¹ • x)),hx.2,?_⟩
      simpa only [inv_smul_smul] using hx.1
  rw [he]
  refine isClopen_iUnion_of_finite fun a => isClopen_iUnion_of_finite fun b =>
    isClopen_iUnion_of_finite fun g => ?_
  exact ((isClopen_testComponent hact hfree hA hV g.val).preimage (hact _)).inter
    (hU.preimage ((hact _).comp ((hact _).comp (hact _))))

/-- Saturation across several finite displacement charts. -/
def saturateTranslatedComponents {I : Type*} (K : Finset G) (A : Set X)
    (E : I → Finset G) (U : Set X) : Set X :=
  U ∪ ⋃ i, translatedComponentHit K A (E i) U

theorem isClopen_saturateTranslatedComponents {I : Type*} [Finite I]
    (hact : ∀ g : G, Continuous (fun x : X => g • x))
    (hfree : ∀ g : G, ∀ x : X, g • x = x → g = 1)
    {K V : Finset G} {A U : Set X} (hA : IsClopen A) (hU : IsClopen U)
    (hV : ∀ x y, TestComponent K A x y → ∃ g ∈ V, g • x = y) (E : I → Finset G) :
    IsClopen (saturateTranslatedComponents K A E U) :=
  hU.union (isClopen_iUnion_of_finite fun _ => isClopen_translatedComponentHit hact hfree hA hU hV)

end Saturation

section CompatibleCharts

variable {G X I : Type*} [Group G] [MulAction G X]

private def TranslateRelated (K : Finset G) (A : Set X) (E : I → Finset G) (x y : X) : Prop :=
  ∃ i, ∃ a ∈ E i, ∃ b ∈ E i, TestComponent K A (a⁻¹ • x) (b⁻¹ • y)

private theorem mem_saturateTranslatedComponents {K : Finset G} {A U : Set X}
    {E : I → Finset G} {x : X} :
    x ∈ saturateTranslatedComponents K A E U ↔ x ∈ U ∨
      ∃ y ∈ U, TranslateRelated K A E x y := by
  constructor
  · rintro (hx|hx)
    · exact Or.inl hx
    · obtain ⟨i,a,ha,b,hb,y,hy,h⟩ := Set.mem_iUnion.mp hx
      exact Or.inr ⟨y,hy,i,a,ha,b,hb,h⟩
  · rintro (hx|⟨y,hy,i,a,ha,b,hb,h⟩)
    · exact Or.inl hx
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i,a,ha,b,hb,y,hy,h⟩)

private theorem translateRelated_trans {K : Finset G} {A : Set X} {E : I → Finset G}
    (halign : ∀ i j y, ∀ a ∈ E i, ∀ b ∈ E j, a⁻¹ • y ∈ A → b⁻¹ • y ∈ A →
      E i = E j ∧ TestComponent K A (a⁻¹ • y) (b⁻¹ • y)) :
    ∀ ⦃x y z⦄, TranslateRelated K A E x y → TranslateRelated K A E y z →
      TranslateRelated K A E x z := by
  rintro x y z ⟨i,a,ha,b,hb,hxy⟩ ⟨j,c,hc,d,hd,hyz⟩
  obtain ⟨he,hbc⟩ := halign i j y b hb c hc (testComponent_end hxy) hyz.1
  exact ⟨i,a,ha,d,he.symm ▸ hd,testComponent_trans (testComponent_trans hxy hbc) hyz⟩

/-- Alignment at every overlap makes translated saturation idempotent. -/
theorem saturateTranslatedComponents_idempotent {K : Finset G} {A : Set X} {E : I → Finset G}
    (halign : ∀ i j y, ∀ a ∈ E i, ∀ b ∈ E j, a⁻¹ • y ∈ A → b⁻¹ • y ∈ A →
      E i = E j ∧ TestComponent K A (a⁻¹ • y) (b⁻¹ • y)) (U : Set X) :
    saturateTranslatedComponents K A E (saturateTranslatedComponents K A E U) =
      saturateTranslatedComponents K A E U := by
  ext x
  rw [mem_saturateTranslatedComponents]
  constructor
  · rintro (hx|⟨y,hy,hxy⟩)
    · exact hx
    · apply mem_saturateTranslatedComponents.mpr
      rcases mem_saturateTranslatedComponents.mp hy with hy|⟨z,hz,hyz⟩
      · exact Or.inr ⟨y,hy,hxy⟩
      · exact Or.inr ⟨z,hz,translateRelated_trans halign hxy hyz⟩
  · exact Or.inl

/-- A set fixed by translated saturation contains an entire translated
component once it meets any point of that component. -/
theorem moveThickening_component_subset_of_hit {K : Finset G} {A U : Set X}
    {E : I → Finset G} (hK : SymmetricMoves K)
    (hU : saturateTranslatedComponents K A E U = U) (i : I) {x : X}
    (hhit : ∃ y ∈ U, y ∈ moveThickening (E i) {z | TestComponent K A x z}) :
    moveThickening (E i) {z | TestComponent K A x z} ⊆ U := by
  rintro z ⟨a,ha,z',hz',rfl⟩
  obtain ⟨y,hy,b,hb,y',hy',rfl⟩ := hhit
  have hh : TestComponent K A z' y' := testComponent_trans (testComponent_symm hK hz') hy'
  rw [← hU]
  exact mem_saturateTranslatedComponents.mpr (Or.inr ⟨b • y',hy,i,a,ha,b,hb,by
    simpa only [inv_smul_smul] using hh⟩)

/-- Thickening by two finite sets is thickening by their setwise product. -/
theorem moveThickening_mul [DecidableEq G] (S T : Finset G) (A : Set X) :
    moveThickening S (moveThickening T A) = moveThickening (S*T) A := by
  ext x
  constructor
  · rintro ⟨s,hs,_,⟨t,ht,y,hy,rfl⟩,rfl⟩
    exact ⟨s*t,Finset.mem_mul.mpr ⟨s,hs,t,ht,rfl⟩,y,hy,mul_smul _ _ _⟩
  · rintro ⟨g,hg,y,hy,rfl⟩
    obtain ⟨s,hs,t,ht,rfl⟩ := Finset.mem_mul.mp hg
    exact ⟨s,hs,t • y,⟨t,ht,y,hy,rfl⟩,(mul_smul _ _ _).symm⟩

end CompatibleCharts

section OrderedSaturations

variable {X G : Type*} [Group G] [MulAction G X]

/-- Compose a finite run of saturations with smaller stages acting last. -/
def foldClopenSaturation (f : ℕ → Set X → Set X) (a : ℕ) : ℕ → Set X → Set X
  | 0, U => U
  | n+1, U => f a (foldClopenSaturation f (a+1) n U)

theorem foldClopenSaturation_add (f : ℕ → Set X → Set X) (a n m : ℕ) (U : Set X) :
    foldClopenSaturation f a (n+m) U =
      foldClopenSaturation f a n (foldClopenSaturation f (a+n) m U) := by
  induction n generalizing a with
  | zero => simp [foldClopenSaturation]
  | succ n ih =>
    rw [show n+1+m = n+m+1 by omega,foldClopenSaturation,ih,foldClopenSaturation]
    rw [show a+1+n = a+(n+1) by omega]

theorem subset_foldClopenSaturation {f : ℕ → Set X → Set X}
    (hf : ∀ a U, U ⊆ f a U) (a n : ℕ) (U : Set X) :
    U ⊆ foldClopenSaturation f a n U := by
  induction n generalizing a with
  | zero => exact Subset.rfl
  | succ n ih => exact (ih (a+1)).trans (hf a _)

theorem foldClopenSaturation_thickens {f : ℕ → Set X → Set X}
    {A : ℕ → Finset G}
    (hf : ∀ a U, moveThickening (A a) (f a U) ⊆ moveThickening (A (a+1)) U)
    (a n : ℕ) (U : Set X) :
    moveThickening (A a) (foldClopenSaturation f a n U) ⊆ moveThickening (A (a+n)) U := by
  induction n generalizing a with
  | zero => simp [foldClopenSaturation]
  | succ n ih =>
    rw [foldClopenSaturation,show a+(n+1) = a+1+n by omega]
    exact (hf a _).trans (ih (a+1))

theorem isClopen_foldClopenSaturation [TopologicalSpace X] {f : ℕ → Set X → Set X}
    (hf : ∀ a U, IsClopen U → IsClopen (f a U)) (a n : ℕ) {U : Set X} (hU : IsClopen U) :
    IsClopen (foldClopenSaturation f a n U) := by
  induction n generalizing a with
  | zero => exact hU
  | succ n ih => exact hf a _ (ih (a+1))

theorem foldClopenSaturation_fixed {f : ℕ → Set X → Set X}
    (hf : ∀ a U, f a (f a U) = f a U) (a : ℕ) {n : ℕ} (hn : 0 < n) (U : Set X) :
    f a (foldClopenSaturation f a n U) = foldClopenSaturation f a n U := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact hf a _

end OrderedSaturations

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.ClopenSaturation

-- BEGIN COMPLETE MODULE HirschProof.RationalIsolatorWitnesses
section
                                    
                                                 
                                                   
                                          

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set TensorProduct

/-- A class maps to zero in the rationalization precisely when a positive
integer kills it. -/
theorem rationalization_eq_zero_iff {A : Type*} [AddCommGroup A] (a : A) :
    (1 : ℚ) ⊗ₜ[ℤ] a = 0 ↔ ∃ n : ℕ, 0 < n ∧ n • a = 0 := by
  let t := TensorProduct.mk ℤ ℚ A 1
  let S := nonZeroDivisors ℤ
  haveI : IsLocalizedModule S t := IsLocalization.tensorProduct_isLocalizedModule S ℚ
  change t a = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff S t]
  constructor
  · rintro ⟨s,hs⟩
    have hs' : (s : ℤ) ≠ 0 := nonZeroDivisors.ne_zero s.property
    change (s : ℤ) • a = 0 at hs
    refine ⟨(s : ℤ).natAbs,Nat.pos_of_ne_zero (fun h => hs' (Int.natAbs_eq_zero.mp h)),?_⟩
    rcases Int.natAbs_eq (s : ℤ) with h|h
    · rw [h] at hs
      simpa only [natCast_zsmul] using hs
    · rw [h,neg_smul,natCast_zsmul,neg_eq_zero] at hs
      exact hs
  · rintro ⟨n,hn,ha⟩
    have hne : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    refine ⟨⟨n,mem_nonZeroDivisors_of_ne_zero hne⟩,?_⟩
    change (n : ℤ) • a = 0
    simpa only [natCast_zsmul] using ha

/-- In a commutative group of finite rational rank, choose finitely many
elements whose rationalizations span the image of the subgroup. -/
theorem finiteIsolatorWitness_of_finite_rationalization {G : Type*} [CommGroup G]
    [Module.Finite ℚ (ℚ ⊗[ℤ] Additive G)] : HasFiniteIsolatorWitness G := by
  classical
  intro H
  let t := TensorProduct.mk ℤ ℚ (Additive G) 1
  let u : G → ℚ ⊗[ℤ] Additive G := fun x => t (Additive.ofMul x)
  let W := Submodule.span ℚ (u '' (H : Set G))
  have hW : W.FG := IsNoetherian.noetherian W
  obtain ⟨S,hS,hSW⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hW
  have hLift (a : (S : Set (ℚ ⊗[ℤ] Additive G))) : ∃ x ∈ H, u x = a := hS a.property
  choose σ hσH hσ using hLift
  let T := range σ
  have hT : T.Finite := finite_range σ
  let H₀ := Subgroup.closure T
  have hH₀ : H₀ ≤ H := (Subgroup.closure_le _).mpr (by rintro _ ⟨a,rfl⟩; exact hσH a)
  have hH₀f : H₀.FG := (Subgroup.fg_iff _).mpr ⟨T,rfl,hT⟩
  refine ⟨H₀,hH₀,hH₀f,le_antisymm (nilpotentIsolator_mono hH₀) ?_⟩
  let N := H₀.toAddSubgroup.toIntSubmodule
  let q := N.mkQ
  let f := q.baseChange ℚ
  have hzero : Submodule.span ℚ (S : Set (ℚ ⊗[ℤ] Additive G)) ≤ f.ker := by
    rw [Submodule.span_le]
    intro a ha
    let b : (S : Set (ℚ ⊗[ℤ] Additive G)) := ⟨a,ha⟩
    have hmem : Additive.ofMul (σ b) ∈ N := by
      change σ b ∈ H₀
      exact Subgroup.subset_closure ⟨b,rfl⟩
    have hq : q (Additive.ofMul (σ b)) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hmem
    change f a = 0
    have hb : u (σ b) = a := hσ b
    rw [← hb]
    change q.baseChange ℚ (1 ⊗ₜ[ℤ] (Additive.ofMul (σ b))) = 0
    rw [LinearMap.baseChange_tmul,hq,tmul_zero]
  have hHI : H ≤ nilpotentIsolator H₀ := by
    intro x hx
    have hxW : u x ∈ (Submodule.span ℚ (S : Set (ℚ ⊗[ℤ] Additive G))) := by
      rw [← hSW]
      exact Submodule.subset_span ⟨x,hx,rfl⟩
    have hqx : (1 : ℚ) ⊗ₜ[ℤ] q (Additive.ofMul x) = 0 := by
      exact (q.baseChange_tmul (1 : ℚ) (Additive.ofMul x)).symm.trans (hzero hxW)
    obtain ⟨n,hn,hnx⟩ := (rationalization_eq_zero_iff _).mp hqx
    refine ⟨n,hn,?_⟩
    have hz : q (n • Additive.ofMul x) = 0 := by
      rw [map_nsmul,hnx]
    exact (Submodule.Quotient.mk_eq_zero N).mp hz
  simpa only [nilpotentIsolator_idempotent] using nilpotentIsolator_mono hHI

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.RationalIsolatorWitnesses

-- BEGIN COMPLETE MODULE HirschProof.SolvableRationalRank
section
                                            
                                                         
                                         

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set TensorProduct

theorem rationalization_injective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →ₗ[ℤ] B) (hf : Function.Injective f) : Function.Injective (f.baseChange ℚ) := by
  let S := nonZeroDivisors ℤ
  let t := TensorProduct.mk ℤ ℚ A 1
  haveI : IsLocalizedModule S t := IsLocalization.tensorProduct_isLocalizedModule S ℚ
  apply (LinearMap.ker_eq_bot).mp
  rw [eq_bot_iff]
  intro y hy
  change f.baseChange ℚ y = 0 at hy
  change y = 0
  obtain ⟨⟨a,s⟩,hsa⟩ := IsLocalizedModule.surj S t y
  have hsa' : (s : ℤ) • y = t a := hsa
  have hz : (1 : ℚ) ⊗ₜ[ℤ] f a = 0 := calc
    _ = f.baseChange ℚ (t a) := (f.baseChange_tmul _ _).symm
    _ = (s : ℤ) • (f.baseChange ℚ y) := by rw [← hsa',map_zsmul]
    _ = 0 := by rw [hy,zsmul_zero]
  obtain ⟨n,hn,hna⟩ := (rationalization_eq_zero_iff _).mp hz
  have hna' : n • a = 0 := hf (by rw [map_nsmul,hna,map_zero])
  have hta : t a = 0 := (rationalization_eq_zero_iff _).mpr ⟨n,hn,hna'⟩
  have hsz : s • y = s • (0 : ℚ ⊗[ℤ] A) := by rw [hsa,hta,smul_zero]
  exact (IsLocalizedModule.smul_inj t s y 0).mp hsz

theorem finite_rationalization_of_injective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℚ (ℚ ⊗[ℤ] B)] (f : A →ₗ[ℤ] B) (hf : Function.Injective f) :
    Module.Finite ℚ (ℚ ⊗[ℤ] A) := by
  letI := isNoetherian_of_injective (f.baseChange ℚ) (rationalization_injective f hf)
  infer_instance

theorem finite_rationalization_of_surjective {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℚ (ℚ ⊗[ℤ] A)] (f : A →ₗ[ℤ] B) (hf : Function.Surjective f) :
    Module.Finite ℚ (ℚ ⊗[ℤ] B) :=
  Module.Finite.of_surjective _ (f.baseChange_surjective ℚ hf)

theorem finite_rationalization_of_exact {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module.Finite ℚ (ℚ ⊗[ℤ] A)] [Module.Finite ℚ (ℚ ⊗[ℤ] C)]
    (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C) (h : Function.Exact f g) (hg : Function.Surjective g) :
    Module.Finite ℚ (ℚ ⊗[ℤ] B) := by
  have ht : Function.Exact (f.baseChange ℚ) (g.baseChange ℚ) := lTensor_exact ℚ h hg
  letI := isNoetherian_of_range_eq_ker (f.baseChange ℚ) (g.baseChange ℚ) ht.linearMap_ker_eq.symm
  infer_instance

private theorem abelianization_map_surjective {G J : Type*} [Group G] [Group J]
    (f : G →* J) (hf : Function.Surjective f) : Function.Surjective (Abelianization.map f) := by
  intro y
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (commutator J) y
  obtain ⟨a,rfl⟩ := hf x
  exact ⟨Abelianization.of a,rfl⟩

/-- A quotient of a solvable group of finite Hirsch length also has finite
Hirsch length. -/
theorem IsSolvableFiniteHirsch.of_surjective {G J : Type*} [Group G] [Group J]
    (h : IsSolvableFiniteHirsch G) (f : G →* J) (hf : Function.Surjective f) :
    IsSolvableFiniteHirsch J := by
  letI : IsSolvable G := h.1
  refine ⟨solvable_of_surjective hf,?_⟩
  intro n
  let p : derivedSeries G n →* derivedSeries J n := {
    toFun := fun x => ⟨f x.val,map_derivedSeries_le_derivedSeries f n ⟨x.val,x.property,rfl⟩⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }
  have hp : Function.Surjective p := by
    intro y
    have hy : y.val ∈ (derivedSeries G n).map f := (map_derivedSeries_eq hf n).symm ▸ y.property
    obtain ⟨x,hx,hxy⟩ := hy
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  letI : Module.Finite ℚ (RationalDerivedFactor G n) := h.2 n
  exact finite_rationalization_of_surjective (Abelianization.map p).toAdditive.toIntLinearMap
    (abelianization_map_surjective p hp)

private theorem finite_rationalization_range_of_kernel_image {P A B : Type*}
    [Group P] [CommGroup A] [CommGroup B] (p : P →* B) (f : P →* A)
    [Module.Finite ℚ (ℚ ⊗[ℤ] Additive B)]
    (h : Module.Finite ℚ (ℚ ⊗[ℤ] Additive (p.ker.map f))) :
    Module.Finite ℚ (ℚ ⊗[ℤ] Additive f.range) := by
  let F := f.rangeRestrict
  let C := p.ker.map F
  let π := QuotientGroup.mk' C
  have hKer : p.ker ≤ (π.comp F).ker := by
    intro x hx
    change π (F x) = 1
    exact (QuotientGroup.eq_one_iff _).mpr ⟨x,hx,rfl⟩
  let q : P ⧸ p.ker →* f.range ⧸ C := QuotientGroup.lift p.ker (π.comp F) hKer
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective C y
    obtain ⟨a,ha⟩ := f.rangeRestrict_surjective b
    exact ⟨QuotientGroup.mk a,congrArg π ha⟩
  let e := QuotientGroup.quotientKerEquivRange p
  let r := q.comp e.symm.toMonoidHom
  letI : Module.Finite ℚ (ℚ ⊗[ℤ] Additive p.range) :=
    finite_rationalization_of_injective p.range.subtype.toAdditive.toIntLinearMap p.range.subtype_injective
  letI : Module.Finite ℚ (ℚ ⊗[ℤ] Additive (f.range ⧸ C)) :=
    finite_rationalization_of_surjective r.toAdditive.toIntLinearMap (hq.comp e.symm.surjective)
  have hC : C.map f.range.subtype = p.ker.map f := by
    change (p.ker.map F).map f.range.subtype = p.ker.map f
    rw [Subgroup.map_map]
    rfl
  let j := C.equivMapOfInjective f.range.subtype f.range.subtype_injective
  letI : Module.Finite ℚ (ℚ ⊗[ℤ] Additive (C.map f.range.subtype)) := hC.symm ▸ h
  letI : Module.Finite ℚ (ℚ ⊗[ℤ] Additive C) :=
    finite_rationalization_of_injective j.toMonoidHom.toAdditive.toIntLinearMap j.injective
  have hex : Function.Exact C.subtype.toAdditive.toIntLinearMap π.toAdditive.toIntLinearMap := by
    intro x
    change (QuotientGroup.mk x : f.range ⧸ C) = 1 ↔ x ∈ range C.subtype
    rw [QuotientGroup.eq_one_iff]
    exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩,fun ⟨c,hc⟩ => hc ▸ c.property⟩
  exact finite_rationalization_of_exact _ _ hex (QuotientGroup.mk'_surjective C)

/-- Every abelian image of a subgroup of a finite-Hirsch solvable group has
finite rational rank. Filter the subgroup by its intersections with the
ambient derived series. -/
theorem finite_rationalization_range_of_solvableFiniteHirsch {G A : Type*}
    [Group G] [CommGroup A] (h : IsSolvableFiniteHirsch G) (H : Subgroup G) (f : H →* A) :
    Module.Finite ℚ (ℚ ⊗[ℤ] Additive f.range) := by
  obtain ⟨n,hn⟩ := h.1.solvable
  let K (i : ℕ) := (derivedSeries G i).subgroupOf H
  let F (i : ℕ) := f.comp (K i).subtype
  let R (i : ℕ) := Module.Finite ℚ (ℚ ⊗[ℤ] Additive (F i).range)
  have hbase : R n := by
    have hk : K n = ⊥ := by change (derivedSeries G n).subgroupOf H = ⊥; rw [hn]; simp
    have hF : (F n).range = ⊥ := by
      apply bot_unique
      rintro _ ⟨x,rfl⟩
      have hx : x.val ∈ (⊥ : Subgroup H) := hk ▸ x.property
      have hx' : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hx)
      rw [hx',map_one]
      exact Subgroup.one_mem _
    letI : Subsingleton (F n).range := hF.symm ▸ inferInstanceAs (Subsingleton (⊥ : Subgroup A))
    change Module.Finite ℚ (ℚ ⊗[ℤ] Additive (F n).range)
    infer_instance
  have hstep (i : ℕ) (hi : R (i+1)) : R i := by
    let j : K i →* derivedSeries G i := {
      toFun := fun x => ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    let p := Abelianization.of.comp j
    have hpker (x : K i) : x ∈ p.ker ↔ x.val.val ∈ derivedSeries G (i+1) := by
      change j x ∈ (Abelianization.of : derivedSeries G i →* _).ker ↔ _
      rw [Abelianization.ker_of]
      calc
        _ ↔ (j x).val ∈ (commutator (derivedSeries G i)).map (derivedSeries G i).subtype :=
          (Subgroup.mem_map_iff_mem (f := (derivedSeries G i).subtype)
            (derivedSeries G i).subtype_injective).symm
        _ ↔ _ := by rw [Subgroup.map_subtype_commutator,← derivedSeries_succ]; rfl
    have hmap : p.ker.map (F i) = (F (i+1)).range := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨⟨x.val,(hpker x).mp hx⟩,rfl⟩
      · rintro ⟨x,rfl⟩
        let a : K i := ⟨x.val,derivedSeries_antitone G (Nat.le_succ i) x.property⟩
        exact ⟨a,(hpker a).mpr x.property,rfl⟩
    letI : Module.Finite ℚ (RationalDerivedFactor G i) := h.2 i
    exact finite_rationalization_range_of_kernel_image p (F i) (hmap.symm ▸ hi)
  have hdown (m : ℕ) : ∀ i, m+i=n → R i := by
    induction m with
    | zero =>
      intro i hi
      rw [Nat.zero_add] at hi
      exact hi.symm ▸ hbase
    | succ m ih => intro i hi; exact hstep i (ih (i+1) (by omega))
  have hF0 : (F 0).range = f.range := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,by change x.val ∈ derivedSeries G 0; simp⟩,rfl⟩
  exact hF0 ▸ hdown n 0 (Nat.add_zero n)

/-- Every commutative group that is a quotient of a subgroup has finite
rational rank when the ambient group is solvable of finite Hirsch length. -/
theorem finite_rationalization_of_solvableFiniteHirsch {G A : Type*}
    [Group G] [CommGroup A] (h : IsSolvableFiniteHirsch G) (H : Subgroup G) (f : H →* A)
    (hf : Function.Surjective f) : Module.Finite ℚ (ℚ ⊗[ℤ] Additive A) := by
  letI := finite_rationalization_range_of_solvableFiniteHirsch h H f
  exact finite_rationalization_of_surjective f.range.subtype.toAdditive.toIntLinearMap (by
    intro a
    obtain ⟨x,rfl⟩ := hf a
    exact ⟨⟨f x,⟨x,rfl⟩⟩,rfl⟩)

/-- Subgroups inherit solvability and finite Hirsch length. -/
theorem IsSolvableFiniteHirsch.subgroup {G : Type*} [Group G]
    (h : IsSolvableFiniteHirsch G) (H : Subgroup G) : IsSolvableFiniteHirsch H := by
  letI : IsSolvable G := h.1
  refine ⟨inferInstance,?_⟩
  intro n
  let J := derivedSeries H n
  let e := J.equivMapOfInjective H.subtype H.subtype_injective
  let f : J.map H.subtype →* Abelianization J := Abelianization.of.comp e.symm.toMonoidHom
  exact finite_rationalization_of_solvableFiniteHirsch h _ f
    ((QuotientGroup.mk'_surjective (commutator J)).comp e.symm.surjective)

/-- A nilpotent group of finite Hirsch length has finite isolator witnesses.
The proof removes the last nontrivial central layer at each induction step. -/
theorem finiteIsolatorWitness_of_nilpotent_finiteHirsch {G : Type*} [Group G] [Group.IsNilpotent G]
    (h : IsSolvableFiniteHirsch G) : HasFiniteIsolatorWitness G := by
  have main (n : ℕ) : ∀ (Q : Type _) [Group Q] [Group.IsNilpotent Q],
      Subgroup.lowerCentralSeries Q n = ⊥ → IsSolvableFiniteHirsch Q → HasFiniteIsolatorWitness Q := by
    induction n with
    | zero =>
      intro Q _ _ hn _ H
      have htop : (⊤ : Subgroup Q) = ⊥ := hn
      have hbot : H = ⊥ := bot_unique (htop ▸ le_top)
      have hH : H.FG := (Subgroup.fg_iff H).mpr
        ⟨∅,by rw [Subgroup.closure_empty,hbot],finite_empty⟩
      exact ⟨H,le_rfl,hH,rfl⟩
    | succ n ih =>
      intro Q _ _ hn hQ
      let C := Subgroup.lowerCentralSeries Q n
      let q := QuotientGroup.mk' C
      have hc : C ≤ Subgroup.center Q := last_lowerCentral_le_center n hn
      let gC : Group C := inferInstance
      letI : CommGroup C := { gC with
        mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hc y.property) x.val) }
      letI : Module.Finite ℚ (ℚ ⊗[ℤ] Additive C) :=
        finite_rationalization_of_solvableFiniteHirsch hQ C (MonoidHom.id C) Function.surjective_id
      have hq : Subgroup.lowerCentralSeries (Q ⧸ C) n = ⊥ := by
        rw [← map_lowerCentralSeries_surjective q (QuotientGroup.mk'_surjective C)]
        exact (Subgroup.map_eq_bot_iff C).mpr (by simp [q])
      exact HasFiniteIsolatorWitness.centralExtension C hc
        finiteIsolatorWitness_of_finite_rationalization
        (ih _ hq (hQ.of_surjective q (QuotientGroup.mk'_surjective C)))
  obtain ⟨n,hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent G)
  exact main n G hn h

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.SolvableRationalRank

-- BEGIN COMPLETE MODULE HirschProof.LatticePacking
section
                                
                                       
                                
                                
                                           
                                                    

set_option autoImplicit false
noncomputable section

open Set Topology TopologicalSpace
open scoped Pointwise

namespace LocalHirschHyperfinite

/-- Each finite test set is in the image of a lattice of fixed rank. -/
def HasBoundedIntegerLifts (G : Type*) [Group G] (e : ℕ) : Prop :=
  ∀ K : Finset G, ∃ f : Multiplicative (Fin e → ℤ) →* G,
    ∀ g ∈ K, g ∈ Set.range f

private def intBox (e : ℕ) (s : ℤ) : Finset (Fin e → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(s : ℤ)) s)

private theorem mem_intBox {e : ℕ} {s : ℤ} {v : Fin e → ℤ} :
    v ∈ intBox e s ↔ ∀ i, -s ≤ v i ∧ v i ≤ s := by
  simp only [intBox,Fintype.mem_piFinset,Finset.mem_Icc]

section Packing
attribute [local instance] Classical.decEq

variable {G : Type*} [Group G]

private def latticeImage {e : ℕ} (f : Multiplicative (Fin e → ℤ) →* G) (s : ℤ) : Finset G := by
  classical
  exact (intBox e s).image (fun v => f (Multiplicative.ofAdd v))

private theorem mem_latticeImage {e : ℕ} {f : Multiplicative (Fin e → ℤ) →* G} {s : ℤ} {g : G} :
    g ∈ latticeImage f s ↔ ∃ v : Fin e → ℤ, (∀ i, -s ≤ v i ∧ v i ≤ s) ∧
      f (Multiplicative.ofAdd v) = g := by
  classical
  simp only [latticeImage,Finset.mem_image,mem_intBox]

private theorem exists_latticeImage_bound {e : ℕ} {f : Multiplicative (Fin e → ℤ) →* G}
    {K : Finset G} (hK : ∀ g ∈ K, g ∈ Set.range f) :
    ∃ n : ℕ, K ⊆ latticeImage f n := by
  classical
  have hex (g : G) : ∃ v : Fin e → ℤ, g ∈ K → f (Multiplicative.ofAdd v) = g := by
    by_cases hg : g ∈ K
    · obtain ⟨v,he⟩ := hK g hg
      exact ⟨Multiplicative.toAdd v,fun _ => he⟩
    · exact ⟨0,fun h => (hg h).elim⟩
  choose v hv using hex
  let R (g : G) := (Finset.univ : Finset (Fin e)).sup (fun i => (v g i).natAbs)
  refine ⟨K.sup R, fun g hg => mem_latticeImage.mpr ⟨v g,?_,hv g hg⟩⟩
  intro i
  have h : (v g i).natAbs ≤ K.sup R :=
    (Finset.le_sup (f := fun i => (v g i).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := R) hg)
  have h' := Int.ofNat_le.mpr h
  omega

private theorem inv_mem_latticeImage {e : ℕ} (f : Multiplicative (Fin e → ℤ) →* G) (s : ℤ) :
    SymmetricMoves (latticeImage f s) := by
  intro g hg
  obtain ⟨v,hv,rfl⟩ := mem_latticeImage.mp hg
  refine mem_latticeImage.mpr ⟨-v,fun i => ?_,?_⟩
  · obtain ⟨ha,hb⟩ := hv i
    change -s ≤ -(v i) ∧ -(v i) ≤ s
    omega
  · exact f.map_inv (Multiplicative.ofAdd v)

private theorem triple_latticeImage {e : ℕ} (f : Multiplicative (Fin e → ℤ) →* G) (s : ℤ) :
    latticeImage f s * latticeImage f s * latticeImage f s ⊆ latticeImage f (3*s) := by
  classical
  intro g hg
  obtain ⟨d,hd,c,hc,rfl⟩ := Finset.mem_mul.mp hg
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hd
  obtain ⟨v,hv,rfl⟩ := mem_latticeImage.mp ha
  obtain ⟨w,hw,rfl⟩ := mem_latticeImage.mp hb
  obtain ⟨q,hq,rfl⟩ := mem_latticeImage.mp hc
  refine mem_latticeImage.mpr ⟨v+w+q,fun i => ?_,?_⟩
  · have h₁ := hv i
    have h₂ := hw i
    have h₃ := hq i
    change -(3*s) ≤ v i + w i + q i ∧ v i + w i + q i ≤ 3*s
    omega
  · change f (Multiplicative.ofAdd v * Multiplicative.ofAdd w * Multiplicative.ofAdd q) = _
    rw [map_mul,map_mul]

private def boxCode {e : ℕ} (s : ℕ) (v : Fin e → ℤ) : Fin e → ℤ :=
  fun i => (v i + 3*(s : ℤ)) / ((s : ℤ)+1)

private theorem boxCode_mem {e s : ℕ} {v : Fin e → ℤ}
    (h : ∀ i, -(3*(s : ℤ)) ≤ v i ∧ v i ≤ 3*(s : ℤ)) (i : Fin e) :
    boxCode s v i ∈ Finset.Icc (0 : ℤ) 5 := by
  have hdiv : 0 < (s : ℤ)+1 := by omega
  have hne : 0 ≤ v i + 3*(s : ℤ) := by have := (h i).1; omega
  have hlt : v i + 3*(s : ℤ) < 6*((s : ℤ)+1) := by have := (h i).2; omega
  refine Finset.mem_Icc.mpr ⟨Int.ediv_nonneg hne (le_of_lt hdiv),?_⟩
  have h6 := (Int.ediv_lt_iff_lt_mul hdiv).mpr hlt
  change (v i + 3*(s : ℤ)) / ((s : ℤ)+1) ≤ 5
  omega

private theorem boxCode_eq_imp {e s : ℕ} {v w : Fin e → ℤ}
    (h : boxCode s v = boxCode s w) :
    ∀ i, -(s : ℤ) ≤ v i - w i ∧ v i - w i ≤ s := by
  intro i
  have hdiv : 0 < (s : ℤ)+1 := by omega
  let a := v i + 3*(s : ℤ)
  let b := w i + 3*(s : ℤ)
  let m := (s : ℤ)+1
  have hab : a/m = b/m := congrFun h i
  have ha := Int.emod_add_mul_ediv a m
  have hb := Int.emod_add_mul_ediv b m
  have hra : a % m ≤ (s : ℤ) := by
    have hz : a % m < (s : ℤ)+1 := Int.emod_lt_of_pos a hdiv
    omega
  have hrb : b % m ≤ (s : ℤ) := by
    have hz : b % m < (s : ℤ)+1 := Int.emod_lt_of_pos b hdiv
    omega
  have hma : 0 ≤ a % m := Int.emod_nonneg a hdiv.ne.symm
  have hmb : 0 ≤ b % m := Int.emod_nonneg b hdiv.ne.symm
  rw [hab] at ha
  have hdiff : v i - w i = a % m - b % m := by
    have he : a-b = a % m - b % m := by omega
    change a-b = a % m - b % m at he
    simp only [a,b] at he
    omega
  exact ⟨by linarith,by linarith⟩

/-- A fixed number of integer generators gives uniform cubic packing. The lattice
maps may have a kernel, so finite torsion in the image poses no problem. -/
theorem uniformCubicPacking_of_integerLifts (e : ℕ) (h : HasBoundedIntegerLifts G e) :
    UniformCubicPacking G (6^e) := by
  classical
  intro K
  obtain ⟨f,hf⟩ := h K
  obtain ⟨s,hs⟩ := exists_latticeImage_bound hf
  let B := latticeImage f (s : ℤ)
  refine ⟨B,hs,mem_latticeImage.mpr ⟨0,fun i => by simp, f.map_one⟩,
    inv_mem_latticeImage f s,?_⟩
  intro T hT hSep
  have hlift (g : G) : ∃ v : Fin e → ℤ, g ∈ T →
      (∀ i, -(3*(s : ℤ)) ≤ v i ∧ v i ≤ 3*(s : ℤ)) ∧ f (Multiplicative.ofAdd v) = g := by
    by_cases hg : g ∈ T
    · obtain ⟨v,hv,he⟩ := mem_latticeImage.mp (triple_latticeImage f s (hT hg))
      exact ⟨v,fun _ => ⟨hv,he⟩⟩
    · exact ⟨0,fun hc => (hg hc).elim⟩
  choose v hv using hlift
  let D := Fintype.piFinset (fun _ : Fin e => Finset.Icc (0 : ℤ) 5)
  have hmap : Set.MapsTo (fun g => boxCode s (v g)) (↑T : Set G) (↑D : Set (Fin e → ℤ)) :=
    fun g hg => Fintype.mem_piFinset.mpr fun i => boxCode_mem (hv g hg).1 i
  have hinj : Set.InjOn (fun g => boxCode s (v g)) (↑T : Set G) := by
    intro g hg k hk he
    by_contra hn
    apply hSep g hg k hk hn
    refine mem_latticeImage.mpr ⟨v g-v k,boxCode_eq_imp he,?_⟩
    change f (Multiplicative.ofAdd (v g) * (Multiplicative.ofAdd (v k))⁻¹) = _
    rw [map_mul,map_inv,(hv g hg).2,(hv k hk).2]
  have hcard : D.card = 6^e := by
    simp [D,Fintype.card_piFinset]
  exact hcard ▸ Finset.card_le_card_of_injOn _ hmap hinj

end Packing

universe u

theorem compactClopenDADLE_of_integerLifts {G : Type u} [Group G]
    {e : ℕ} (h : HasBoundedIntegerLifts G e) : CompactClopenDADLE G (6^e) :=
  compactClopenDADLE_of_cubicPacking (uniformCubicPacking_of_integerLifts e h)

section RationalRank

open TensorProduct

/-- Each finite subset of a torsion-free abelian group of finite rational rank is
contained in the image of an integer lattice with the same rank bound. -/
theorem hasBoundedIntegerLifts_of_finite_rationalization {A : Type*}
    [AddCommGroup A] [IsAddTorsionFree A] [Module.Finite ℚ (ℚ ⊗[ℤ] A)] :
    HasBoundedIntegerLifts (Multiplicative A) (Module.finrank ℚ (ℚ ⊗[ℤ] A)) := by
  classical
  intro K
  let C : Set A := Multiplicative.toAdd '' (K : Set (Multiplicative A))
  let W := Submodule.span ℤ C
  letI : Module.Finite ℤ W := Module.Finite.of_fg (Submodule.fg_span (K.finite_toSet.image _))
  letI : Module.Free ℤ W := inferInstance
  let e := Module.finrank ℚ (ℚ ⊗[ℤ] A)
  let n := Module.finrank ℤ W
  have hinj := rationalization_injective W.subtype Subtype.val_injective
  have hle : n ≤ e := by
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    simpa only [Module.finrank_baseChange] using h
  let r := LinearMap.funLeft ℤ ℤ (Fin.castLE hle)
  have hr : Function.Surjective r := (Fin.castLE_injective hle).surjective_comp_right
  let b := (Module.finBasis ℤ W).equivFun
  let f := (W.subtype.comp (b.symm.toLinearMap.comp r)).toAddMonoidHom.toMultiplicative
  refine ⟨f,?_⟩
  intro g hg
  let x : W := ⟨Multiplicative.toAdd g,Submodule.subset_span ⟨g,hg,rfl⟩⟩
  obtain ⟨v,hv⟩ := hr (b x)
  refine ⟨Multiplicative.ofAdd v,?_⟩
  change (b.symm (r v)).val = Multiplicative.toAdd g
  rw [hv,b.symm_apply_apply]

universe v

/-- Finite-rank torsion-free abelian groups have finite dynamic dimension for compact
zero-dimensional free actions. -/
theorem compactClopenDADLE_of_finite_rationalization {G : Type v}
    [CommGroup G] [IsMulTorsionFree G] [Module.Finite ℚ (ℚ ⊗[ℤ] Additive G)] :
    CompactClopenDADLE G (6 ^ Module.finrank ℚ (ℚ ⊗[ℤ] Additive G)) :=
  compactClopenDADLE_of_integerLifts (hasBoundedIntegerLifts_of_finite_rationalization (A := Additive G))

end RationalRank

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.LatticePacking

-- BEGIN COMPLETE MODULE HirschProof.AutomorphismPacking
section
                                 

set_option autoImplicit false
noncomputable section

open Set Topology TopologicalSpace
open scoped Pointwise

namespace LocalHirschHyperfinite

section Automorphisms

attribute [local instance] Classical.decEq
variable {G : Type*} [Group G]

/-- The finite-automorphism bounded-packing property used in the normal-series
argument for clopen dynamic asymptotic dimension. -/
def HasAutomorphismPacking (G : Type*) [Group G] (Φ : Finset (G ≃* G)) (k : ℕ) : Prop :=
  ∀ K : Finset G, ∃ B : Finset G, K ⊆ B ∧ 1 ∈ B ∧ SymmetricMoves B ∧
    ∀ φ ∈ Φ, ∀ T : Finset G, T ⊆ B*B*B*(B*B*B).image φ →
      (∀ g ∈ T, ∀ h ∈ T, g ≠ h → g*h⁻¹ ∉ B) → T.card ≤ k

/-- The normal-series packing hypothesis is automatic for a group exhausted by
finite characteristic subgroups. -/
theorem hasAutomorphismPacking_of_finiteCharacteristic
    (h : ∀ K : Finset G, ∃ L : Subgroup G, L.Characteristic ∧ Finite L ∧
      ∀ g ∈ K, g ∈ L) (Φ : Finset (G ≃* G)) :
    HasAutomorphismPacking G Φ 1 := by
  classical
  intro K
  obtain ⟨L,hL,hLf,hKL⟩ := h K
  letI : Finite L := hLf
  have hfinite : (L : Set G).Finite := Set.toFinite _
  let B := hfinite.toFinset
  have hmem (g : G) : g ∈ B ↔ g ∈ L := hfinite.mem_toFinset
  refine ⟨B,fun g hg => (hmem g).mpr (hKL g hg),(hmem 1).mpr (Subgroup.one_mem L),
    fun g hg => (hmem _).mpr (L.inv_mem ((hmem g).mp hg)),?_⟩
  intro φ _ T hT hsep
  have hthree {g : G} (hg : g ∈ B*B*B) : g ∈ L := by
    obtain ⟨ab,hab,c,hc,rfl⟩ := Finset.mem_mul.mp hg
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hab
    exact L.mul_mem (L.mul_mem ((hmem a).mp ha) ((hmem b).mp hb)) ((hmem c).mp hc)
  have hφ : ∀ g ∈ L, φ g ∈ L := by
    intro g hg
    rw [← (Subgroup.characteristic_iff_map_eq.mp hL) φ]
    exact ⟨g,hg,rfl⟩
  have hsets : ∀ g ∈ T, g ∈ L := by
    intro g hg
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp (hT hg)
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    exact L.mul_mem (hthree ha) (hφ c (hthree hc))
  refine Finset.card_le_one.mpr fun g hg k hk => ?_
  by_contra hne
  exact hsep g hg k hk hne ((hmem _).mpr (L.mul_mem (hsets g hg) (L.inv_mem (hsets k hk))))

theorem hasAutomorphismPacking_of_finite [Finite G] (Φ : Finset (G ≃* G)) :
    HasAutomorphismPacking G Φ 1 :=
  hasAutomorphismPacking_of_finiteCharacteristic (fun _ => ⟨⊤,inferInstance,inferInstance,
    fun g _ => Subgroup.mem_top g⟩) Φ


theorem HasAutomorphismPacking.mono {Φ : Finset (G ≃* G)} {a b : ℕ}
    (h : HasAutomorphismPacking G Φ a) (hab : a ≤ b) : HasAutomorphismPacking G Φ b := by
  intro K
  obtain ⟨B,hKB,h1,hB,hp⟩ := h K
  exact ⟨B,hKB,h1,hB,fun φ hφ T hT hsep => (hp φ hφ T hT hsep).trans hab⟩

/-- Conjugate an automorphism through a multiplicative equivalence. -/
def transportAutomorphism {J : Type*} [Group J] (e : G ≃* J) (φ : J ≃* J) : G ≃* G :=
  e.trans (φ.trans e.symm)

theorem transportAutomorphism_refl {J : Type*} [Group J] (e : G ≃* J) :
    transportAutomorphism e (MulEquiv.refl J) = MulEquiv.refl G := by
  ext x
  simp [transportAutomorphism]

/-- Packing is preserved by transport through a multiplicative equivalence. -/
theorem hasAutomorphismPacking_of_equiv {J : Type*} [Group J] (e : G ≃* J)
    (Φ : Finset (J ≃* J)) {k : ℕ}
    (hp : HasAutomorphismPacking G (Φ.image (transportAutomorphism e)) k) :
    HasAutomorphismPacking J Φ k := by
  classical
  intro K
  obtain ⟨A,hKA,h1,hA,hPack⟩ := hp (K.image e.symm)
  let B := A.image e
  refine ⟨B,?_,?_,?_,?_⟩
  · intro x hx
    exact Finset.mem_image.mpr ⟨e.symm x,hKA (Finset.mem_image.mpr ⟨x,hx,rfl⟩),e.apply_symm_apply x⟩
  · exact Finset.mem_image.mpr ⟨1,h1,map_one e⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨a⁻¹,hA ha,map_inv e a⟩
  · intro φ hφ T hT hsep
    let ψ := transportAutomorphism e φ
    have hψ : ψ ∈ Φ.image (transportAutomorphism e) := Finset.mem_image.mpr ⟨φ,hφ,rfl⟩
    have backB : B.image e.symm = A := by
      rw [Finset.image_image]
      simp [Function.comp_def]
    have back3 : (B*B*B).image e.symm = A*A*A := by
      simp only [Finset.image_mul e.symm,backB]
    have backφ : ((B*B*B).image φ).image e.symm = ((B*B*B).image e.symm).image ψ := by
      rw [Finset.image_image,Finset.image_image]
      apply Finset.image_congr
      intro x _
      simp [ψ,transportAutomorphism,Function.comp_def]
    have hshape : (B*B*B*(B*B*B).image φ).image e.symm =
        A*A*A*(A*A*A).image ψ := by
      rw [Finset.image_mul e.symm,backφ,back3]
    let S := T.image e.symm
    have hS : S ⊆ A*A*A*(A*A*A).image ψ := hshape ▸ Finset.image_subset_image hT
    have hSsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a*b⁻¹ ∉ A := by
      intro a ha b hb hn hm
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
      have hne : x ≠ y := fun he => hn (congrArg e.symm he)
      apply hsep x hx y hy hne
      exact Finset.mem_image.mpr ⟨e.symm x*(e.symm y)⁻¹,hm,by simp⟩
    have hcard := hPack ψ hψ S hS hSsep
    rwa [show S.card = T.card from Finset.card_image_of_injective _ e.symm.injective] at hcard

end Automorphisms

section QuotientPacking

attribute [local instance] Classical.decEq
variable {H P : Type*} [Group H] [Group P]

/-- Ambient form of the relative packing estimate. The finite separations in
the kernel may grow with the chosen neighborhood in the subgroup. -/
def HasRelativePacking (F G : Subgroup H) (C : Finset H) (k : ℕ) : Prop :=
  ∀ K : Finset H, (∀ x ∈ K, x ∈ G) →
    ∃ A B : Finset H, K ⊆ B ∧ 1 ∈ A ∧ 1 ∈ B ∧
      (∀ x ∈ A, x ∈ F) ∧ (∀ x ∈ B, x ∈ G) ∧ SymmetricMoves A ∧ SymmetricMoves B ∧
      ∀ T : Finset H, T ⊆ (B*B*B)*C*(B*B*B) →
        (∀ x ∈ T, ∀ y ∈ T, x ≠ y → x*y⁻¹ ∉ A*B*A) → T.card ≤ k

private theorem exists_finite_symmetric_lifts (q : H →* P) (G : Subgroup H)
    {K : Finset H} (hK : ∀ x ∈ K, x ∈ G) {U : Finset (G.map q)}
    (hKU : ∀ x (hx : x ∈ K), (⟨q x,⟨x,hK x hx,rfl⟩⟩ : G.map q) ∈ U)
    (h1 : 1 ∈ U) (hU : SymmetricMoves U) :
    ∃ B : Finset H, K ⊆ B ∧ 1 ∈ B ∧ (∀ x ∈ B, x ∈ G) ∧ SymmetricMoves B ∧
      B.image q = U.image Subtype.val := by
  classical
  have hl (y : G.map q) : ∃ x ∈ G, q x = y.val := y.property
  choose v hvG hvq using hl
  let M := K ∪ (U.image v) ∪ {1}
  let B := M ∪ M⁻¹
  have hMG (x : H) (hx : x ∈ M) : x ∈ G := by
    simp only [M,Finset.mem_union,Finset.mem_image,Finset.mem_singleton] at hx
    rcases hx with (hx|⟨y,hy,rfl⟩)|rfl
    · exact hK x hx
    · exact hvG y
    · exact G.one_mem
  have hMQ (x : H) (hx : x ∈ M) : ∃ y ∈ U, q x = y.val := by
    simp only [M,Finset.mem_union,Finset.mem_image,Finset.mem_singleton] at hx
    rcases hx with (hx|⟨y,hy,rfl⟩)|rfl
    · exact ⟨⟨q x,⟨x,hK x hx,rfl⟩⟩,hKU x hx,rfl⟩
    · exact ⟨y,hy,hvq y⟩
    · exact ⟨1,h1,map_one q⟩
  refine ⟨B,fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_union_left _ hx)),
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)),?_,?_,?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hMG x hx
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_inv.mp hx
      exact G.inv_mem (hMG y hy)
  · intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact Finset.mem_union_right _ (Finset.mem_inv.mpr ⟨x,hx,rfl⟩)
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_inv.mp hx
      exact Finset.mem_union_left _ (by simpa using hy)
  · ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x,hx,rfl⟩
      rcases Finset.mem_union.mp hx with hx|hx
      · obtain ⟨a,ha,he⟩ := hMQ x hx
        exact ⟨a,ha,he.symm⟩
      · obtain ⟨z,hz,rfl⟩ := Finset.mem_inv.mp hx
        obtain ⟨a,ha,he⟩ := hMQ z hz
        exact ⟨a⁻¹,hU ha,by change (a.val)⁻¹ = q z⁻¹; rw [map_inv,he]⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨v a,Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))),hvq a⟩

private theorem exists_kernel_separation_buffer (q : H →* P) {B D : Finset H} :
    ∃ A : Finset H, 1 ∈ A ∧ (∀ x ∈ A, x ∈ q.ker) ∧ SymmetricMoves A ∧
      ∀ x ∈ D, ∀ y ∈ D, q (x*y⁻¹) ∈ B.image q → x*y⁻¹ ∈ A*B*A := by
  classical
  let R := (B⁻¹*D*D⁻¹).filter (fun x => x ∈ q.ker)
  let A := (R ∪ R⁻¹) ∪ {1}
  have h1A : 1 ∈ A := Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
  refine ⟨A,h1A,?_,?_,?_⟩
  · intro x hx
    simp only [A,Finset.mem_union,Finset.mem_singleton,Finset.mem_inv,Finset.mem_filter,R] at hx
    rcases hx with ((hx|⟨y,hy,rfl⟩)|rfl)
    · exact hx.2
    · exact q.ker.inv_mem hy.2
    · exact q.ker.one_mem
  · intro x hx
    simp only [A,Finset.mem_union,Finset.mem_singleton] at hx ⊢
    rcases hx with ((hx|hx)|rfl)
    · exact Or.inl (Or.inr (Finset.mem_inv.mpr ⟨x,hx,rfl⟩))
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_inv.mp hx
      exact Or.inl (Or.inl (by simpa using hy))
    · exact Or.inr (inv_one : (1 : H)⁻¹ = 1)
  · intro x hx y hy h
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp h
    have hm : b⁻¹*x*y⁻¹ ∈ B⁻¹*D*D⁻¹ :=
      Finset.mem_mul.mpr ⟨b⁻¹*x,Finset.mem_mul.mpr
        ⟨b⁻¹,Finset.mem_inv.mpr ⟨b,hb,rfl⟩,x,hx,rfl⟩,
        y⁻¹,Finset.mem_inv.mpr ⟨y,hy,rfl⟩,rfl⟩
    have hk : b⁻¹*x*y⁻¹ ∈ q.ker := by
      change q (b⁻¹*x*y⁻¹) = 1
      rw [mul_assoc,map_mul,map_inv,he,inv_mul_cancel]
    have ha : b⁻¹*x*y⁻¹ ∈ A :=
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hm,hk⟩))
    exact Finset.mem_mul.mpr ⟨1*b,Finset.mem_mul.mpr ⟨1,h1A,b,hb,rfl⟩,
      b⁻¹*x*y⁻¹,ha,by simp only [one_mul,mul_assoc,mul_inv_cancel_left]⟩


/-- Conjugation restricts to the image of a normal subgroup under any homomorphism. -/
def imageConjugation (q : H →* P) (G : Subgroup H) (hG : G.Normal) (c : H) :
    G.map q ≃* G.map q := by
  have h (x : G.map q) (d : H) : q d * x.val * (q d)⁻¹ ∈ G.map q := by
    obtain ⟨u,hu,he⟩ := x.property
    exact ⟨d*u*d⁻¹,hG.conj_mem u hu d,by rw [map_mul,map_mul,map_inv,he]⟩
  exact {
    toFun := fun x => ⟨q c*x.val*(q c)⁻¹,h x c⟩
    invFun := fun x => ⟨q c⁻¹*x.val*(q c⁻¹)⁻¹,h x c⁻¹⟩
    left_inv := fun x => Subtype.ext (by simp [map_inv,mul_assoc])
    right_inv := fun x => Subtype.ext (by simp [map_inv,mul_assoc])
    map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }

/-- CJMST's relative packing estimate lifts a finite-family estimate in the
quotient through a finite separation buffer in the kernel. -/
theorem hasRelativePacking_of_automorphisms (q : H →* P) (G : Subgroup H)
    (hG : G.Normal) (C : Finset H) {k : ℕ}
    (hp : HasAutomorphismPacking (G.map q) (C.image (imageConjugation q G hG)) k) :
    HasRelativePacking q.ker G C (C.card*k) := by
  classical
  intro K hK
  let J := G.map q
  letI : DecidableEq (G.map q) := Classical.decEq _
  let a (x : G) : J := ⟨q x.val,⟨x.val,x.property,rfl⟩⟩
  let K' := (K.subtype fun x => x ∈ G).image a
  obtain ⟨U,hKU,hU1,hU,hpack⟩ := hp K'
  have hKU' (x : H) (hx : x ∈ K) : a ⟨x,hK x hx⟩ ∈ U :=
    hKU (Finset.mem_image.mpr ⟨⟨x,hK x hx⟩,Finset.mem_subtype.mpr hx,rfl⟩)
  obtain ⟨B,hKB,hB1,hBG,hB,hBU⟩ := exists_finite_symmetric_lifts q G hK hKU' hU1 hU
  let B3 := B*B*B
  let D := B3*C*B3
  obtain ⟨A,hA1,hA,hAs,hAsep⟩ := exists_kernel_separation_buffer q (B := B) (D := D)
  refine ⟨A,B,hKB,hA1,hB1,hA,hBG,hAs,hB,?_⟩
  intro T hT hs
  let S (c : H) := T.filter fun x => x ∈ B3*{c}*B3
  have hcover : T ⊆ C.biUnion S := by
    intro x hx
    obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_mul.mp (hT hx)
    obtain ⟨b,hb,c,hc,rfl⟩ := Finset.mem_mul.mp hu
    exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨hx,
      Finset.mem_mul.mpr ⟨b*c,Finset.mem_mul.mpr ⟨b,hb,c,Finset.mem_singleton.mpr rfl,rfl⟩,
        v,hv,rfl⟩⟩⟩
  have liftB {b : H} (hb : b ∈ B) : ∃ u ∈ U, u.val = q b := by
    have hr : q b ∈ B.image q := Finset.mem_image.mpr ⟨b,hb,rfl⟩
    rw [hBU] at hr
    exact Finset.mem_image.mp hr
  have lift3 {b : H} (hb : b ∈ B3) : ∃ u ∈ U*U*U, u.val = q b := by
    obtain ⟨d,hd,b,hbb,rfl⟩ := Finset.mem_mul.mp hb
    obtain ⟨g,hg,h,hh,rfl⟩ := Finset.mem_mul.mp hd
    obtain ⟨u,hu,he⟩ := liftB hg
    obtain ⟨v,hv,hj⟩ := liftB hh
    obtain ⟨w,hw,hl⟩ := liftB hbb
    exact ⟨u*v*w,Finset.mem_mul.mpr ⟨u*v,Finset.mem_mul.mpr ⟨u,hu,v,hv,rfl⟩,w,hw,rfl⟩,
      by change u.val*v.val*w.val = q (g*h*b); simp only [map_mul,he,hj,hl]⟩
  have hsmall (c : H) (hc : c ∈ C) : (S c).card ≤ k := by
    let φ := imageConjugation q G hG c
    have hx (x : (S c : Set H)) :
        ∃ v ∈ (U*U*U)*((U*U*U).image φ), v.val = q x.val * (q c)⁻¹ := by
      obtain ⟨y,hy,z,hz,hyz⟩ := Finset.mem_mul.mp (Finset.mem_filter.mp x.property).2
      obtain ⟨b,hb,c',hc',rfl⟩ := Finset.mem_mul.mp hy
      have hc'e : c' = c := Finset.mem_singleton.mp hc'
      subst c'
      obtain ⟨v,hv,he⟩ := lift3 hb
      obtain ⟨w,hw,hr⟩ := lift3 hz
      refine ⟨v * φ w,Finset.mem_mul.mpr ⟨v,hv,φ w,
        Finset.mem_image.mpr ⟨w,hw,rfl⟩,rfl⟩,?_⟩
      change v.val * (q c * w.val * (q c)⁻¹) = _
      simp only [← hyz,map_mul,he,hr,mul_assoc]
    choose v hv hq using hx
    let R := (S c).attach.image v
    have hR : R ⊆ (U*U*U)*((U*U*U).image φ) := by
      intro z hz
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
      exact hv x
    have val_diff (x y : (S c : Set H)) :
        (v x * (v y)⁻¹).val = q (x.val*y.val⁻¹) := by
      change (v x).val * (v y).val⁻¹ = _
      rw [hq x,hq y,map_mul,map_inv]
      group
    have hprohibit {x y : (S c : Set H)} (hne : x.val ≠ y.val) :
        q (x.val*y.val⁻¹) ∉ B.image q := by
      have hxt := (Finset.mem_filter.mp x.property).1
      have hyt := (Finset.mem_filter.mp y.property).1
      exact fun hp => hs x.val hxt y.val hyt hne (hAsep _ (hT hxt) _ (hT hyt) hp)
    have hinj : Function.Injective v := by
      intro x y he
      apply Subtype.ext
      by_contra hn
      apply hprohibit hn
      have hf : q (x.val*y.val⁻¹) = 1 := by rw [← val_diff,he,mul_inv_cancel]; rfl
      exact Finset.mem_image.mpr ⟨1,hB1,(map_one q).trans hf.symm⟩
    have hsep : ∀ u ∈ R, ∀ w ∈ R, u ≠ w → u*w⁻¹ ∉ U := by
      intro u hu w hw hne hm
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hw
      have hn : x.val ≠ y.val := fun he => hne (congrArg v (Subtype.ext he))
      apply hprohibit hn
      rw [← val_diff,hBU]
      exact Finset.mem_image.mpr ⟨_,hm,rfl⟩
    have hc' : φ ∈ C.image (imageConjugation q G hG) := Finset.mem_image.mpr ⟨c,hc,rfl⟩
    have hCard : R.card = (S c).card := (Finset.card_image_of_injective _ hinj).trans Finset.card_attach
    exact hCard ▸ hpack φ hc' R hR hsep
  calc
    T.card ≤ (C.biUnion S).card := Finset.card_le_card hcover
    _ ≤ ∑ c ∈ C, (S c).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ C, k := Finset.sum_le_sum hsmall
    _ = C.card*k := by simp [Nat.mul_comm]

end QuotientPacking

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.AutomorphismPacking

-- BEGIN COMPLETE MODULE HirschProof.ClopenRapidCovers
section
                                   
                                      

set_option autoImplicit false
noncomputable section

open Set Topology TopologicalSpace
open scoped Pointwise

namespace LocalHirschHyperfinite

section RapidCovers

variable {H P X : Type*} [Group H] [Group P] [MulAction H X] [TopologicalSpace X]
variable [DecidableEq H] [DecidableEq P]

/-- Clopen decompositions on an acting subgroup, with bounds in the subgroup. -/
def HasClopenSubgroupDimension (F : Subgroup H) (d : ℕ) (X : Type*) [MulAction H X]
    [TopologicalSpace X] : Prop :=
  ∀ K : Finset H, (∀ g ∈ K, g ∈ F) → SymmetricMoves K →
    ∃ V : Fin (d+1) → Set X, (∀ i, IsClopen (V i)) ∧ (∀ x, ∃ i, x ∈ V i) ∧
      ∃ D : Finset H, (∀ g ∈ D, g ∈ F) ∧
        ∀ i x y, TestComponent K (V i) x y → ∃ g ∈ D, g • x = y

/-- The relative palette bound is uniform over finite tests with a given
finite set of quotient displacements. -/
def HasClopenQuotientPalettes (q : H →* P) (X : Type*) [MulAction H X]
    [TopologicalSpace X] : Prop :=
  ∀ C : Finset H, ∃ n : ℕ, ∀ E : Finset H, (∀ g ∈ E, ∃ c ∈ C, q c = q g) →
    ∃ W : Fin n → Set X, (∀ j, IsClopen (W j)) ∧ (∀ x, ∃ j, x ∈ W j) ∧
      ∀ j x, x ∈ W j → ∀ g ∈ E, q g ≠ 1 → g • x ∉ W j

private def symmetricNeighborhood (K : Finset H) : Finset H := insert 1 (K ∪ K⁻¹)

private theorem subset_symmetricNeighborhood (K : Finset H) : K ⊆ symmetricNeighborhood K :=
  fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)

private theorem one_mem_symmetricNeighborhood (K : Finset H) : 1 ∈ symmetricNeighborhood K :=
  Finset.mem_insert_self _ _

private theorem symmetricNeighborhood_symmetric (K : Finset H) :
    SymmetricMoves (symmetricNeighborhood K) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl|hx
  · simpa only [inv_one] using one_mem_symmetricNeighborhood K
  · rcases Finset.mem_union.mp hx with hx|hx
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_inv.mpr ⟨x,hx,rfl⟩))
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_inv.mp hx
      simpa only [inv_inv] using subset_symmetricNeighborhood K hy

private theorem symmetricNeighborhood_subset_subgroup (K : Finset H) (F : Subgroup H)
    (hK : ∀ g ∈ K, g ∈ F) : ∀ g ∈ symmetricNeighborhood K, g ∈ F := by
  intro g hg
  rcases Finset.mem_insert.mp hg with rfl|hg
  · exact F.one_mem
  · rcases Finset.mem_union.mp hg with hg|hg
    · exact hK g hg
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_inv.mp hg
      exact F.inv_mem (hK a ha)

omit [TopologicalSpace X] in
private theorem testComponent_of_thickened_subset
    {K L B : Finset H} {U V : Set X} (hU : U ⊆ moveThickening B V)
    (h1 : 1 ∈ K) (hBL : B⁻¹*K*B ⊆ L) {x y : X} (hxy : TestComponent K U x y)
    {a b : H} (ha : a ∈ B) (hb : b ∈ B) {u v : X} (hu : u ∈ V) (hv : v ∈ V)
    (hux : a • u = x) (hvy : b • v = y) : TestComponent L V u v := by
  refine ⟨hu,?_⟩
  have reach {z : X} (p : Relation.ReflTransGen (TestEdge K U) x z) :
      ∀ b ∈ B, ∀ v ∈ V, b • v = z → Relation.ReflTransGen (TestEdge L V) u v := by
    induction p with
    | refl =>
      intro b hb v hv he
      have hmem : b⁻¹*1*a ∈ B⁻¹*K*B := Finset.mem_mul.mpr
        ⟨b⁻¹*1,Finset.mem_mul.mpr ⟨b⁻¹,Finset.mem_inv.mpr ⟨b,hb,rfl⟩,1,h1,rfl⟩,a,ha,rfl⟩
      exact .single ⟨hu,hv,b⁻¹*1*a,hBL hmem,by
        rw [mul_one,mul_smul,hux,← he,inv_smul_smul]⟩
    | tail _ e ih =>
      intro b hb v hv he
      obtain ⟨c,hc,w,hw,hwz⟩ := hU e.1
      obtain ⟨g,hg,hgv⟩ := e.2.2
      refine (ih c hc w hw hwz).tail ⟨hw,hv,b⁻¹*g*c,hBL (Finset.mem_mul.mpr
        ⟨b⁻¹*g,Finset.mem_mul.mpr ⟨b⁻¹,Finset.mem_inv.mpr ⟨b,hb,rfl⟩,g,hg,rfl⟩,c,hc,rfl⟩),?_⟩
      rw [mul_smul,mul_smul,hwz,hgv,← he,inv_smul_smul]
  exact reach hxy.2 b hb v hv hvy


private def triplePad (B C : Finset H) : Finset H := B⁻¹*C*B

private theorem mem_triplePad {B C : Finset H} {a b c : H} (ha : a ∈ B) (hb : b ∈ C) (hc : c ∈ B) :
    a⁻¹*b*c ∈ triplePad B C :=
  Finset.mem_mul.mpr ⟨a⁻¹*b,Finset.mem_mul.mpr ⟨a⁻¹,Finset.mem_inv.mpr ⟨a,ha,rfl⟩,b,hb,rfl⟩,c,hc,rfl⟩

private def cosetPad (q : H →* P) (B C : Finset H) (c : H) : Finset H :=
  triplePad B (C.filter fun a => q a = q c)

private theorem mem_cosetPad {q : H →* P} {B C : Finset H} {a b c d : H}
    (ha : a ∈ B) (hb : b ∈ C) (hc : c ∈ B) (hbd : q b = q d) :
    a⁻¹*b*c ∈ cosetPad q B C d :=
  mem_triplePad ha (Finset.mem_filter.mpr ⟨hb,hbd⟩) hc

private theorem cosetPad_subset (q : H →* P) (B C : Finset H) (c : H) :
    cosetPad q B C c ⊆ triplePad B C :=
  Finset.mul_subset_mul (Finset.mul_subset_mul Subset.rfl (Finset.filter_subset _ _)) Subset.rfl

private theorem cosetPad_projection (q : H →* P) {B C : Finset H} {c g : H}
    (hB : ∀ g ∈ B, q g = 1) (hg : g ∈ cosetPad q B C c) : q g = q c := by
  obtain ⟨w,hw,b,hb,rfl⟩ := Finset.mem_mul.mp hg
  obtain ⟨a,ha,c',hc',rfl⟩ := Finset.mem_mul.mp hw
  obtain ⟨a',ha',rfl⟩ := Finset.mem_inv.mp ha
  simp only [map_mul,map_inv,hB _ ha',hB _ hb,(Finset.mem_filter.mp hc').2,inv_one,one_mul,mul_one]

private def rapidTest (q : H →* P) (C A B : Finset H) : Finset H :=
  symmetricNeighborhood (((triplePad B A ∪ triplePad B B) ∪ (triplePad B C)⁻¹ * (triplePad B C)).filter
    (fun a => q a = 1))

private theorem rapidTest_kernel (q : H →* P) (C A B : Finset H) :
    ∀ g ∈ rapidTest q C A B, q g = 1 := by
  apply symmetricNeighborhood_subset_subgroup _ q.ker
  intro g hg
  exact (Finset.mem_filter.mp hg).2

private theorem rapidTest_symm (q : H →* P) (C A B : Finset H) :
    SymmetricMoves (rapidTest q C A B) := symmetricNeighborhood_symmetric _

private theorem rapidTest_of_A (q : H →* P) {C A B : Finset H} {g : H}
    (hB : ∀ g ∈ B, q g = 1) (hA : ∀ g ∈ A, q g = 1)
    (hg : g ∈ triplePad B A) : g ∈ rapidTest q C A B := by
  apply subset_symmetricNeighborhood
  refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hg),?_⟩
  obtain ⟨w,hw,b,hb,rfl⟩ := Finset.mem_mul.mp hg
  obtain ⟨a,ha,c,hc,rfl⟩ := Finset.mem_mul.mp hw
  obtain ⟨a',ha',rfl⟩ := Finset.mem_inv.mp ha
  simp [hB _ ha',hB _ hb,hA _ hc]

private theorem rapidTest_of_B (q : H →* P) {C A B : Finset H} {g : H}
    (hB : ∀ g ∈ B, q g = 1) (hg : g ∈ triplePad B B) :
    g ∈ rapidTest q C A B := by
  apply subset_symmetricNeighborhood
  refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hg),?_⟩
  obtain ⟨w,hw,b,hb,rfl⟩ := Finset.mem_mul.mp hg
  obtain ⟨a,ha,c,hc,rfl⟩ := Finset.mem_mul.mp hw
  obtain ⟨a',ha',rfl⟩ := Finset.mem_inv.mp ha
  simp [hB _ ha',hB _ hb,hB _ hc]

private def nextPad (q : H →* P) (C B D : Finset H) : Finset H :=
  symmetricNeighborhood (B ∪ ((B*(triplePad B C)*D*(triplePad B C)⁻¹).filter fun g => q g = 1))

private theorem nextPad_kernel (q : H →* P) (C B D : Finset H) (hB : ∀ g ∈ B, q g = 1) :
    ∀ g ∈ nextPad q C B D, q g = 1 := by
  apply symmetricNeighborhood_subset_subgroup _ q.ker
  intro g hg
  rcases Finset.mem_union.mp hg with hg|hg
  · exact hB _ hg
  · exact (Finset.mem_filter.mp hg).2

private theorem subset_nextPad (q : H →* P) (C B D : Finset H) : B ⊆ nextPad q C B D :=
  fun _ h => subset_symmetricNeighborhood _ (Finset.mem_union_left _ h)

private theorem mul_cosetPad_inv_mem_nextPad (q : H →* P) {C B D : Finset H}
    (hB : ∀ g ∈ B, q g = 1) (hD : ∀ g ∈ D, q g = 1)
    {a b d r c : H} (ha : a ∈ B) (hb : b ∈ cosetPad q B C c)
    (hd : d ∈ D) (hr : r ∈ cosetPad q B C c) :
    a*b*d*r⁻¹ ∈ nextPad q C B D := by
  apply subset_symmetricNeighborhood
  refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_,?_⟩)
  · exact Finset.mem_mul.mpr ⟨a*b*d,Finset.mem_mul.mpr ⟨a*b,Finset.mem_mul.mpr
      ⟨a,ha,b,cosetPad_subset q B C c hb,rfl⟩,d,hd,rfl⟩,
      r⁻¹,Finset.mem_inv.mpr ⟨r,cosetPad_subset q B C c hr,rfl⟩,rfl⟩
  · simp [hB a ha, hD d hd, cosetPad_projection q hB hb, cosetPad_projection q hB hr]

omit [TopologicalSpace X] in
private theorem saturate_cosetPad_thickening (q : H →* P) {C A B D : Finset H}
    {S : Set X} (hB : ∀ g ∈ B, q g = 1) (hD : ∀ g ∈ D, q g = 1)
    (hcomp : ∀ x y, TestComponent (rapidTest q C A B) S x y → ∃ g ∈ D, g • x = y)
    (U : Set X) :
    moveThickening B (saturateTranslatedComponents (rapidTest q C A B) S
      (fun c : (C : Set H) => cosetPad q B C c.val) U) ⊆ moveThickening (nextPad q C B D) U := by
  rintro x ⟨a,ha,y,hy,rfl⟩
  rcases hy with hy|hy
  · exact ⟨a,subset_nextPad q C B D ha,y,hy,rfl⟩
  · obtain ⟨c,b,hb,r,hr,w,hw,hp⟩ := Set.mem_iUnion.mp hy
    obtain ⟨g,hg,he⟩ := hcomp _ _ (testComponent_symm (rapidTest_symm q C A B) hp)
    refine ⟨a*b*g*r⁻¹,mul_cosetPad_inv_mem_nextPad q hB hD ha hb hg hr,w,hw,?_⟩
    rw [mul_smul,mul_smul,mul_smul,he,smul_inv_smul]

omit [TopologicalSpace X] in
private theorem cosetPad_alignment (q : H →* P) {C A B : Finset H} {S : Set X}
    (hB : ∀ g ∈ B, q g = 1)
    (hS : ∀ x ∈ S, ∀ g ∈ (triplePad B C)⁻¹*(triplePad B C), q g ≠ 1 → g • x ∉ S)
    {c c' y a b} (ha : a ∈ cosetPad q B C c) (hb : b ∈ cosetPad q B C c')
    (hy : a⁻¹ • y ∈ S) (hy' : b⁻¹ • y ∈ S) :
    cosetPad q B C c = cosetPad q B C c' ∧
      TestComponent (rapidTest q C A B) S (a⁻¹ • y) (b⁻¹ • y) := by
  have hmove : (b⁻¹*a) • (a⁻¹ • y) = b⁻¹ • y := by rw [mul_smul,smul_inv_smul]
  have hmem : b⁻¹*a ∈ (triplePad B C)⁻¹*(triplePad B C) := Finset.mem_mul.mpr
    ⟨b⁻¹,Finset.mem_inv.mpr ⟨b,cosetPad_subset q B C c' hb,rfl⟩,
      a,cosetPad_subset q B C c ha,rfl⟩
  have hzero : q (b⁻¹*a) = 1 := by
    by_contra h
    exact hS _ hy _ hmem h (hmove.symm ▸ hy')
  have he : q c = q c' := by
    have hh := hzero
    rw [map_mul,map_inv,cosetPad_projection q hB hb,cosetPad_projection q hB ha] at hh
    simpa using congrArg (fun x : P => q c' * x) hh
  refine ⟨by simp [cosetPad,he],hy,Relation.ReflTransGen.single ⟨hy,hy',b⁻¹*a,?_,hmove⟩⟩
  exact subset_symmetricNeighborhood _ (Finset.mem_filter.mpr
    ⟨Finset.mem_union_right _ hmem,hzero⟩)


/-- The image of a component under a finite family of moves in one quotient coset. -/
def crossComponentImage (c : H) (A K : Finset H) (U : Set X) (x : X) : Set X :=
  (fun z : X => c • z) '' moveThickening A {z | TestComponent K U x z}

omit [TopologicalSpace X] [DecidableEq P] in
private theorem rapidCover_independent (q : H →* P) {C A B : Finset H}
    (h1B : 1 ∈ B) (h1C : 1 ∈ C) (h1A : 1 ∈ A)
    (hB : ∀ g ∈ B, q g = 1) (hA : ∀ g ∈ A, q g = 1) {S U : Set X}
    (hS : ∀ x ∈ S, ∀ g ∈ (triplePad B C)⁻¹*(triplePad B C), q g ≠ 1 → g • x ∉ S)
    (hU : moveThickening A U ⊆ moveThickening B S) :
    ∀ x ∈ U, ∀ g ∈ C*A, q g ≠ 1 → g • x ∉ U := by
  intro x hx g hg hn h
  obtain ⟨c,hc,a,ha,rfl⟩ := Finset.mem_mul.mp hg
  obtain ⟨b,hb,v,hv,he⟩ := hU ⟨a,ha,x,hx,rfl⟩
  obtain ⟨r,hr,w,hw,hw'⟩ := hU ((subset_moveThickening h1A U) h)
  have hmove : (r⁻¹*c*b) • v = w := by
    rw [mul_smul,mul_smul,he,← mul_smul c a x]
    rw [←hw',inv_smul_smul]
  have hmem : r⁻¹*c*b ∈ (triplePad B C)⁻¹*(triplePad B C) := by
    have h1 : 1 ∈ triplePad B C := by
      simpa only [inv_one,mul_one] using mem_triplePad h1B h1C h1B
    exact Finset.mem_mul.mpr ⟨1,by simpa only [inv_one] using
      (Finset.mem_inv.mpr ⟨1,h1,rfl⟩ : (1 : H)⁻¹ ∈ (triplePad B C)⁻¹),
      _,mem_triplePad hr hc hb,one_mul _⟩
  have hne : q (r⁻¹*c*b) ≠ 1 := by
    simpa [hB _ hr,hB _ hb, hA _ ha] using hn
  exact hS v hv _ hmem hne (hmove.symm ▸ hw)

omit [TopologicalSpace X] in
private theorem rapidCross_comparison (q : H →* P) {C A B D B' : Finset H}
    (h1A : 1 ∈ A) (h1B : 1 ∈ B) (hA : ∀ g ∈ A, q g = 1)
    (hB : ∀ g ∈ B, q g = 1) (hD : ∀ g ∈ D, q g = 1) {S U V Z : Set X}
    (hU : moveThickening A U ⊆ moveThickening B S)
    (hZV : Z ⊆ V) (hV : V ⊆ moveThickening B Z)
    (hDcomp : ∀ x y, TestComponent (rapidTest q C A B) S x y → ∃ g ∈ D, g • x = y)
    (hfixed : saturateTranslatedComponents (rapidTest q C A B) S
      (fun c : (C : Set H) => cosetPad q B C c.val) Z = Z)
    (hLarge : nextPad q C B D ⊆ B')
    {c : H} (hc : c ∈ C) {x : X} (hx : x ∈ U) :
    ∀ y ∈ crossComponentImage c A B U x, y ∈ V → ∀ z ∈ crossComponentImage c A B U x,
      TestComponent B' V y z := by
  have hU' : U ⊆ moveThickening B S := (subset_moveThickening h1A U).trans hU
  obtain ⟨b₀,hb₀,v₀,hv₀,hv₀x⟩ := hU' hx
  let J := {v | TestComponent (rapidTest q C A B) S v₀ v}
  have anchor (w : X) (hw : TestComponent B U x w) (a : H) (ha : a ∈ A) :
      ∃ b ∈ B, ∃ v ∈ J, b • v = a • w := by
    obtain ⟨b,hb,v,hv,he⟩ := hU ⟨a,ha,w,testComponent_end hw,rfl⟩
    obtain ⟨r,hr,u,hu,heu⟩ := hU' (testComponent_end hw)
    have hcomp := testComponent_of_thickened_subset hU' h1B
      (fun _ ht => rapidTest_of_B q (C := C) (A := A) hB ht) hw hb₀ hr hv₀ hu hv₀x heu
    have hmove : (b⁻¹*a*r) • u = v := by
      rw [mul_smul,mul_smul,heu,←he,inv_smul_smul]
    have hlarge := rapidTest_of_A q (C := C) hB hA (mem_triplePad hb ha hr)
    exact ⟨b,hb,v,testComponent_trans hcomp ⟨hu,.single ⟨hu,hv,b⁻¹*a*r,hlarge,hmove⟩⟩,he⟩
  have liftCross {y : X} (hy : y ∈ crossComponentImage c A B U x) :
      ∃ b ∈ B, ∃ v ∈ J, (c*b) • v = y := by
    obtain ⟨_,⟨a,ha,w,hw,rfl⟩,rfl⟩ := hy
    obtain ⟨b,hb,v,hv,he⟩ := anchor w hw a ha
    exact ⟨b,hb,v,hv,by rw [mul_smul,he]⟩
  let E := cosetPad q B C c
  let O := moveThickening E J
  have hCross : crossComponentImage c A B U x ⊆ O := by
    intro y hy
    obtain ⟨b,hb,v,hv,he⟩ := liftCross hy
    have he' := mem_cosetPad (q := q) h1B hc hb (rfl : q c = q c)
    exact ⟨c*b,by simpa only [inv_one,one_mul] using he',v,hv,he⟩
  intro y hy hyV z hz
  obtain ⟨b,hb,v,hv,hbv⟩ := liftCross hy
  obtain ⟨a,ha,u,hu,hau⟩ := hV hyV
  have huO : u ∈ O := by
    refine ⟨a⁻¹*c*b,mem_cosetPad ha hc hb rfl,v,hv,?_⟩
    rw [mul_assoc,mul_smul,hbv,←hau,inv_smul_smul]
  have hOZ : O ⊆ Z :=
    moveThickening_component_subset_of_hit (rapidTest_symm q C A B) hfixed ⟨c,hc⟩ ⟨u,hu,huO⟩
  have hOV : O ⊆ V := hOZ.trans hZV
  have hyO := hCross hy
  have hzO := hCross hz
  have hzV := hOV hzO
  obtain ⟨r,hr,y₀,hy₀,hyE⟩ := hyO
  obtain ⟨t,ht,z₀,hz₀,hzE⟩ := hzO
  have hcomp := testComponent_trans (testComponent_symm (rapidTest_symm q C A B) hy₀) hz₀
  obtain ⟨d,hd,hde⟩ := hDcomp _ _ hcomp
  have hh : (t*d*r⁻¹) • y = z := by
    rw [mul_smul,mul_smul,←hyE,inv_smul_smul,hde,hzE]
  have hm : t*d*r⁻¹ ∈ nextPad q C B D := by
    simpa only [one_mul] using mul_cosetPad_inv_mem_nextPad q hB hD h1B ht hd hr
  exact ⟨hyV,.single ⟨hyV,hzV,t*d*r⁻¹,hLarge hm,hh⟩⟩


/-- Rapidly separated covers for the ordered relative coloring construction. -/
structure ClopenRapidCover (q : H →* P) (C A : Finset H) (d : ℕ) (X : Type*)
    [MulAction H X] [TopologicalSpace X] where
  levels : ℕ
  pieces : ℕ → Fin (d+1) → Set X
  moves : ℕ → Finset H
  one_mem_moves : ∀ n, 1 ∈ moves n
  symmetric_moves : ∀ n, SymmetricMoves (moves n)
  kernel_moves : ∀ n, ∀ g ∈ moves n, q g = 1
  includes_test : ∀ n, ∀ g ∈ C*A, q g = 1 → g ∈ moves n
  clopen_pieces : ∀ n i, IsClopen (pieces n i)
  covers : ∀ x, ∃ n < levels, ∃ i, x ∈ pieces n i
  independent : ∀ n i x, x ∈ pieces n i → ∀ g ∈ C*A, q g ≠ 1 → g • x ∉ pieces n i
  bounded : ∀ n i, ∃ D : Finset H, ∀ x y, TestComponent A (pieces n i) x y →
    ∃ g ∈ D, g • x = y
  cross : ∀ n m, n < m → ∀ i c, c ∈ C → ∀ x, x ∈ pieces n i →
    ∀ y ∈ crossComponentImage c A (moves n) (pieces n i) x, y ∈ pieces m i →
    ∀ z ∈ crossComponentImage c A (moves n) (pieces n i) x, TestComponent (moves m) (pieces m i) y z

omit [TopologicalSpace X] [DecidableEq P] in
private theorem triplePad_image (q : H →* P) {B C : Finset H}
    (hB : ∀ g ∈ B, q g = 1) {g : H} (hg : g ∈ triplePad B C) :
    ∃ c ∈ C, q g = q c := by
  obtain ⟨w,hw,b,hb,rfl⟩ := Finset.mem_mul.mp hg
  obtain ⟨a,ha,c,hc,rfl⟩ := Finset.mem_mul.mp hw
  obtain ⟨a',ha',rfl⟩ := Finset.mem_inv.mp ha
  exact ⟨c,hc,by simp [hB _ ha',hB _ hb]⟩

omit [TopologicalSpace X] [DecidableEq P] in
private theorem overlapTest_image (q : H →* P) {B C : Finset H}
    (hB : ∀ g ∈ B, q g = 1) :
    ∀ g ∈ (triplePad B C)⁻¹*(triplePad B C), ∃ c ∈ C⁻¹*C, q c = q g := by
  intro g hg
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hg
  obtain ⟨a',ha',rfl⟩ := Finset.mem_inv.mp ha
  obtain ⟨c,hc,he⟩ := triplePad_image q hB ha'
  obtain ⟨d,hd,he'⟩ := triplePad_image q hB hb
  exact ⟨c⁻¹*d,Finset.mem_mul.mpr ⟨c⁻¹,Finset.mem_inv.mpr ⟨c,hc,rfl⟩,d,hd,rfl⟩,
    by simp only [map_mul,map_inv,he,he']⟩

set_option maxHeartbeats 1200000 in
/-- The ordered clopen amplification of the subgroup covers, in the form
needed for the relative packing step (CJMST Lemma 10.5). -/
theorem exists_clopenRapidCover (q : H →* P)
    (hact : ∀ g : H, Continuous (fun x : X => g • x))
    (hfree : ∀ g : H, ∀ x : X, g • x = x → g = 1)
    {d : ℕ} (hd : HasClopenSubgroupDimension q.ker d X)
    (hpal : HasClopenQuotientPalettes q X)
    (C A : Finset H) (hC1 : 1 ∈ C) (hA1 : 1 ∈ A) (hA : ∀ g ∈ A, q g = 1) :
    Nonempty (ClopenRapidCover q C A d X) := by
  classical
  let Pad := {B : Finset H // ∀ g ∈ B, q g = 1}
  have hstage (B : Pad) := hd (rapidTest q C A B.val)
    (rapidTest_kernel q C A B.val) (rapidTest_symm q C A B.val)
  choose V hV hVcover D hD hDb using hstage
  let Bbase := A ∪ ((C*A).filter fun g => q g = 1)
  have hbase : ∀ g ∈ Bbase, q g = 1 := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg|hg
    · exact hA g hg
    · exact (Finset.mem_filter.mp hg).2
  let Bs : ℕ → Pad := Nat.rec ⟨symmetricNeighborhood Bbase,
      symmetricNeighborhood_subset_subgroup Bbase q.ker hbase⟩
    (fun _ B => ⟨nextPad q C B.val (D B),nextPad_kernel q C B.val (D B) B.property⟩)
  let B (n : ℕ) := (Bs n).val
  have hB (n : ℕ) := (Bs n).property
  have hBs (n : ℕ) : SymmetricMoves (B n) := by
    cases n
    · exact symmetricNeighborhood_symmetric _
    · exact symmetricNeighborhood_symmetric _
  have hB1 (n : ℕ) : 1 ∈ B n := by
    cases n
    · exact one_mem_symmetricNeighborhood _
    · exact one_mem_symmetricNeighborhood _
  have hBmono : Monotone B := monotone_nat_of_le_succ fun n => subset_nextPad q C (B n) (D (Bs n))
  obtain ⟨l,hpal'⟩ := hpal (C⁻¹*C)
  let T (n : ℕ) := triplePad (B n) C
  let E := (Finset.range l).biUnion fun n => (T n)⁻¹ * (T n)
  have hE : ∀ g ∈ E, ∃ c ∈ C⁻¹*C, q c = q g := by
    intro g hg
    obtain ⟨n,_,hn⟩ := Finset.mem_biUnion.mp hg
    exact overlapTest_image q (hB n) g hn
  obtain ⟨W,hW,hWcover,hWind⟩ := hpal' E hE
  let W' (n : ℕ) := if h : n < l then W ⟨n,h⟩ else ∅
  let S (i : Fin (d+1)) (n : ℕ) := V (Bs n) i ∩ W' n
  have hS (i : Fin (d+1)) (n : ℕ) : IsClopen (S i n) := by
    apply (hV (Bs n) i).inter
    dsimp [W']
    split
    · exact hW _
    · exact isClopen_empty
  have hSind (i : Fin (d+1)) (n : ℕ) (x : X) (hx : x ∈ S i n)
      (g : H) (hg : g ∈ (T n)⁻¹*(T n)) (hn : q g ≠ 1) : g • x ∉ S i n := by
    by_cases h : n < l
    · have hx' : x ∈ W ⟨n,h⟩ := by simpa [W',h] using hx.2
      intro hgx
      exact hWind ⟨n,h⟩ x hx' g (Finset.mem_biUnion.mpr ⟨n,Finset.mem_range.mpr h,hg⟩) hn
        (by simpa [W',h] using hgx.2)
    · exact (by simpa [W',h] using hx.2 : False).elim
  have hcomp (i : Fin (d+1)) (n : ℕ) (x y : X)
      (h : TestComponent (rapidTest q C A (B n)) (S i n) x y) : ∃ g ∈ D (Bs n), g • x = y :=
    hDb (Bs n) i x y (testComponent_mono Subset.rfl Set.inter_subset_left h)
  let f (i : Fin (d+1)) (n : ℕ) := saturateTranslatedComponents (rapidTest q C A (B n)) (S i n)
    (fun c : (C : Set H) => cosetPad q (B n) C c.val)
  have hcl (i : Fin (d+1)) (n : ℕ) (U : Set X) (hU : IsClopen U) :
      IsClopen (f i n U) := isClopen_saturateTranslatedComponents hact hfree
    (hS i n) hU (hcomp i n) _
  have hmono (i : Fin (d+1)) (n : ℕ) (U : Set X) : U ⊆ f i n U := Set.subset_union_left
  have htid (i : Fin (d+1)) (n : ℕ) (U : Set X) :
      f i n (f i n U) = f i n U := saturateTranslatedComponents_idempotent
    (fun a b y c hc r hr hy hy' => cosetPad_alignment q (hB n) (hSind i n) hc hr hy hy') _
  have hthick (i : Fin (d+1)) (n : ℕ) (U : Set X) :
      moveThickening (B n) (f i n U) ⊆ moveThickening (B (n+1)) U :=
    saturate_cosetPad_thickening q (hB n) (hD (Bs n)) (hcomp i n) U
  let U (n : ℕ) (i : Fin (d+1)) := foldClopenSaturation (f i) 0 n (S i n)
  have hUB (n : ℕ) (i : Fin (d+1)) : moveThickening A (U n i) ⊆ moveThickening (B n) (S i n) := by
    refine (moveThickening_mono_moves (show A ⊆ B 0 from fun g hg =>
      subset_symmetricNeighborhood _ (Finset.mem_union_left _ hg)) _).trans ?_
    simpa only [zero_add] using foldClopenSaturation_thickens (hthick i) 0 n (S i n)
  refine ⟨⟨l,U,B,hB1,hBs,hB,?_,?_,?_,?_,?_,?_⟩⟩
  · intro n g hg he
    exact hBmono (Nat.zero_le n) (subset_symmetricNeighborhood _
      (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hg,he⟩)))
  · intro n i
    exact isClopen_foldClopenSaturation (hcl i) 0 n (hS i n)
  · intro x
    obtain ⟨j,hj⟩ := hWcover x
    obtain ⟨i,hi⟩ := hVcover (Bs j.val) x
    exact ⟨j.val,j.isLt,i,subset_foldClopenSaturation (hmono i) 0 j.val _
      ⟨hi,by simpa [W',j.isLt] using hj⟩⟩
  · intro n i
    exact rapidCover_independent q (hB1 n) hC1 hA1 (hB n) hA (hSind i n) (hUB n i)
  · intro n i
    refine ⟨B n * D (Bs n) * (B n)⁻¹,?_⟩
    intro x y hxy
    have hu : U n i ⊆ moveThickening (B n) (S i n) :=
      (subset_moveThickening hA1 (U n i)).trans (hUB n i)
    obtain ⟨a,ha,r,hr,he⟩ := hu hxy.1
    obtain ⟨b,hb,s,hs,he'⟩ := hu (testComponent_end hxy)
    have hcomp' := testComponent_of_thickened_subset hu hA1
      (fun _ hg => rapidTest_of_A q (C := C) (hB n) hA hg) hxy ha hb hr hs he he'
    obtain ⟨g,hg,hgs⟩ := hcomp i n r s hcomp'
    exact ⟨b*g*a⁻¹,Finset.mem_mul.mpr ⟨b*g,Finset.mem_mul.mpr ⟨b,hb,g,hg,rfl⟩,a⁻¹,
      Finset.mem_inv.mpr ⟨a,ha,rfl⟩,rfl⟩,by rw [mul_smul,mul_smul,← he,inv_smul_smul,hgs,he']⟩
  · intro n m hnm i c hc x hx
    let Z := foldClopenSaturation (f i) n (m-n) (S i m)
    have hEq : U m i = foldClopenSaturation (f i) 0 n Z := by
      have h := foldClopenSaturation_add (f i) 0 n (m-n) (S i m)
      simpa only [zero_add,Nat.add_sub_of_le hnm.le] using h
    have hZU : Z ⊆ U m i := hEq.symm ▸ subset_foldClopenSaturation (hmono i) 0 n Z
    have hUZ : U m i ⊆ moveThickening (B n) Z := by
      rw [hEq]
      exact (subset_moveThickening (hB1 0) _).trans (by
        simpa only [zero_add] using foldClopenSaturation_thickens (hthick i) 0 n Z)
    have hfixed : f i n Z = Z := foldClopenSaturation_fixed (htid i) n (by omega) _
    exact rapidCross_comparison q hA1 (hB1 n) hA (hB n) (hD (Bs n)) (hUB n i)
      hZU hUZ (hcomp i n) hfixed (hBmono hnm) hc hx

end RapidCovers

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.ClopenRapidCovers

-- BEGIN COMPLETE MODULE HirschProof.ClopenRelativeColoring
section
                                    

set_option autoImplicit false
noncomputable section

open Set Topology TopologicalSpace
open scoped Pointwise

namespace LocalHirschHyperfinite

section DescendingColoring

variable {H P X : Type*} [Group H] [Group P] [TopologicalSpace X] [MulAction H X]
variable [DecidableEq H] [DecidableEq P]
variable {q : H →* P} {C A : Finset H} {d : ℕ}

/-- A partial clopen coloring of the higher levels in one rapid cover color. -/
structure ClopenColoredTail (R : ClopenRapidCover q C A d X) (i : Fin (d+1))
    (B D L : Finset H) (k n : ℕ) where
  site : ℕ → Fin (k+1) → Set X
  clopen : ∀ m j, IsClopen (site m j)
  inside : ∀ m j x, x ∈ site m j → n ≤ m ∧ m < R.levels ∧ x ∈ R.pieces m i
  stable : ∀ m j x y, x ∈ site m j →
    TestComponent (R.moves m) (R.pieces m i) x y → y ∈ site m j
  separated : ∀ m m' j j' x y, x ∈ site m j → y ∈ site m' j' →
    ∀ g ∈ D, g • x = y → m = m' ∧ j = j'
  same_color_level : ∀ m m' j x y, x ∈ site m j → y ∈ site m' j →
    ∀ g ∈ L, g • x = y → m = m'
  covered : ∀ m, n ≤ m → m < R.levels → ∀ x ∈ R.pieces m i,
    ∃ m' < R.levels, ∃ j, x ∈ moveThickening B (site m' j)

private def ClopenColoredTail.empty (R : ClopenRapidCover q C A d X) (i : Fin (d+1))
    (B D L : Finset H) (k : ℕ) : ClopenColoredTail R i B D L k R.levels where
  site := fun _ _ => ∅
  clopen := fun _ _ => isClopen_empty
  inside := fun _ _ _ hx => hx.elim
  stable := fun _ _ _ _ hx => hx.elim
  separated := fun _ _ _ _ _ _ hx => hx.elim
  same_color_level := fun _ _ _ _ _ hx => hx.elim
  covered := fun _ h₁ h₂ => (Nat.not_lt_of_ge h₁ h₂).elim

omit [TopologicalSpace X] [DecidableEq H] in
private theorem crossComponentImage_mem {c g : H} {K : Finset H} {U : Set X} {x z : X}
    (hg : g ∈ A) (hz : TestComponent K U x z) :
    (c*g) • z ∈ crossComponentImage c A K U x :=
  ⟨g • z,⟨g,hg,z,hz,rfl⟩,(mul_smul _ _ _).symm⟩

omit [TopologicalSpace X] [DecidableEq H] in
private theorem crossComponentImage_move_mem {c : H} {K : Finset H} {U : Set X} {x z : X}
    (hA1 : 1 ∈ A) (hz : TestComponent K U x z) :
    c • z ∈ crossComponentImage c A K U x := by
  simpa only [mul_one] using crossComponentImage_mem (c := c) hA1 hz

private def ClopenColoredTail.oldColor
    {R : ClopenRapidCover q C A d X} {i : Fin (d+1)} {B D L : Finset H} {k n : ℕ}
    (T : ClopenColoredTail R i B D L k n) (j : Fin (k+1)) : Set X :=
  ⋃ m : Fin R.levels, T.site m.val j

private def ClopenColoredTail.oldSites
    {R : ClopenRapidCover q C A d X} {i : Fin (d+1)} {B D L : Finset H} {k n : ℕ}
    (T : ClopenColoredTail R i B D L k n) : Set X :=
  ⋃ j : Fin (k+1), T.oldColor j

omit [DecidableEq P] in
private theorem isClopen_oldColor {R : ClopenRapidCover q C A d X} {i : Fin (d+1)}
    {B D L : Finset H} {k n : ℕ} (T : ClopenColoredTail R i B D L k n) (j : Fin (k+1)) :
    IsClopen (T.oldColor j) := isClopen_iUnion_of_finite fun m => T.clopen m.val j

omit [DecidableEq P] in
private theorem isClopen_oldSites {R : ClopenRapidCover q C A d X} {i : Fin (d+1)}
    {B D L : Finset H} {k n : ℕ} (T : ClopenColoredTail R i B D L k n) :
    IsClopen T.oldSites := isClopen_iUnion_of_finite fun j => isClopen_oldColor T j

omit [DecidableEq P] in
private theorem oldColor_mem_iff {R : ClopenRapidCover q C A d X} {i : Fin (d+1)}
    {B D L : Finset H} {k n : ℕ} (T : ClopenColoredTail R i B D L k n) {j : Fin (k+1)} {x : X} :
    x ∈ T.oldColor j ↔ ∃ m, x ∈ T.site m j := by
  constructor
  · intro hx
    obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hx
    exact ⟨m.val,hm⟩
  · rintro ⟨m,hm⟩
    exact Set.mem_iUnion.mpr ⟨⟨m,(T.inside m j x hm).2.1⟩,hm⟩

omit [DecidableEq P] in
private theorem oldSites_mem_iff {R : ClopenRapidCover q C A d X} {i : Fin (d+1)}
    {B D L : Finset H} {k n : ℕ} (T : ClopenColoredTail R i B D L k n) {x : X} :
    x ∈ T.oldSites ↔ ∃ m j, x ∈ T.site m j := by
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨m,hm⟩ := (oldColor_mem_iff T).mp hj
    exact ⟨m,j,hm⟩
  · rintro ⟨m,j,hm⟩
    exact Set.mem_iUnion.mpr ⟨j,(oldColor_mem_iff T).mpr ⟨m,hm⟩⟩

omit [DecidableEq P] in
private theorem oldColor_component_mem_iff {R : ClopenRapidCover q C A d X} {i : Fin (d+1)}
    {B D L : Finset H} {k n : ℕ} (T : ClopenColoredTail R i B D L k (n+1))
    (hA1 : 1 ∈ A) {g : H} (hg : g ∈ C) {x y : X}
    (hxy : TestComponent (R.moves n) (R.pieces n i) x y) (j : Fin (k+1)) :
    g • x ∈ T.oldColor j ↔ g • y ∈ T.oldColor j := by
  have move {x y : X} (hxy : TestComponent (R.moves n) (R.pieces n i) x y)
      (hx : g • x ∈ T.oldColor j) : g • y ∈ T.oldColor j := by
    obtain ⟨m,hm⟩ := (oldColor_mem_iff T).mp hx
    obtain ⟨hnm,_,hU⟩ := T.inside m j _ hm
    have h₁ := crossComponentImage_move_mem (c := g) hA1 (show TestComponent (R.moves n) _ x x
      from ⟨hxy.1,.refl⟩)
    have h₂ := crossComponentImage_move_mem (c := g) hA1 hxy
    have hcomp := R.cross n m hnm i g hg x hxy.1 _ h₁ hU _ h₂
    exact (oldColor_mem_iff T).mpr ⟨m,T.stable m j _ _ hm hcomp⟩
  exact ⟨move hxy,move (testComponent_symm (R.symmetric_moves n) hxy)⟩

omit [DecidableEq P] in
private theorem prune_stable {R : ClopenRapidCover q C A d X} {i : Fin (d+1)}
    {B D L : Finset H} {k n : ℕ} (T : ClopenColoredTail R i B D L k (n+1))
    (hA1 : 1 ∈ A) (hBC : B ⊆ C) (hB : SymmetricMoves B) {x y : X}
    (hx : x ∈ R.pieces n i \ moveThickening B T.oldSites)
    (hxy : TestComponent (R.moves n) (R.pieces n i) x y) :
    y ∈ R.pieces n i \ moveThickening B T.oldSites := by
  refine ⟨testComponent_end hxy,?_⟩
  rintro ⟨b,hb,z,hz,hzy⟩
  obtain ⟨m,j,hz⟩ := (oldSites_mem_iff T).mp hz
  have hzy' : b⁻¹ • y = z := by rw [← hzy,inv_smul_smul]
  have hy' : b⁻¹ • y ∈ T.oldColor j := (oldColor_mem_iff T).mpr ⟨m,hzy'.symm ▸ hz⟩
  have hx' := (oldColor_component_mem_iff T hA1 (hBC (hB hb)) hxy j).mpr hy'
  obtain ⟨m,hm⟩ := (oldColor_mem_iff T).mp hx'
  exact hx.2 ⟨b,hb,b⁻¹ • x,(oldSites_mem_iff T).mpr ⟨m,j,hm⟩,smul_inv_smul _ _⟩

omit [DecidableEq P] in
private theorem prune_separated {R : ClopenRapidCover q C A d X} {i : Fin (d+1)}
    {B D L : Finset H} {k n : ℕ} (T : ClopenColoredTail R i B D L k (n+1))
    (hA1 : 1 ∈ A) (hBC : B ⊆ C) (hB : SymmetricMoves B)
    (hDrep : ∀ g ∈ D, ∃ b ∈ B, ∃ a ∈ A, b⁻¹*a = g) {x y : X}
    (hx : x ∈ R.pieces n i \ moveThickening B T.oldSites) (hy : y ∈ T.oldSites) :
    ∀ g ∈ D, g • x ≠ y := by
  intro g hg he
  obtain ⟨b,hb,a,ha,rfl⟩ := hDrep g hg
  obtain ⟨m,j,hm⟩ := (oldSites_mem_iff T).mp hy
  obtain ⟨hnm,_,hU⟩ := T.inside m j y hm
  have hxx : TestComponent (R.moves n) (R.pieces n i) x x := ⟨hx.1,.refl⟩
  have hy' : y ∈ crossComponentImage b⁻¹ A (R.moves n) (R.pieces n i) x :=
    he ▸ crossComponentImage_mem (c := b⁻¹) ha hxx
  have hx' := crossComponentImage_move_mem (c := b⁻¹) hA1 hxx
  have hcomp := R.cross n m hnm i b⁻¹ (hBC (hB hb)) x hx.1 y hy' hU _ hx'
  have hx'' := T.stable m j _ _ hm hcomp
  exact hx.2 ⟨b,hb,b⁻¹ • x,(oldSites_mem_iff T).mpr ⟨m,j,hx''⟩,smul_inv_smul _ _⟩


set_option maxHeartbeats 1200000 in
private theorem ClopenColoredTail.extend
    {R : ClopenRapidCover q C A d X} {i : Fin (d+1)} {B D L : Finset H} {k n : ℕ}
    (T : ClopenColoredTail R i B D L k (n+1))
    (hact : ∀ g : H, Continuous (fun x : X => g • x))
    (hn : n < R.levels) (hA1 : 1 ∈ A) (hB1 : 1 ∈ B) (hD1 : 1 ∈ D)
    (hB : SymmetricMoves B) (hDS : SymmetricMoves D) (hLS : SymmetricMoves L)
    (hBC : B ⊆ C) (hLC : L ⊆ C) (hDC : D ⊆ C*A)
    (hDrep : ∀ g ∈ D, ∃ b ∈ B, ∃ a ∈ A, b⁻¹*a = g)
    (hpack : ∀ F : Finset H, F ⊆ L →
      (∀ g ∈ F, ∀ h ∈ F, g ≠ h → g*h⁻¹ ∉ D) → F.card ≤ k) :
    Nonempty (ClopenColoredTail R i B D L k n) := by
  classical
  let P := R.pieces n i \ moveThickening B T.oldSites
  let Q (j : Fin (k+1)) := ⋂ g : (L : Set H),
    ((fun x : X => g.val • x) ⁻¹' T.oldColor j)ᶜ
  let Earlier (j : Fin (k+1)) := ⋃ a : {a : Fin (k+1) // a < j}, Q a.val
  let N (j : Fin (k+1)) := (P ∩ Q j) \ Earlier j
  have hPc : IsClopen P := (R.clopen_pieces n i).diff (isClopen_moveThickening hact B (isClopen_oldSites T))
  have hQ (j : Fin (k+1)) {x : X} :
      x ∈ Q j ↔ ∀ g ∈ L, g • x ∉ T.oldColor j :=
    ⟨fun h g hg => Set.mem_iInter.mp h ⟨g,hg⟩,
      fun h => Set.mem_iInter.mpr fun g => h g.val g.property⟩
  have hQc (j : Fin (k+1)) : IsClopen (Q j) := isClopen_iInter_of_finite fun g =>
    ((isClopen_oldColor T j).preimage (hact g.val)).compl
  have hNc (j : Fin (k+1)) : IsClopen (N j) :=
    (hPc.inter (hQc j)).diff (isClopen_iUnion_of_finite fun a => hQc a.val)
  have oldColor_separate {j j' : Fin (k+1)} {x y : X} (hx : x ∈ T.oldColor j)
      (hy : y ∈ T.oldColor j') {g : H} (hg : g ∈ D) (he : g • x = y) : j = j' := by
    obtain ⟨m,hm⟩ := (oldColor_mem_iff T).mp hx
    obtain ⟨m',hm'⟩ := (oldColor_mem_iff T).mp hy
    exact (T.separated _ _ _ _ _ _ hm hm' g hg he).2
  have hasColor (x : X) : ∃ j : Fin (k+1), x ∈ Q j := by
    by_contra! h
    have hf (j : Fin (k+1)) : ∃ g ∈ L, g • x ∈ T.oldColor j := by
      simpa only [hQ,not_forall,not_not,exists_prop] using h j
    choose f hfL hf' using hf
    let F := Finset.univ.image f
    have hF : F ⊆ L := by
      intro g hg
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hg
      exact hfL j
    have hFi : Function.Injective f := by
      intro j j' he
      exact oldColor_separate (hf' j) (hf' j') hD1 (by rw [one_smul,he])
    have hFsep : ∀ g ∈ F, ∀ b ∈ F, g ≠ b → g*b⁻¹ ∉ D := by
      intro g hg b hb hne hd
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨j',_,rfl⟩ := Finset.mem_image.mp hb
      have he := oldColor_separate (hf' j') (hf' j) hd
        (by rw [mul_smul,inv_smul_smul] : (f j*(f j')⁻¹) • (f j' • x) = f j • x)
      exact hne (congrArg f he.symm)
    have hcard := hpack F hF hFsep
    rw [Finset.card_image_of_injective _ hFi] at hcard
    simp at hcard
  have coverN (x : X) (hx : x ∈ P) : ∃ j, x ∈ N j := by
    let p (a : ℕ) := ∃ j : Fin (k+1), j.val = a ∧ x ∈ Q j
    have hp : ∃ a, p a := by obtain ⟨j,hj⟩ := hasColor x; exact ⟨j.val,j,rfl,hj⟩
    obtain ⟨j,hj,hxq⟩ := Nat.find_spec hp
    refine ⟨j,⟨hx,hxq⟩,?_⟩
    intro h
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp h
    exact Nat.find_min hp (show a.val.val < Nat.find hp from hj ▸ a.property) ⟨a.val,rfl,ha⟩
  have stableN (j : Fin (k+1)) {x y : X} (hx : x ∈ N j)
      (hxy : TestComponent (R.moves n) (R.pieces n i) x y) : y ∈ N j := by
    have invQ (a : Fin (k+1)) : x ∈ Q a ↔ y ∈ Q a := by
      rw [hQ,hQ]
      exact forall₂_congr (fun g hg =>
        not_congr (oldColor_component_mem_iff T hA1 (hLC hg) hxy a))
    refine ⟨⟨prune_stable T hA1 hBC hB hx.1.1 hxy,(invQ j).mp hx.1.2⟩,?_⟩
    intro h
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp h
    exact hx.2 (Set.mem_iUnion.mpr ⟨a,(invQ a.val).mpr ha⟩)
  have equalN {j j' : Fin (k+1)} {x : X} (h : x ∈ N j) (h' : x ∈ N j') : j = j' := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt|hlt
    · exact h'.2 (Set.mem_iUnion.mpr ⟨⟨j,hlt⟩,h.1.2⟩)
    · exact h.2 (Set.mem_iUnion.mpr ⟨⟨j',hlt⟩,h'.1.2⟩)
  have disjointMove {x y : X} {j j' : Fin (k+1)} (hx : x ∈ N j) (hy : y ∈ N j')
      {g : H} (hg : g ∈ D) (he : g • x = y) : j = j' := by
    have hx' : x ∈ R.pieces n i := hx.1.1.1
    have hy' : y ∈ R.pieces n i := hy.1.1.1
    have hq : q g = 1 := by
      by_contra hn
      exact R.independent n i x hx' g (hDC hg) hn (he.symm ▸ hy')
    have hrel : TestComponent (R.moves n) (R.pieces n i) x y :=
      ⟨hx',.single ⟨hx',hy',g,R.includes_test n g (hDC hg) hq,he⟩⟩
    exact equalN (stableN j hx hrel) hy
  let S (m : ℕ) (j : Fin (k+1)) : Set X := if m = n then N j else T.site m j
  have newmem (j : Fin (k+1)) {x : X} (hx : x ∈ N j) : x ∈ S n j := by simpa [S] using hx
  have oldmem (m : ℕ) (j : Fin (k+1)) {x : X} (hx : x ∈ T.site m j) : x ∈ S m j := by
    have hne : m ≠ n := by have := (T.inside m j x hx).1; omega
    simpa [S,hne] using hx
  have splitmem (m : ℕ) (j : Fin (k+1)) {x : X} (hx : x ∈ S m j) :
      (m = n ∧ x ∈ N j) ∨ x ∈ T.site m j := by
    by_cases h : m = n <;> simp_all [S]
  refine ⟨⟨S,?_,?_,?_,?_,?_,?_⟩⟩
  · intro m j
    dsimp [S]
    split
    · exact hNc j
    · exact T.clopen m j
  · intro m j x hx
    rcases splitmem m j hx with ⟨rfl,h⟩|h
    · exact ⟨le_rfl,hn,h.1.1.1⟩
    · obtain ⟨hnm,hm,hh⟩ := T.inside m j x h
      exact ⟨by omega,hm,hh⟩
  · intro m j x y hx hxy
    rcases splitmem m j hx with ⟨rfl,h⟩|h
    · exact newmem j (stableN j h hxy)
    · exact oldmem m j (T.stable m j x y h hxy)
  · intro m m' j j' x y hx hy g hg he
    rcases splitmem m j hx with ⟨rfl,hx'⟩|hx'
    · rcases splitmem m' j' hy with ⟨rfl,hy'⟩|hy'
      · exact ⟨rfl,disjointMove hx' hy' hg he⟩
      · exact (prune_separated T hA1 hBC hB hDrep hx'.1.1
          ((oldSites_mem_iff T).mpr ⟨m',j',hy'⟩) g hg he).elim
    · rcases splitmem m' j' hy with ⟨rfl,hy'⟩|hy'
      · exact (prune_separated T hA1 hBC hB hDrep hy'.1.1
          ((oldSites_mem_iff T).mpr ⟨m,j,hx'⟩) g⁻¹ (hDS hg)
          (by rw [←he,inv_smul_smul])).elim
      · exact T.separated _ _ _ _ _ _ hx' hy' g hg he
  · intro m m' j x y hx hy g hg he
    rcases splitmem m j hx with ⟨rfl,hx'⟩|hx'
    · rcases splitmem m' j hy with ⟨rfl,hy'⟩|hy'
      · rfl
      · exact ((hQ j).mp hx'.1.2 g hg (he.symm ▸ (oldColor_mem_iff T).mpr ⟨m',hy'⟩)).elim
    · rcases splitmem m' j hy with ⟨rfl,hy'⟩|hy'
      · exact ((hQ j).mp hy'.1.2 g⁻¹ (hLS hg) (by
          rw [←he,inv_smul_smul]
          exact (oldColor_mem_iff T).mpr ⟨m,hx'⟩)).elim
      · exact T.same_color_level _ _ _ _ _ hx' hy' g hg he
  · intro m hnm hm x hx
    have liftOld {b : ℕ} {j : Fin (k+1)} (h : x ∈ moveThickening B (T.site b j)) :
        x ∈ moveThickening B (S b j) := moveThickening_mono (fun _ h => oldmem b j h) h
    by_cases he : m = n
    · subst m
      by_cases hp : x ∈ moveThickening B T.oldSites
      · obtain ⟨g,hg,z,hz,hx'⟩ := hp
        obtain ⟨b,j,hb⟩ := (oldSites_mem_iff T).mp hz
        exact ⟨b,(T.inside b j z hb).2.1,j,liftOld ⟨g,hg,z,hb,hx'⟩⟩
      · obtain ⟨j,hj⟩ := coverN x ⟨hx,hp⟩
        exact ⟨n,hn,j,subset_moveThickening hB1 (S n j) (newmem j hj)⟩
    · obtain ⟨b,hb,j,h⟩ := T.covered m (by omega) hm x hx
      exact ⟨b,hb,j,liftOld h⟩

end DescendingColoring

section RelativeExtension
attribute [local instance] Classical.decEq

variable {H P X : Type*} [Group H] [Group P] [TopologicalSpace X] [MulAction H X]
variable [DecidableEq P]

omit [TopologicalSpace X] [MulAction H X] [DecidableEq P] in
private theorem mem_product3 {U V W : Finset H} {g : H} :
    g ∈ U*V*W ↔ ∃ u ∈ U, ∃ v ∈ V, ∃ w ∈ W, u*v*w = g := by
  constructor
  · intro h
    obtain ⟨a,ha,w,hw,rfl⟩ := Finset.mem_mul.mp h
    obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_mul.mp ha
    exact ⟨u,hu,v,hv,w,hw,rfl⟩
  · rintro ⟨u,hu,v,hv,w,hw,rfl⟩
    exact Finset.mem_mul.mpr ⟨u*v,Finset.mem_mul.mpr ⟨u,hu,v,hv,rfl⟩,w,hw,rfl⟩

omit [TopologicalSpace X] [MulAction H X] [DecidableEq P] in
private theorem symmetric_product3 {U V : Finset H} (hU : SymmetricMoves U) (hV : SymmetricMoves V) :
    SymmetricMoves (U*V*U) := by
  intro x hx
  obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := mem_product3.mp hx
  refine mem_product3.mpr ⟨c⁻¹,hU hc,b⁻¹,hV hb,a⁻¹,hU ha,?_⟩
  rw [mul_inv_rev,mul_inv_rev,mul_assoc]

omit [TopologicalSpace X] [DecidableEq P] in
private theorem testComponent_from_subgroup (G : Subgroup H)
    {K : Finset H} (hK : ∀ g ∈ K, g ∈ G) {U : Set X} {x y : X}
    (hx : TestComponent K U x y) : ∃ g ∈ G, g • x = y := by
  have aux {y : X} (p : Relation.ReflTransGen (TestEdge K U) x y) : ∃ g ∈ G, g • x = y := by
    induction p with
    | refl => exact ⟨1,G.one_mem,one_smul _ _⟩
    | tail _ e ih =>
      obtain ⟨g,hg,he⟩ := ih
      obtain ⟨b,hb,hbe⟩ := e.2.2
      exact ⟨b*g,G.mul_mem (hK _ hb) hg,by rw [mul_smul,he,hbe]⟩
  exact aux hx.2

/-- One extension step's clopen cover, using a number of colors independent of
the finite neighborhood tested inside the subgroup. -/
structure ClopenRelativeCover (G : Subgroup H) (C K : Finset H) (d k : ℕ)
    (X : Type*) [MulAction H X] [TopologicalSpace X] where
  sites : Fin (d+1) × Fin (k+1) → Set X
  clopen : ∀ p, IsClopen (sites p)
  covers : ∀ x, ∃ p, x ∈ sites p
  independent : ∀ p x, x ∈ sites p → ∀ g ∈ C*K, g ∉ G → g • x ∉ sites p
  bound : ∃ D : Finset H, (∀ g ∈ D, g ∈ G) ∧
    ∀ p x y, TestComponent K (sites p) x y → ∃ g ∈ D, g • x = y

set_option maxHeartbeats 1500000 in
/-- CJMST's clopen relative extension coloring, conditional on the algebraic
packing bound for this one step. -/
theorem exists_clopenRelativeCover (q : H →* P) (G : Subgroup H) (hFG : q.ker ≤ G)
    (hact : ∀ g : H, Continuous (fun x : X => g • x))
    (hfree : ∀ g : H, ∀ x : X, g • x = x → g = 1)
    {d k : ℕ} (hd : HasClopenSubgroupDimension q.ker d X)
    (hpal : HasClopenQuotientPalettes q X)
    (C : Finset H) (hC1 : 1 ∈ C) (hC : SymmetricMoves C)
    (K : Finset H) (hKG : ∀ g ∈ K, g ∈ G)
    (hp : HasRelativePacking q.ker G C k) :
    Nonempty (ClopenRelativeCover G C K d k X) := by
  classical
  obtain ⟨A,B,hKB,hA1,hB1,hA,hBG,hAinv,hB,hpack⟩ := hp K hKG
  let B3 := B*B*B
  let L := B3*C*B3
  let D := A*B*A
  let C' := L ∪ D
  let A' := (((B*A)*(B*A)) ∪ B3).filter (fun g => q g = 1)
  have hB3 (b : H) (hb : b ∈ B) : b ∈ B3 :=
    mem_product3.mpr ⟨b,hb,1,hB1,1,hB1,by simp⟩
  have hB3L : B3 ⊆ L := fun b hb => mem_product3.mpr
    ⟨b,hb,1,hC1,1,hB3 _ hB1,by simp⟩
  have hB3s : SymmetricMoves B3 := symmetric_product3 hB hB
  have hLs : SymmetricMoves L := symmetric_product3 hB3s hC
  have hDs : SymmetricMoves D := symmetric_product3 hAinv hB
  have hD1 : 1 ∈ D := mem_product3.mpr ⟨1,hA1,1,hB1,1,hA1,by simp⟩
  have hC'1 : 1 ∈ C' := Finset.mem_union_right _ hD1
  have hA'1 : 1 ∈ A' := Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (hB3 _ hB1),map_one _⟩
  have hA' (g : H) (hg : g ∈ A') : q g = 1 := (Finset.mem_filter.mp hg).2
  have hLC : L ⊆ C' := Finset.subset_union_left
  have hBC : B ⊆ C' := fun b hb => hLC (hB3L (hB3 _ hb))
  have hDC : D ⊆ C'*A' := fun g hg => Finset.mem_mul.mpr
    ⟨g,Finset.mem_union_right _ hg,1,hA'1,mul_one _⟩
  have hDrep (g : H) (hg : g ∈ D) : ∃ b ∈ B, ∃ a ∈ A', b⁻¹*a = g := by
    obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := mem_product3.mp hg
    refine ⟨b⁻¹,hB hb,b⁻¹*a*b*c,Finset.mem_filter.mpr ⟨Finset.mem_union_left _ ?_,?_⟩,?_⟩
    · exact Finset.mem_mul.mpr ⟨b⁻¹*a,Finset.mem_mul.mpr ⟨b⁻¹,hB hb,a,ha,rfl⟩,
        b*c,Finset.mem_mul.mpr ⟨b,hb,c,hc,rfl⟩,by rw [mul_assoc (b⁻¹*a)]⟩
    · simp only [map_mul,map_inv,show q a = 1 from hA _ ha,show q c = 1 from hA _ hc,
        mul_one,inv_mul_cancel]
    · simp only [inv_inv,mul_assoc,mul_inv_cancel_left]
  obtain ⟨R⟩ := exists_clopenRapidCover q hact hfree hd hpal C' A' hC'1 hA'1 hA'
  have allTails (i : Fin (d+1)) (a : ℕ) (ha : a ≤ R.levels) :
      Nonempty (ClopenColoredTail R i B D L k (R.levels-a)) := by
    induction a with
    | zero => simpa using (show Nonempty (ClopenColoredTail R i B D L k R.levels) from
        ⟨ClopenColoredTail.empty R i B D L k⟩)
    | succ a ih =>
      let n := R.levels - (a+1)
      have hnext : R.levels-a = n+1 := by dsimp [n]; omega
      obtain ⟨old⟩ := hnext ▸ ih (by omega)
      apply old.extend hact (by dsimp [n]; omega) hA'1 hB1 hD1 hB hDs hLs hBC hLC hDC hDrep
      exact hpack
  have all : ∀ i : Fin (d+1), Nonempty (ClopenColoredTail R i B D L k 0) := by
    intro i
    simpa using allTails i R.levels le_rfl
  let T (i : Fin (d+1)) := (all i).some
  let U (p : Fin (d+1) × Fin (k+1)) := moveThickening B ((T p.1).oldColor p.2)
  have hU (p : Fin (d+1) × Fin (k+1)) (x : X) : x ∈ U p ↔
      ∃ b ∈ B, ∃ u : X, ∃ n, u ∈ (T p.1).site n p.2 ∧ b • u = x := by
    constructor
    · rintro ⟨b,hb,u,hu,he⟩
      obtain ⟨n,hn⟩ := (oldColor_mem_iff _).mp hu
      exact ⟨b,hb,u,n,hn,he⟩
    · rintro ⟨b,hb,u,n,hn,he⟩
      exact ⟨b,hb,u,(oldColor_mem_iff _).mpr ⟨n,hn⟩,he⟩
  have hSame (p : Fin (d+1) × Fin (k+1)) {n m : ℕ} {x y : X}
      (hx : x ∈ (T p.1).site n p.2) (hy : y ∈ (T p.1).site m p.2)
      {g : H} (hg : g ∈ L) (he : g • x = y) : n = m ∧ q g = 1 := by
    have hnm := (T p.1).same_color_level n m p.2 x y hx hy g hg he
    subst m
    refine ⟨rfl,?_⟩
    by_contra hn
    exact R.independent n p.1 x ((T p.1).inside n p.2 x hx).2.2 g
      (Finset.mem_mul.mpr ⟨g,hLC hg,1,hA'1,mul_one _⟩) hn
      (he.symm ▸ ((T p.1).inside n p.2 y hy).2.2)
  have hb_L (g : H) (hg : g ∈ C*B) (b a : H) (hb : b ∈ B) (ha : a ∈ B) :
      b⁻¹*g*a ∈ L := by
    obtain ⟨c,hc,t,ht,rfl⟩ := Finset.mem_mul.mp hg
    have hta : t*a ∈ B3 := mem_product3.mpr ⟨t,ht,a,ha,1,hB1,mul_one _⟩
    exact mem_product3.mpr ⟨b⁻¹,hB3 _ (hB hb),c,hc,t*a,hta,by simp [mul_assoc]⟩
  refine ⟨⟨U,fun p => isClopen_moveThickening hact B (isClopen_oldColor (T p.1) p.2),?_,?_,?_⟩⟩
  · intro x
    obtain ⟨n,hn,i,hx⟩ := R.covers x
    obtain ⟨m,hm,j,b,hb,u,hu,he⟩ := (T i).covered n (Nat.zero_le _) hn x hx
    exact ⟨(i,j),(hU _ x).mpr ⟨b,hb,u,m,hu,he⟩⟩
  · intro p x hx g hg hn hy
    have hgB : g ∈ C*B := Finset.mul_subset_mul Subset.rfl hKB hg
    obtain ⟨b,hb,u,n,hu,he⟩ := (hU p x).mp hx
    obtain ⟨a,ha,v,m,hv,he'⟩ := (hU p (g • x)).mp hy
    have hmove : (a⁻¹*g*b) • u = v := by rw [mul_smul,mul_smul,he,←he',inv_smul_smul]
    have hq := (hSame p hu hv (hb_L g hgB a b ha hb) hmove).2
    have hG : a⁻¹*g*b ∈ G := hFG (show a⁻¹*g*b ∈ q.ker from hq)
    have h := G.mul_mem (G.mul_mem (hBG _ ha) hG) (G.inv_mem (hBG _ hb))
    exact hn (by simpa [mul_assoc] using h)
  · choose F hF using R.bounded
    let E := (Finset.range R.levels).biUnion fun n =>
      (Finset.univ : Finset (Fin (d+1))).biUnion fun i => B*(F n i)*B⁻¹
    let D' := E.filter fun g => g ∈ G
    refine ⟨D',fun g hg => (Finset.mem_filter.mp hg).2,?_⟩
    intro p x y hxy
    obtain ⟨b,hb,u,n,hu,he⟩ := (hU p x).mp hxy.1
    have hu' := ((T p.1).inside n p.2 u hu).2.2
    have path {w : X} (h : Relation.ReflTransGen (TestEdge K (U p)) x w) :
        ∃ c ∈ B, ∃ v : X, v ∈ (T p.1).site n p.2 ∧ c • v = w ∧
          TestComponent A' (R.pieces n p.1) u v := by
      induction h with
      | refl => exact ⟨b,hb,u,hu,he,hu',.refl⟩
      | tail _ e ih =>
        obtain ⟨c,hc,v,hv,hv',huv⟩ := ih
        obtain ⟨a,ha,z,m,hz,hz'⟩ := (hU p _).mp e.2.1
        obtain ⟨g,hg,hg'⟩ := e.2.2
        have hmove : (a⁻¹*g*c) • v = z := by
          rw [mul_smul,mul_smul,hv',hg',←hz',inv_smul_smul]
        have hB3' : a⁻¹*g*c ∈ B3 := mem_product3.mpr ⟨a⁻¹,hB ha,g,hKB hg,c,hc,rfl⟩
        obtain ⟨rfl,hq⟩ := hSame p hv hz (hB3L hB3') hmove
        have hm : a⁻¹*g*c ∈ A' :=
          Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hB3',hq⟩
        exact ⟨a,ha,z,hz,hz',huv.1,huv.2.tail
          ⟨testComponent_end huv,((T p.1).inside n p.2 z hz).2.2,_,hm,hmove⟩⟩
    obtain ⟨a,ha,v,hv,hvy,huv⟩ := path hxy.2
    obtain ⟨g,hg,hgv⟩ := hF n p.1 u v huv
    have hE : a*g*b⁻¹ ∈ E := Finset.mem_biUnion.mpr
      ⟨n,Finset.mem_range.mpr ((T p.1).inside n p.2 u hu).2.1,Finset.mem_biUnion.mpr
        ⟨p.1,Finset.mem_univ _,mem_product3.mpr
          ⟨a,ha,g,hg,b⁻¹,Finset.mem_inv.mpr ⟨b,hb,rfl⟩,rfl⟩⟩⟩
    have hdisp : (a*g*b⁻¹) • x = y := by
      rw [mul_smul,mul_smul,←he,inv_smul_smul,hgv,hvy]
    obtain ⟨u,hu,heq⟩ := testComponent_from_subgroup G hKG hxy
    have hh := free_smul_injective hfree x (hdisp.trans heq.symm)
    exact ⟨a*g*b⁻¹,Finset.mem_filter.mpr ⟨hE,hh.symm ▸ hu⟩,hdisp⟩

end RelativeExtension

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.ClopenRelativeColoring

-- BEGIN COMPLETE MODULE HirschProof.RationalAutomorphismPacking
section
                                      

set_option autoImplicit false
noncomputable section

open Set TensorProduct
open scoped Pointwise

namespace LocalHirschHyperfinite

private theorem exists_integral_scale {I : Type*} [Fintype I] (f : I → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ m : I → ℤ, ∀ i, (d : ℚ) * f i = (m i : ℚ) := by
  classical
  let d := ∏ i, (f i).den
  have hd : 0 < d := Finset.prod_pos fun i _ => (f i).den_pos
  have hmult (i : I) : ∃ m : ℤ, (d : ℚ) * f i = m := by
    obtain ⟨k,hk⟩ := Finset.dvd_prod_of_mem (fun i => (f i).den) (Finset.mem_univ i)
    change d = (f i).den * k at hk
    have hne : ((f i).den : ℚ) ≠ 0 := by exact_mod_cast (f i).den_nz
    refine ⟨((k : ℤ) * (f i).num),?_⟩
    calc
      (d : ℚ) * f i = (d : ℚ) * ((f i).num / (f i).den) :=
        congrArg ((d : ℚ) * ·) (f i).num_div_den.symm
      _ = _ := by
        rw [hk,Nat.cast_mul,Int.cast_mul,Int.cast_natCast]
        field_simp
  choose m hm using hmult
  exact ⟨d,hd,m,hm⟩

section IntegerCoordinates
attribute [local instance] Classical.decEq

private def coordinateBox (e : ℕ) (R : ℤ) : Finset (Fin e → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-R) R)

private theorem mem_coordinateBox {e : ℕ} {R : ℤ} {v : Fin e → ℤ} :
    v ∈ coordinateBox e R ↔ ∀ i, |v i| ≤ R := by
  simp only [coordinateBox,Fintype.mem_piFinset,Finset.mem_Icc,abs_le]

variable {G : Type*} [Group G] {e : ℕ}
variable (z : G →* Multiplicative (Fin e → ℚ))

private def scaledBox (s : ℕ) (R : ℤ) : Set G :=
  {x | ∃ v ∈ coordinateBox e R, ∀ i, (s : ℚ) * Multiplicative.toAdd (z x) i = v i}

private theorem finite_scaledBox (hz : Function.Injective z) {s : ℕ} (hs : 0 < s) (R : ℤ) :
    (scaledBox z s R).Finite := by
  classical
  let A := scaledBox z s R
  have h (x : A) : ∃ v ∈ coordinateBox e R,
      ∀ i, (s : ℚ)* Multiplicative.toAdd (z x.val) i = (v i : ℚ) := x.property
  choose f hf he using h
  let f' (x : A) : (coordinateBox e R : Set (Fin e → ℤ)) := ⟨f x,hf x⟩
  apply Set.finite_coe_iff.mp
  apply Finite.of_injective f'
  intro x y hc
  apply Subtype.ext
  apply hz
  funext i
  have heq := congrFun (congrArg Subtype.val hc) i
  change f x i = f y i at heq
  have hx := he x i
  have hy := he y i
  rw [heq] at hx
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  exact mul_left_cancel₀ hs0 (hx.trans hy.symm)

private theorem exists_scaledBox_contains (K : Finset G) :
    ∃ s : ℕ, 0 < s ∧ ∃ R : ℕ, (K : Set G) ⊆ scaledBox z s R := by
  classical
  obtain ⟨s,hs,a,ha⟩ := exists_integral_scale
    (fun p : ↥(K : Set G) × Fin e => Multiplicative.toAdd (z p.1.val) p.2)
  let R := (Finset.univ : Finset (↥(K : Set G) × Fin e)).sup fun p => (a p).natAbs
  refine ⟨s,hs,R,fun x hx => ⟨fun i => a (⟨x,hx⟩,i),mem_coordinateBox.mpr ?_,?_⟩⟩
  · intro i
    let p : ↥(K : Set G) × Fin e := (⟨x,hx⟩,i)
    have h : (a p).natAbs ≤ R :=
      Finset.le_sup (f := fun p : ↥(K : Set G) × Fin e => (a p).natAbs) (Finset.mem_univ p)
    have h' : ((a (⟨x,hx⟩,i)).natAbs : ℤ) ≤ R := by exact_mod_cast h
    simpa only [Int.natCast_natAbs] using h'
  · intro i
    exact ha (⟨x,hx⟩,i)

private theorem one_mem_scaledBox (s : ℕ) {R : ℤ} (hR : 0 ≤ R) :
    (1 : G) ∈ scaledBox z s R := by
  refine ⟨0,mem_coordinateBox.mpr fun i => ?_,fun i => ?_⟩
  · simpa using hR
  · simp [z.map_one]

private theorem inv_mem_scaledBox {s : ℕ} {R : ℤ} {x : G}
    (hx : x ∈ scaledBox z s R) : x⁻¹ ∈ scaledBox z s R := by
  obtain ⟨v,hv,he⟩ := hx
  refine ⟨-v,mem_coordinateBox.mpr fun i => ?_,fun i => ?_⟩
  · simpa only [Pi.neg_apply,abs_neg] using mem_coordinateBox.mp hv i
  · rw [map_inv]
    change (s : ℚ)* (-Multiplicative.toAdd (z x) i) = (-(v i) : ℤ)
    rw [mul_neg,he,Int.cast_neg]

private theorem mul_mem_scaledBox {s : ℕ} {R S : ℤ} {x y : G}
    (hx : x ∈ scaledBox z s R) (hy : y ∈ scaledBox z s S) :
    x*y ∈ scaledBox z s (R+S) := by
  obtain ⟨v,hv,hx⟩ := hx
  obtain ⟨w,hw,hy⟩ := hy
  refine ⟨v+w,mem_coordinateBox.mpr fun i => ?_,fun i => ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add (mem_coordinateBox.mp hv i) (mem_coordinateBox.mp hw i))
  · rw [map_mul]
    change (s : ℚ) * (Multiplicative.toAdd (z x) i + Multiplicative.toAdd (z y) i) =
      ((v i + w i : ℤ) : ℚ)
    rw [mul_add,hx,hy,Int.cast_add]

private theorem scaledBox_cube {s R : ℕ} {B : Finset G} {x : G}
    (hB : ∀ x ∈ B, x ∈ scaledBox z s R) (hx : x ∈ B*B*B) :
    x ∈ scaledBox z s (3 * (R : ℤ)) := by
  classical
  obtain ⟨d,hd,c,hc,rfl⟩ := Finset.mem_mul.mp hx
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp hd
  have h := mul_mem_scaledBox z (mul_mem_scaledBox z (hB _ ha) (hB _ hb)) (hB _ hc)
  simpa only [show (R : ℤ)+R+R = 3 * R from by omega] using h


private theorem scaledBox_rescale {s D : ℕ} {R : ℤ} {x : G}
    (hx : x ∈ scaledBox z s R) : x ∈ scaledBox z (D*s) ((D : ℤ)*R) := by
  obtain ⟨v,hv,he⟩ := hx
  refine ⟨fun i => (D : ℤ)*v i,mem_coordinateBox.mpr fun i => ?_,fun i => ?_⟩
  · rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg D)]
    exact mul_le_mul_of_nonneg_left (mem_coordinateBox.mp hv i) (Int.natCast_nonneg D)
  · rw [Nat.cast_mul,mul_assoc,he,Int.cast_mul,Int.cast_natCast]

private theorem scaledBox_matrix {s D L : ℕ} {R : ℤ} {x y : G} {M : Fin e → Fin e → ℤ}
    (hM : ∀ i j, |M i j| ≤ L)
    (heq : ∀ i, (D : ℚ)* Multiplicative.toAdd (z y) i =
      ∑ j, (M i j : ℚ)* Multiplicative.toAdd (z x) j)
    (hx : x ∈ scaledBox z s R) :
    y ∈ scaledBox z (D*s) ((e*L : ℤ)*R) := by
  obtain ⟨v,hv,he⟩ := hx
  refine ⟨fun i => ∑ j, M i j * v j,mem_coordinateBox.mpr fun i => ?_,fun i => ?_⟩
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _ : Fin e, (L : ℤ)*R := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hM i j) (mem_coordinateBox.mp hv j) (abs_nonneg _) (Int.natCast_nonneg L)
      _ = _ := by simp [mul_assoc]
  · rw [Nat.cast_mul,mul_comm (D : ℚ),mul_assoc,heq,Finset.mul_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_left_comm,he]

private def coordinateCell (D P R : ℕ) (a : ℤ) : ℤ × ℤ :=
  (a % (D : ℤ),(a+(P : ℤ)*R) / ((R : ℤ)+1))

private theorem coordinateCell_mem {D P R : ℕ} (hD : 0 < D) {a : ℤ}
    (ha : |a| ≤ (P : ℤ)*R) :
    coordinateCell D P R a ∈ (Finset.Icc 0 ((D : ℤ)-1)).product (Finset.Icc 0 (2*(P : ℤ))) := by
  have hD' : (0 : ℤ) < D := by exact_mod_cast hD
  have hR : 0 < (R : ℤ)+1 := by omega
  obtain ⟨ha₁,ha₂⟩ := abs_le.mp ha
  have h0 : 0 ≤ a+(P : ℤ)*R := by omega
  have hUp : a+(P : ℤ)*R < (2*(P : ℤ)+1)*((R : ℤ)+1) := by
    nlinarith [Int.natCast_nonneg P,Int.natCast_nonneg R]
  have hm : a % (D : ℤ) ≤ (D : ℤ)-1 := by
    have h := Int.emod_lt_of_pos a hD'
    omega
  have hu := (Int.ediv_lt_iff_lt_mul hR).mpr hUp
  refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Int.emod_nonneg _ (by omega),hm⟩,
    Finset.mem_Icc.mpr ⟨Int.ediv_nonneg h0 (le_of_lt hR),?_⟩⟩
  change (a+(P : ℤ)*R) / ((R : ℤ)+1) ≤ 2*(P : ℤ)
  omega

private theorem coordinateCell_eq {D P R : ℕ} (hD : 0 < D) {a b : ℤ}
    (eq : coordinateCell D P R a = coordinateCell D P R b) :
    ∃ c : ℤ, |c| ≤ R ∧ a-b = (D : ℤ)*c := by
  have hdvd : (D : ℤ) ∣ a-b :=
    Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (congrArg Prod.fst eq))
  obtain ⟨c,hc⟩ := hdvd
  refine ⟨c,?_,hc⟩
  let m := (R : ℤ)+1
  let u := a+(P : ℤ)*R
  let v := b+(P : ℤ)*R
  have hm : 0 < m := by dsimp [m]; omega
  have he : u / m = v / m := congrArg Prod.snd eq
  have hu := Int.emod_add_mul_ediv u m
  have hv := Int.emod_add_mul_ediv v m
  rw [he] at hu
  have hdiff : a-b = u % m - v % m := by
    have huv : u-v = u % m - v % m := by linarith
    change a+(P : ℤ)*R - (b+(P : ℤ)*R) = _ at huv
    linarith
  have hbound : |a-b| ≤ (R : ℤ) := by
    have hu' := Int.emod_lt_of_pos u hm
    have hv' := Int.emod_lt_of_pos v hm
    have hu₀ := Int.emod_nonneg u hm.ne.symm
    have hv₀ := Int.emod_nonneg v hm.ne.symm
    change u % m < (R : ℤ)+1 at hu'
    change v % m < (R : ℤ)+1 at hv'
    have hul : u % m ≤ (R : ℤ) := by omega
    have hvl : v % m ≤ (R : ℤ) := by omega
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hD' : (1 : ℤ) ≤ D := by exact_mod_cast hD
  have hmul : |c| ≤ (D : ℤ)*|c| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD' (abs_nonneg c)
  rw [hc,abs_mul,abs_of_nonneg (Int.natCast_nonneg D)] at hbound
  exact hmul.trans hbound

private theorem card_le_scaledBoxSeparated {D P R s : ℕ} (hD : 0 < D) (T : Finset G)
    (hT : ∀ x ∈ T, x ∈ scaledBox z (D*s) ((P : ℤ)*R))
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x*y⁻¹ ∉ scaledBox z s R) :
    T.card ≤ (D*(2*P+1))^e := by
  classical
  have hex (x : G) : ∃ a : Fin e → ℤ, x ∈ T →
      a ∈ coordinateBox e ((P : ℤ)*R) ∧
      ∀ i, ((D*s : ℕ) : ℚ)*Multiplicative.toAdd (z x) i = (a i : ℚ) := by
    by_cases hx : x ∈ T
    · obtain ⟨v,hv,he⟩ := hT x hx
      exact ⟨v,fun _ => ⟨hv,he⟩⟩
    · exact ⟨0,fun h => (hx h).elim⟩
  choose a ha using hex
  let I := (Finset.Icc 0 ((D : ℤ)-1)).product (Finset.Icc 0 (2*(P : ℤ)))
  let J := Fintype.piFinset (fun _ : Fin e => I)
  let f (x : G) (i : Fin e) := coordinateCell D P R (a x i)
  have hf : Set.MapsTo f (T : Set G) (J : Set (Fin e → ℤ × ℤ)) := fun x hx =>
    Fintype.mem_piFinset.mpr fun i => coordinateCell_mem hD (mem_coordinateBox.mp (ha x hx).1 i)
  have hfi : Set.InjOn f (T : Set G) := by
    intro x hx y hy he
    by_contra hn
    apply hsep x hx y hy hn
    have h (i : Fin e) : ∃ c : ℤ, |c| ≤ R ∧ a x i - a y i = (D : ℤ)*c :=
      coordinateCell_eq hD (congrFun he i)
    choose c hc hce using h
    refine ⟨c,mem_coordinateBox.mpr hc,fun i => ?_⟩
    rw [map_mul,map_inv]
    change (s : ℚ)*(Multiplicative.toAdd (z x) i + -Multiplicative.toAdd (z y) i) = (c i : ℚ)
    rw [← sub_eq_add_neg]
    have he₁ := (ha x hx).2 i
    have he₂ := (ha y hy).2 i
    have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
    apply mul_left_cancel₀ hD'
    simp only [mul_sub,← mul_assoc,← Nat.cast_mul,he₁,he₂]
    exact_mod_cast hce i
  have hI : I.card = D*(2*P+1) := by
    have hd : ((D : ℤ)-1+1-0).toNat = D := by omega
    have hp : (2*(P : ℤ)+1-0).toNat = 2*P+1 := by omega
    change ((Finset.Icc (0 : ℤ) ((D : ℤ)-1)).product
      (Finset.Icc (0 : ℤ) (2*(P : ℤ)))).card = _
    rw [Finset.product_eq_sprod,Finset.card_product,Int.card_Icc,Int.card_Icc,hd,hp]
  have hJ : J.card = (D*(2*P+1))^e := by simp [J,Fintype.card_piFinset,hI]
  exact hJ ▸ Finset.card_le_card_of_injOn f hf hfi

end IntegerCoordinates

section LinearActions

variable {G : Type*} [Group G] {e : ℕ}

/-- A faithful rational linear coordinate system provides bounded packing for
every finite set of linearizable automorphisms. -/
theorem hasAutomorphismPacking_of_rational_coordinates
    (z : G →* Multiplicative (Fin e → ℚ)) (hz : Function.Injective z)
    (Φ : Finset (G ≃* G)) (L : (G ≃* G) → (Fin e → ℚ) →ₗ[ℚ] (Fin e → ℚ))
    (hL : ∀ φ ∈ Φ, ∀ g, Multiplicative.toAdd (z (φ g)) = L φ (Multiplicative.toAdd (z g))) :
    ∃ k, HasAutomorphismPacking G Φ k := by
  classical
  let I := ↥(Φ : Set (G ≃* G)) × Fin e × Fin e
  let mat (p : I) := L p.1.val (Pi.single p.2.2 (1 : ℚ)) p.2.1
  obtain ⟨D,hD,m,hm⟩ := exists_integral_scale mat
  let M := (Finset.univ : Finset I).sup (fun p => (m p).natAbs)
  let P := 3*(D+e*M)
  have mat_bound (p : I) : |m p| ≤ (M : ℤ) := by
    have h : (m p).natAbs ≤ M :=
      Finset.le_sup (f := fun p : I => (m p).natAbs) (Finset.mem_univ p)
    have q : ((m p).natAbs : ℤ) ≤ M := by exact_mod_cast h
    simpa only [Int.natCast_natAbs] using q
  have mat_acts (φ : G ≃* G) (hφ : φ ∈ Φ) (x : G) (i : Fin e) :
      (D : ℚ) * Multiplicative.toAdd (z (φ x)) i =
        ∑ j : Fin e, (m (⟨φ,hφ⟩,i,j) : ℚ) * Multiplicative.toAdd (z x) j := by
    let v := Multiplicative.toAdd (z x)
    have hv : (∑ j : Fin e, v j • Pi.single j (1 : ℚ)) = v := by
      ext k
      simp [Finset.sum_apply,Pi.single_apply,Pi.smul_apply]
    have hl : L φ v i = ∑ j : Fin e, v j * L φ (Pi.single j (1 : ℚ)) i := by
      conv_lhs => rw [← hv]
      simp only [map_sum,LinearMap.map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [hL φ hφ x]
    change (D : ℚ)*L φ v i = _
    rw [hl,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (D : ℚ) * L φ (Pi.single j (1 : ℚ)) i = m (⟨φ,hφ⟩,i,j) :=
      hm (⟨φ,hφ⟩,i,j)
    rw [← he]
    ring
  refine ⟨(D*(2*P+1))^e,?_⟩
  intro K
  obtain ⟨s,hs,R,hKR⟩ := exists_scaledBox_contains z K
  let hf := finite_scaledBox z hz hs (R : ℤ)
  let B := hf.toFinset
  have hB (x : G) : x ∈ B ↔ x ∈ scaledBox z s R := hf.mem_toFinset
  refine ⟨B,fun x hx => (hB x).mpr (hKR hx),
    (hB 1).mpr (one_mem_scaledBox z s (Int.natCast_nonneg R)),
    fun x hx => (hB x⁻¹).mpr (inv_mem_scaledBox z ((hB x).mp hx)),?_⟩
  intro φ hφ T hT hsep
  apply card_le_scaledBoxSeparated z hD T
  · intro t ht
    obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_mul.mp (hT ht)
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    have hbx := scaledBox_cube z (fun x hx => (hB x).mp hx) hx
    have hbv := scaledBox_cube z (fun x hx => (hB x).mp hx) hv
    have hx' : x ∈ scaledBox z (D*s) ((D : ℤ)*(3*(R : ℤ))) := scaledBox_rescale z hbx
    have hv' : φ v ∈ scaledBox z (D*s) ((e*M : ℤ)*(3*(R : ℤ))) :=
      scaledBox_matrix z (fun i j => mat_bound (⟨φ,hφ⟩,i,j)) (mat_acts φ hφ v) hbv
    have h := mul_mem_scaledBox z hx' hv'
    have hcalc : (D : ℤ)*(3*(R : ℤ))+(e*M : ℤ)*(3*(R : ℤ)) = (P : ℤ)*R := by
      dsimp [P]
      ring
    rw [hcalc] at h
    exact h
  · intro x hx y hy hn h
    exact hsep x hx y hy hn ((hB (x*y⁻¹)).mpr h)

section FiniteRationalRank

variable {A : Type*} [CommGroup A] [IsMulTorsionFree A]
variable [Module.Finite ℚ (ℚ ⊗[ℤ] Additive A)]

private theorem exists_rational_packing_coordinates :
    let e := Module.finrank ℚ (ℚ ⊗[ℤ] Additive A)
    ∃ z : A →* Multiplicative (Fin e → ℚ), Function.Injective z ∧
      ∃ L : (A ≃* A) → (Fin e → ℚ) →ₗ[ℚ] (Fin e → ℚ),
        ∀ φ g, Multiplicative.toAdd (z (φ g)) = L φ (Multiplicative.toAdd (z g)) := by
  let V := ℚ ⊗[ℤ] Additive A
  let e := Module.finrank ℚ V
  let b := (Module.finBasis ℚ V).equivFun
  let t := TensorProduct.mk ℤ ℚ (Additive A) 1
  have ht : Function.Injective t := by
    apply (LinearMap.ker_eq_bot).mp
    rw [eq_bot_iff]
    intro x hx
    change (1 : ℚ) ⊗ₜ[ℤ] x = 0 at hx
    obtain ⟨n,hn,hx'⟩ := (rationalization_eq_zero_iff x).mp hx
    exact (nsmul_right_inj (Nat.ne_of_gt hn)).mp (hx'.trans (nsmul_zero n).symm)
  let q := (b.toLinearMap.restrictScalars ℤ).comp t
  let z : A →* Multiplicative (Fin e → ℚ) := q.toAddMonoidHom.toMultiplicative
  have hz : Function.Injective z := b.injective.comp ht
  let F (φ : A ≃* A) := (φ.toMonoidHom.toAdditive.toIntLinearMap).baseChange ℚ
  let L (φ : A ≃* A) : (Fin e → ℚ) →ₗ[ℚ] (Fin e → ℚ) :=
    b.toLinearMap.comp ((F φ).comp b.symm.toLinearMap)
  refine ⟨z,hz,L,?_⟩
  intro φ g
  change b (t (Additive.ofMul (φ g))) = b (F φ (b.symm (b (t (Additive.ofMul g)))))
  rw [b.symm_apply_apply]
  apply congrArg b
  exact ((φ.toMonoidHom.toAdditive.toIntLinearMap).baseChange_tmul _ _).symm

/-- The torsion-free finite-rational-rank case of the CJMST automorphism packing
lemma. The finite neighborhood is the inverse image of a box in scaled lattice
coordinates, with separate residue and distance tests for packing. -/
theorem hasAutomorphismPacking_of_finite_rationalization (Φ : Finset (A ≃* A)) :
    ∃ k, HasAutomorphismPacking A Φ k := by
  obtain ⟨z,hz,L,hL⟩ := exists_rational_packing_coordinates (A := A)
  exact hasAutomorphismPacking_of_rational_coordinates z hz Φ L fun φ _ x => hL φ x

/-- The identity-automorphism case has a bound depending only on the rational rank. -/
theorem hasAutomorphismPacking_identity_of_finite_rationalization :
    HasAutomorphismPacking A {MulEquiv.refl A} (13^Module.finrank ℚ (ℚ ⊗[ℤ] Additive A)) := by
  classical
  obtain ⟨z,hz,_,_⟩ := exists_rational_packing_coordinates (A := A)
  intro K
  obtain ⟨s,hs,R,hKR⟩ := exists_scaledBox_contains z K
  let hf := finite_scaledBox z hz hs (R : ℤ)
  let B := hf.toFinset
  have hB (x : A) : x ∈ B ↔ x ∈ scaledBox z s R := hf.mem_toFinset
  refine ⟨B,fun x hx => (hB x).mpr (hKR hx),
    (hB 1).mpr (one_mem_scaledBox z s (Int.natCast_nonneg R)),
    fun x hx => (hB x⁻¹).mpr (inv_mem_scaledBox z ((hB x).mp hx)),?_⟩
  intro φ hφ T hT hsep
  have same := Finset.mem_singleton.mp hφ
  subst φ
  have bound (x : A) (hx : x ∈ T) : x ∈ scaledBox z (1*s) ((6 : ℤ)*R) := by
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_mul.mp (hT hx)
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    have ha' := scaledBox_cube z (fun x hx => (hB x).mp hx) ha
    have hc' := scaledBox_cube z (fun x hx => (hB x).mp hx) hc
    have h := mul_mem_scaledBox z ha' hc'
    simpa only [MulEquiv.refl_apply,one_mul,show 3*(R : ℤ)+3*R = 6*R from by omega] using h
  exact card_le_scaledBoxSeparated z (Nat.succ_pos 0) T bound
    (fun x hx y hy hne hm => hsep x hx y hy hne ((hB _).mpr hm))

end FiniteRationalRank
end LinearActions

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.RationalAutomorphismPacking

-- BEGIN COMPLETE MODULE HirschProof.ClopenNormalSeries
section
                                         
                                              

set_option autoImplicit false
noncomputable section

open Set Topology TopologicalSpace
open scoped Pointwise

namespace LocalHirschHyperfinite

section ClopenSeries

attribute [local instance] Classical.decEq

variable {H X : Type*} [Group H] [TopologicalSpace X] [MulAction H X]

private theorem product_color_equiv (d k : ℕ) :
    Nonempty (Fin (((d+1)*(k+1)-1)+1) ≃ Fin (d+1) × Fin (k+1)) := by
  have h : 0 < (d+1)*(k+1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  exact ⟨(finCongr (Nat.sub_add_cancel (by omega : 1 ≤ (d+1)*(k+1)))).trans finProdFinEquiv.symm⟩

private theorem subgroup_dimension_step {F G : Subgroup H} [F.Normal]
    (hFG : F ≤ G)
    (hact : ∀ g : H, Continuous (fun x : X => g • x))
    (hfree : ∀ g : H, ∀ x : X, g • x = x → g = 1)
    {d k : ℕ} (hd : HasClopenSubgroupDimension F d X)
    (hpal : HasClopenQuotientPalettes (QuotientGroup.mk' F) X)
    (hpack : HasRelativePacking F G {1} k) :
    HasClopenSubgroupDimension G ((d+1)*(k+1)-1) X := by
  classical
  intro K hKG _
  let q := QuotientGroup.mk' F
  have hq : q.ker = F := QuotientGroup.ker_mk' F
  have h1 : (1 : H) ∈ ({1} : Finset H) := Finset.mem_singleton_self _
  have hsym : SymmetricMoves ({1} : Finset H) := by
    intro g hg
    rw [Finset.mem_singleton.mp hg,inv_one]
    exact h1
  obtain ⟨R⟩ := exists_clopenRelativeCover q G (hq.symm ▸ hFG) hact hfree
    (hq.symm ▸ hd) hpal {1} h1 hsym K hKG (hq.symm ▸ hpack)
  let e := (product_color_equiv d k).some
  refine ⟨fun j => R.sites (e j),fun j => R.clopen (e j),?_,?_⟩
  · intro x
    obtain ⟨p,hp⟩ := R.covers x
    exact ⟨e.symm p,by simpa using hp⟩
  · obtain ⟨D,hD,hDb⟩ := R.bound
    exact ⟨D,hD,fun j => hDb (e j)⟩

private def symmetricHull (C : Finset H) : Finset H := insert 1 (C ∪ C⁻¹)

private theorem one_mem_symmetricHull (C : Finset H) : 1 ∈ symmetricHull C :=
  Finset.mem_insert_self _ _

private theorem subset_symmetricHull (C : Finset H) : C ⊆ symmetricHull C :=
  fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)

private theorem symmetricHull_symm (C : Finset H) : SymmetricMoves (symmetricHull C) := by
  intro g hg
  rcases Finset.mem_insert.mp hg with rfl|hg
  · simpa only [inv_one] using one_mem_symmetricHull C
  · rcases Finset.mem_union.mp hg with hg|hg
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_inv.mpr ⟨g,hg,rfl⟩))
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_inv.mp hg
      simpa only [inv_inv] using subset_symmetricHull C ha

private theorem subgroup_palettes_step {F G : Subgroup H} [F.Normal] [G.Normal]
    (hFG : F ≤ G)
    (hact : ∀ g : H, Continuous (fun x : X => g • x))
    (hfree : ∀ g : H, ∀ x : X, g • x = x → g = 1)
    {d : ℕ} (hd : HasClopenSubgroupDimension F d X)
    (hpal : HasClopenQuotientPalettes (QuotientGroup.mk' F) X)
    (hpack : ∀ C : Finset H, ∃ k, HasRelativePacking F G C k) :
    HasClopenQuotientPalettes (QuotientGroup.mk' G) X := by
  classical
  intro C
  let C' := symmetricHull C
  obtain ⟨k,hPack⟩ := hpack C'
  let q := QuotientGroup.mk' F
  let r := QuotientGroup.mk' G
  have hq : q.ker = F := QuotientGroup.ker_mk' F
  have hr : r.ker = G := QuotientGroup.ker_mk' G
  refine ⟨(d+1)*(k+1),?_⟩
  intro E hE
  let K := (C'⁻¹*E).filter (fun g => g ∈ G)
  have hKG (g : H) (hg : g ∈ K) : g ∈ G := (Finset.mem_filter.mp hg).2
  have hEK : E ⊆ C'*K := by
    intro g hg
    obtain ⟨c,hc,he⟩ := hE g hg
    have hc' := subset_symmetricHull C hc
    have hk : c⁻¹*g ∈ K := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_mul.mpr ⟨c⁻¹,Finset.mem_inv.mpr ⟨c,hc',rfl⟩,
        g,hg,rfl⟩,?_⟩
      rw [← hr]
      change r (c⁻¹*g) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    exact Finset.mem_mul.mpr ⟨c,hc',c⁻¹*g,hk,mul_inv_cancel_left _ _⟩
  obtain ⟨R⟩ := exists_clopenRelativeCover q G (hq.symm ▸ hFG) hact hfree
    (hq.symm ▸ hd) hpal C' (one_mem_symmetricHull _) (symmetricHull_symm _) K hKG (hq.symm ▸ hPack)
  let e : Fin ((d+1)*(k+1)) ≃ Fin (d+1) × Fin (k+1) := finProdFinEquiv.symm
  refine ⟨fun j => R.sites (e j),fun j => R.clopen (e j),?_,?_⟩
  · intro x
    obtain ⟨p,hp⟩ := R.covers x
    exact ⟨e.symm p,by simpa using hp⟩
  · intro j x hx g hg hgq
    have hne : g ∉ G := fun h => hgq (show g ∈ r.ker from hr.symm ▸ h)
    exact R.independent (e j) x hx g (hEK hg) hne

private theorem subgroup_dimension_bot : HasClopenSubgroupDimension (⊥ : Subgroup H) 0 X := by
  intro K hK _
  refine ⟨fun _ => univ,fun _ => isClopen_univ,fun _ => ⟨0,Set.mem_univ _⟩,
    {1},fun g hg => by simpa using hg,?_⟩
  intro i x y h
  refine ⟨1,Finset.mem_singleton_self _,?_⟩
  have he : x = y := by
    have aux {y : X} (p : Relation.ReflTransGen (TestEdge K univ) x y) : x = y := by
      induction p with
      | refl => rfl
      | tail _ e ih =>
        obtain ⟨g,hg,hxy⟩ := e.2.2
        rw [Subgroup.mem_bot.mp (hK _ hg),one_smul] at hxy
        exact ih.trans hxy
    exact aux h.2
  simpa using he

variable [T2Space X] [CompactSpace X]

private theorem subgroup_palettes_of_injective {P : Type*} [Group P]
    (q : H →* P) (hq : Function.Injective q)
    (hact : ∀ g : H, Continuous (fun x : X => g • x))
    (hfree : ∀ g : H, ∀ x : X, g • x = x → g = 1)
    (hbasis : IsTopologicalBasis {U : Set X | IsClopen U}) :
    HasClopenQuotientPalettes q X := by
  classical
  intro C
  obtain ⟨l,W,hW,hWcov,hsep⟩ := exists_clopen_move_separation hact hfree hbasis C
  refine ⟨l,fun E hE => ⟨W,hW,hWcov,?_⟩⟩
  intro i x hx g hg hn
  obtain ⟨c,hc,he⟩ := hE g hg
  have he' := hq he
  exact hsep i x hx g (he' ▸ hc) (fun h => hn (h.symm ▸ map_one q))

end ClopenSeries

universe u

/-- A finite normal series whose relative packing bounds are available in the ambient
group. The distinguished one-element test controls the uniform dimension bound. -/
structure NormalPackingSeries (H : Type u) [Group H] where
  length : ℕ
  layer : ℕ → Subgroup H
  normal : ∀ n, (layer n).Normal
  mono : Monotone layer
  bottom : layer 0 = ⊥
  top : layer length = ⊤
  stepBound : ℕ → ℕ
  packing : ∀ n < length, ∀ C : Finset H, ∃ k, HasRelativePacking (layer n) (layer (n+1)) C k
  packing_one : ∀ n < length, HasRelativePacking (layer n) (layer (n+1)) {1} (stepBound n)

def NormalPackingSeries.dimAt {H : Type u} [Group H] (S : NormalPackingSeries H) : ℕ → ℕ
  | 0 => 0
  | n+1 => (S.dimAt n + 1)*(S.stepBound n+1)-1

/-- The compact free-action dimension bound obtained by iterating relative
clopen coloring along a finite normal series. -/
theorem compactClopenDADLE_of_normalPackingSeries {H : Type u} [Group H]
    (S : NormalPackingSeries H) : CompactClopenDADLE H (S.dimAt S.length) := by
  classical
  intro X _ _ _ _ hbasis hact hfree K hK
  letI (n : ℕ) : (S.layer n).Normal := S.normal n
  have level (n : ℕ) (hn : n ≤ S.length) :
      HasClopenSubgroupDimension (S.layer n) (S.dimAt n) X ∧
        HasClopenQuotientPalettes (QuotientGroup.mk' (S.layer n)) X := by
    induction n with
    | zero =>
      have h : S.layer 0 = ⊥ := S.bottom
      have hd : HasClopenSubgroupDimension (S.layer 0) 0 X := h.symm ▸ subgroup_dimension_bot
      have hp : HasClopenQuotientPalettes (QuotientGroup.mk' (S.layer 0)) X := by
        let q := QuotientGroup.mk' (S.layer 0)
        have hq : Function.Injective q := q.ker_eq_bot_iff.mp ((QuotientGroup.ker_mk' _).trans h)
        exact subgroup_palettes_of_injective q hq hact hfree hbasis
      exact ⟨hd,hp⟩
    | succ n ih =>
      obtain ⟨hd,hp⟩ := ih (Nat.le_of_succ_le hn)
      have hFG : S.layer n ≤ S.layer (n+1) := S.mono (Nat.le_succ n)
      exact ⟨subgroup_dimension_step hFG hact hfree hd hp (S.packing_one n hn),
        subgroup_palettes_step hFG hact hfree hd hp (S.packing n hn)⟩
  obtain ⟨U,hU,hUcov,D,_,hD⟩ := (level S.length le_rfl).1 K
    (fun g _ => S.top.symm ▸ Subgroup.mem_top g) hK
  exact ⟨U,hU,hUcov,D.card,fun i x => ⟨D.image (fun g => g • x),Finset.card_image_le,
    fun y hy => by obtain ⟨g,hg,he⟩ := hD i x y hy; exact Finset.mem_image.mpr ⟨g,hg,he⟩⟩⟩


section PackedFactors

attribute [local instance] Classical.decEq

/-- A factor has packing for arbitrary finite automorphism families, with a
specified uniform rank bound for the identity family. -/
structure PackedFactor (G : Type*) [Group G] (rankBound : ℕ) : Prop where
  arbitrary : ∀ Φ : Finset (G ≃* G), ∃ k, HasAutomorphismPacking G Φ k
  identity : HasAutomorphismPacking G {MulEquiv.refl G} (13^rankBound)

theorem packedFactor_of_finiteCharacteristic {G : Type*} [Group G] {rankBound : ℕ}
    (h : ∀ K : Finset G, ∃ L : Subgroup G, L.Characteristic ∧ Finite L ∧
      ∀ g ∈ K, g ∈ L) : PackedFactor G rankBound := by
  refine ⟨fun Φ => ⟨1,hasAutomorphismPacking_of_finiteCharacteristic h Φ⟩,?_⟩
  exact (hasAutomorphismPacking_of_finiteCharacteristic h _).mono
    (Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 13)))

theorem packedFactor_of_finite {G : Type*} [Group G] [Finite G] (rankBound : ℕ) :
    PackedFactor G rankBound :=
  packedFactor_of_finiteCharacteristic (fun _ => ⟨⊤,inferInstance,inferInstance,fun g _ => Subgroup.mem_top g⟩)

open TensorProduct in
theorem packedFactor_of_torsionFree_rationalRank {A : Type*} [CommGroup A] [IsMulTorsionFree A]
    [Module.Finite ℚ (ℚ ⊗[ℤ] Additive A)] {rankBound : ℕ}
    (h : Module.finrank ℚ (ℚ ⊗[ℤ] Additive A) ≤ rankBound) : PackedFactor A rankBound :=
  ⟨hasAutomorphismPacking_of_finite_rationalization,
    hasAutomorphismPacking_identity_of_finite_rationalization.mono
      (Nat.pow_le_pow_right (by decide : 0 < 13) h)⟩

theorem PackedFactor.of_equiv {G J : Type*} [Group G] [Group J]
    {rankBound : ℕ} (h : PackedFactor G rankBound) (e : G ≃* J) :
    PackedFactor J rankBound := by
  constructor
  · intro Φ
    obtain ⟨k,hk⟩ := h.arbitrary (Φ.image (transportAutomorphism e))
    exact ⟨k,hasAutomorphismPacking_of_equiv e Φ hk⟩
  · apply hasAutomorphismPacking_of_equiv e
    simpa only [Finset.image_singleton,transportAutomorphism_refl] using h.identity

private theorem imageConjugation_one {G P : Type*} [Group G] [Group P]
    (q : G →* P) (L : Subgroup G) (hL : L.Normal) :
    imageConjugation q L hL 1 = MulEquiv.refl (L.map q) := by
  ext x
  change q 1 * x.val * (q 1)⁻¹ = _
  simp

/-- Assemble relative packing bounds through the ambient quotients of a normal series. -/
def NormalPackingSeries.of_packed_factors {H : Type u} [Group H] (length rankBound : ℕ)
    (layer : ℕ → Subgroup H) (normal : ∀ n, (layer n).Normal)
    (mono : Monotone layer) (bottom : layer 0 = ⊥) (top : layer length = ⊤)
    (factors : ∀ n < length,
      letI := normal n
      PackedFactor ((layer (n+1)).map (QuotientGroup.mk' (layer n))) rankBound) :
    NormalPackingSeries H where
  length := length
  layer := layer
  normal := normal
  mono := mono
  bottom := bottom
  top := top
  stepBound := fun _ => 13^rankBound
  packing := by
    intro n hn C
    letI := normal n
    let q := QuotientGroup.mk' (layer n)
    let G := layer (n+1)
    have hG := normal (n+1)
    have hq : q.ker = layer n := QuotientGroup.ker_mk' _
    obtain ⟨k,hk⟩ := (factors n hn).arbitrary (C.image (imageConjugation q G hG))
    exact ⟨C.card*k,hq ▸ hasRelativePacking_of_automorphisms q G hG C hk⟩
  packing_one := by
    intro n hn
    letI := normal n
    let q := QuotientGroup.mk' (layer n)
    let G := layer (n+1)
    have hG := normal (n+1)
    have hq : q.ker = layer n := QuotientGroup.ker_mk' _
    have hEq : ({1} : Finset H).image (imageConjugation q G hG) =
        {MulEquiv.refl (G.map q)} := by
      rw [Finset.image_singleton,imageConjugation_one]
    have hp := hasRelativePacking_of_automorphisms q G hG {1} (hEq.symm ▸ (factors n hn).identity)
    simpa only [Finset.card_singleton,one_mul,hq] using hp

/-- Enlarging the number of clopen colors preserves a dynamic dimension bound. -/
theorem CompactClopenDADLE.mono {G : Type u} [Group G] {d d' : ℕ}
    (h : CompactClopenDADLE G d) (hd : d ≤ d') : CompactClopenDADLE G d' := by
  classical
  intro X _ _ _ _ hbasis hact hfree K hK
  obtain ⟨U,hU,hCover,N,hN⟩ := h X hbasis hact hfree K hK
  let V (i : Fin (d'+1)) := if hi : i.val < d+1 then U ⟨i.val,hi⟩ else ∅
  refine ⟨V,?_,?_,N,?_⟩
  · intro i
    dsimp [V]
    split
    · exact hU _
    · exact isClopen_empty
  · intro x
    obtain ⟨i,hi⟩ := hCover x
    let j := Fin.castLE (Nat.succ_le_succ hd) i
    refine ⟨j,?_⟩
    have hj : j.val < d+1 := i.isLt
    change x ∈ (if ht : j.val < d+1 then U ⟨j.val,ht⟩ else ∅)
    rw [dif_pos hj]
    exact hi
  · intro i x
    dsimp [V]
    split
    · exact hN _ x
    · exact ⟨∅,by simp,fun _ h => h.1.elim⟩

/-- The rank and length of the series give a common upper bound for all such
compact free actions. -/
theorem compactClopenDADLE_of_packed_factors {H : Type u} [Group H] (length rankBound : ℕ)
    (layer : ℕ → Subgroup H) (normal : ∀ n, (layer n).Normal)
    (mono : Monotone layer) (bottom : layer 0 = ⊥) (top : layer length = ⊤)
    (factors : ∀ n < length,
      letI := normal n
      PackedFactor ((layer (n+1)).map (QuotientGroup.mk' (layer n))) rankBound) :
    CompactClopenDADLE H ((13^rankBound+1)^length-1) := by
  let S := NormalPackingSeries.of_packed_factors length rankBound layer normal mono bottom top factors
  have hdim (n : ℕ) : S.dimAt n + 1 = (13^rankBound+1)^n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (S.dimAt n+1)*(13^rankBound+1)-1+1 = (13^rankBound+1)^(n+1)
      rw [ih,pow_succ,Nat.sub_add_cancel]
      exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) (Nat.succ_pos _))
  have he : S.dimAt length = (13^rankBound+1)^length-1 := by have := hdim length; omega
  have h : CompactClopenDADLE H (S.dimAt length) := compactClopenDADLE_of_normalPackingSeries S
  rwa [he] at h

end PackedFactors

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.ClopenNormalSeries

-- BEGIN COMPLETE MODULE HirschProof.GeneratorRank
section
                                       

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

/-- A bound on the number of generators needed for every finitely generated
subgroup (the Prüfer rank). -/
def GeneratorRankLE (G : Type*) [Group G] (d : ℕ) : Prop :=
  ∀ H : Subgroup G, H.FG → ∃ T : Finset G, Subgroup.closure (T : Set G) = H ∧ T.card ≤ d

namespace GeneratorRankLE

variable {G A : Type*} [Group G] [Group A] {d e : ℕ}

private theorem fg_closure_finset (S : Finset G) : (Subgroup.closure (S : Set G)).FG :=
  (Subgroup.fg_iff _).mpr ⟨S,rfl,S.finite_toSet⟩

private theorem exists_lift_finset (f : G →* A) (H : Subgroup G) (S : Finset A)
    (hS : (S : Set A) ⊆ H.map f) :
    ∃ T : Finset G, (T : Set G) ⊆ H ∧ f '' (T : Set G) = S ∧ T.card ≤ S.card := by
  classical
  have h (a : (S : Set A)) : ∃ x ∈ H, f x = a := hS a.property
  choose j hj hq using h
  let T := S.attach.image j
  refine ⟨T,?_,?_,(Finset.card_image_le (s := S.attach)).trans_eq Finset.card_attach⟩
  · intro x hx
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    exact hj a
  · ext a
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hx
      rw [hq]
      exact b.property
    · intro ha
      let b : (S : Set A) := ⟨a,ha⟩
      exact ⟨j b,Finset.mem_image.mpr ⟨b,Finset.mem_attach _ b,rfl⟩,hq b⟩

theorem of_injective (f : G →* A) (hf : Function.Injective f) (h : GeneratorRankLE A d) :
    GeneratorRankLE G d := by
  intro H hH
  obtain ⟨S,hS,hs⟩ := h _ (IsLocallyFiniteGroup.fg_map f H hH)
  obtain ⟨T,_,hT,ht⟩ := exists_lift_finset f H S (hS ▸ Subgroup.subset_closure)
  refine ⟨T,?_,ht.trans hs⟩
  apply Subgroup.map_injective hf
  rw [f.map_closure,hT,hS]

theorem subgroup (h : GeneratorRankLE G d) (H : Subgroup G) : GeneratorRankLE H d :=
  of_injective H.subtype H.subtype_injective h

theorem of_surjective (f : G →* A) (hf : Function.Surjective f) (h : GeneratorRankLE G d) :
    GeneratorRankLE A d := by
  classical
  intro H hH
  have hle : H ≤ (⊤ : Subgroup G).map f := by rw [Subgroup.map_top_of_surjective f hf]; exact le_top
  obtain ⟨J,_,hJ,hJq⟩ := exists_fg_subgroup_map_eq f ⊤ H hle hH
  obtain ⟨T,hT,ht⟩ := h J hJ
  refine ⟨T.image f,?_,Finset.card_image_le.trans ht⟩
  rw [Finset.coe_image,← f.map_closure,hT,hJq]

/-- A bound on subgroup generator numbers is subadditive under extensions.
Only finitely many kernel corrections to the given generators are needed. -/
theorem extension (f : G →* A) (hk : GeneratorRankLE f.ker d) (hq : GeneratorRankLE A e) :
    GeneratorRankLE G (d+e) := by
  classical
  intro H hH
  obtain ⟨S,hS,hSc⟩ := hq _ (IsLocallyFiniteGroup.fg_map f H hH)
  obtain ⟨T,hT,hTq,hTc⟩ := exists_lift_finset f H S (hS ▸ Subgroup.subset_closure)
  let J := Subgroup.closure (T : Set G)
  have hJ : J ≤ H := (Subgroup.closure_le _).mpr hT
  have hJq : J.map f = H.map f := by
    change (Subgroup.closure (T : Set G)).map f = _
    rw [f.map_closure,hTq,hS]
  obtain ⟨R,hR,hRf⟩ := (Subgroup.fg_iff H).mp hH
  have hR' (x : R) : x.val ∈ H := hR ▸ Subgroup.subset_closure x.property
  have hLift (x : R) : ∃ y ∈ J, f y = f x.val := by
    change f x.val ∈ J.map f
    rw [hJq]
    exact ⟨x.val,hR' x,rfl⟩
  choose j hj hqj using hLift
  let c (x : R) : f.ker := ⟨(j x)⁻¹*x.val,by
    change f ((j x)⁻¹*x.val) = 1
    rw [map_mul,map_inv,hqj,inv_mul_cancel]⟩
  let D := Subgroup.closure (range c)
  have hDf : D.FG := by
    letI := hRf.to_subtype
    exact (Subgroup.fg_iff _).mpr ⟨_,rfl,finite_range c⟩
  have hDH : D ≤ H.comap f.ker.subtype := (Subgroup.closure_le _).mpr (by
    rintro _ ⟨x,rfl⟩
    exact H.mul_mem (H.inv_mem (hJ (hj x))) (hR' x))
  obtain ⟨V,hV,hVc⟩ := hk D hDf
  let U := T ∪ V.image f.ker.subtype
  let L := Subgroup.closure (U : Set G)
  have hTL : J ≤ L := Subgroup.closure_mono (by
    intro x hx; exact Finset.mem_union_left _ hx)
  have hVL : D.map f.ker.subtype ≤ L := by
    rw [← hV,f.ker.subtype.map_closure]
    exact Subgroup.closure_mono (by
      rintro _ ⟨v,hv,rfl⟩
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv))
  refine ⟨U,le_antisymm ?_ ?_,?_⟩
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hT hx
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
      exact hDH (hV ▸ Subgroup.subset_closure hv)
  · rw [← hR]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    let a : R := ⟨x,hx⟩
    have ha : (c a).val ∈ L := hVL ⟨c a,Subgroup.subset_closure ⟨a,rfl⟩,rfl⟩
    have hmem := L.mul_mem (hTL (hj a)) ha
    change j a*((j a)⁻¹*x) ∈ L at hmem
    simpa using hmem
  · exact (Finset.card_union_le _ _).trans
      ((Nat.add_le_add (hTc.trans hSc) (Finset.card_image_le.trans hVc)).trans_eq (Nat.add_comm e d))

end GeneratorRankLE

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.GeneratorRank

-- BEGIN COMPLETE MODULE HirschProof.ConjugateGrowth
section
                                 
                                       
                                      
                                                      

set_option autoImplicit false

open scoped Pointwise

namespace LocalHirschHyperfinite

variable {G Q : Type*} [Group G] [Group Q]

/-- A word ball has at most as many elements as bounded words in the alphabet. -/
theorem card_wordBall_le (S : Finset G) (r : ℕ) :
    (wordBall S r).card ≤ (S.card + 1)^r := by
  classical
  induction r with
  | zero => simp [wordBall]
  | succ r ih =>
    calc
      (wordBall S (r+1)).card ≤ (wordBall S r).card + (wordBall S r * S).card :=
        Finset.card_union_le _ _
      _ ≤ (wordBall S r).card + (wordBall S r).card * S.card :=
        Nat.add_le_add_left Finset.card_mul_le _
      _ = (wordBall S r).card * (S.card + 1) := by ring
      _ ≤ (S.card + 1)^r * (S.card + 1) := Nat.mul_le_mul_right _ ih
      _ = (S.card + 1)^(r+1) := (pow_succ _ _).symm

/-- A finite abelian group generated by elements of exponent `e` has at most
`e` choices per generator. -/
theorem card_abelian_of_exponent_generators {A I : Type*} [CommGroup A] [Finite A]
    [Fintype I] (u : I → A) (hu : Subgroup.closure (Set.range u) = ⊤)
    (e : ℕ) (he : e ≠ 0) (hexp : ∀ i, u i ^ e = 1) : Nat.card A ≤ e^(Fintype.card I) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  let P (i : I) := Subgroup.zpowers (u i)
  let f : (∀ i, P i) →* A :=
    { toFun := fun z => ∏ i, (z i).val
      map_one' := by simp
      map_mul' := by intro x y; exact Finset.prod_mul_distrib }
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    change (⊤ : Subgroup A) ≤ f.range
    conv_lhs => rw [← hu]
    apply (Subgroup.closure_le _).2
    rintro _ ⟨i,rfl⟩
    let z : ∀ j, P j := Pi.mulSingle i ⟨u i,Subgroup.mem_zpowers (u i)⟩
    refine ⟨z,?_⟩
    show (∏ j, (z j).val) = u i
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [z,Pi.mulSingle_eq_of_ne hj]) (by simp)]
    simp [z]
  calc
    Nat.card A ≤ Nat.card (∀ i, P i) := Nat.card_le_card_of_surjective f hsurj
    _ = ∏ i, Nat.card (P i) := Nat.card_pi
    _ ≤ ∏ _i : I, e := Finset.prod_le_prod' (fun i _ => by
      rw [Nat.card_eq_fintype_card]
      exact card_zpowers_le (u i) he (hexp i))
    _ = e^(Fintype.card I) := by simp

/-- A subgroup generated by the indicated bounded conjugates of a finite seed list. -/
noncomputable def conjugateGroup (S U : Finset G) (r : ℕ) : Subgroup G :=
  Subgroup.closure (Set.range (fun a : (↑(wordBall S r) : Type _) × (↑U : Type _) =>
    a.1.val*a.2.val*a.1.val⁻¹))

theorem conjugateGroup_fg (S U : Finset G) (r : ℕ) : (conjugateGroup S U r).FG :=
  (Subgroup.fg_iff _).2 ⟨_,rfl,Set.finite_range _⟩

theorem conjugateGroup_le (S U : Finset G) (r : ℕ) (K : Subgroup G) [K.Normal]
    (hU : ∀ u ∈ U, u ∈ K) : conjugateGroup S U r ≤ K := by
  apply (Subgroup.closure_le _).2
  rintro _ ⟨a,rfl⟩
  exact ‹K.Normal›.conj_mem _ (hU _ a.2.property) _

theorem conj_mem_conjugateGroup (S U : Finset G) (r : ℕ) {w : G}
    (hw : w ∈ wordBall S r) {b : G} (hb : b ∈ Subgroup.closure (U : Set G)) :
    w*b*w⁻¹ ∈ conjugateGroup S U r := by
  let f := (MulAut.conj w).toMonoidHom
  have hmap : (Subgroup.closure (U : Set G)).map f ≤ conjugateGroup S U r := by
    rw [f.map_closure]
    apply (Subgroup.closure_le _).2
    rintro _ ⟨u,hu,rfl⟩
    exact Subgroup.subset_closure ⟨(⟨w,hw⟩,⟨u,hu⟩),rfl⟩
  exact hmap ⟨b,hb,rfl⟩

set_option maxHeartbeats 700000 in
/-- The abelian image of the generated conjugates grows at most with the number of words. -/
theorem card_image_conjugateGroup_le (S U : Finset G) (r e : ℕ) (he : e ≠ 0)
    (p : G →* Q) (K : Subgroup G) [K.Normal] (hU : ∀ u ∈ U, u ∈ K)
    [Finite (conjugateGroup S U r)] (hcomm : ∀ x ∈ K, ∀ y ∈ K, Commute (p x) (p y))
    (hexp : ∀ u ∈ U, (p u)^e = 1) :
    Nat.card ((conjugateGroup S U r).map p) ≤ e^(U.card*(S.card+1)^r) := by
  classical
  let D := conjugateGroup S U r
  let A := D.map p
  let f := p.subgroupMap D
  letI : Finite A := Finite.of_surjective f (p.subgroupMap_surjective D)
  have hD : D ≤ K := conjugateGroup_le S U r K hU
  letI : CommGroup A := { (inferInstance : Group A) with
    mul_comm := by
      rintro ⟨a,x,hx,rfl⟩ ⟨b,y,hy,rfl⟩
      exact Subtype.ext (hcomm x (hD hx) y (hD hy)).eq }
  let I := (↑(wordBall S r) : Type _) × (↑U : Type _)
  let g (i : I) : D := ⟨i.1.val*i.2.val*i.1.val⁻¹,Subgroup.subset_closure ⟨i,rfl⟩⟩
  let u := f ∘ g
  have hgen : Subgroup.closure (Set.range u) = ⊤ := by
    apply (Subgroup.eq_top_iff' _).2
    intro a
    obtain ⟨x,rfl⟩ := p.subgroupMap_surjective D a
    let R := (Subgroup.closure (Set.range u)).comap f
    have hR : D ≤ R.map D.subtype := by
      apply (Subgroup.closure_le _).2
      rintro _ ⟨i,rfl⟩
      exact ⟨g i,Subgroup.subset_closure ⟨i,rfl⟩,rfl⟩
    obtain ⟨y,hy,heq⟩ := hR x.property
    exact (Subtype.ext heq : y = x) ▸ hy
  have hp (i : I) : u i ^ e = 1 := by
    apply Subtype.ext
    change (p (i.1.val*i.2.val*i.1.val⁻¹))^e = 1
    simp only [map_mul,map_inv,conj_pow,hexp _ i.2.property,mul_one,mul_inv_cancel]
  refine (card_abelian_of_exponent_generators u hgen e he hp).trans ?_
  apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero he)
  simp only [I,Fintype.card_prod,Fintype.card_coe]
  rw [mul_comm (wordBall S r).card U.card]
  exact Nat.mul_le_mul_left _ (card_wordBall_le S r)

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.ConjugateGrowth

-- BEGIN COMPLETE MODULE HirschProof.AbelianRankFactors
section
                                
                                  
                                       
                                  

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set TensorProduct

variable {A : Type*} [CommGroup A] {d : ℕ}

/-- An abelian group of bounded exponent and Prüfer rank is finite. -/
theorem finite_of_generatorRankLE_of_exponent (h : GeneratorRankLE A d) {k : ℕ}
    (hk : 0 < k) (hA : ∀ a : A, a^k=1) : Finite A := by
  classical
  by_contra hfin
  letI : Infinite A := not_finite_iff_infinite.mp hfin
  obtain ⟨S,hS⟩ := Infinite.exists_subset_card_eq A (k^d+1)
  let H := Subgroup.closure (S : Set A)
  have hH : H.FG := (Subgroup.fg_iff H).mpr ⟨S,rfl,S.finite_toSet⟩
  letI : Group.FG H := (Group.fg_iff_subgroup_fg H).2 hH
  have hHex (x : H) : x^k=1 := Subtype.ext (hA x.val)
  letI : Finite H := CommGroup.finite_of_fg_torsion H (fun x =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨k,hk,hHex x⟩)
  obtain ⟨T,hT,hTc⟩ := h H hH
  let u (x : (↑T : Type _)) : H := ⟨x.val,hT ▸ Subgroup.subset_closure x.property⟩
  have hu : Subgroup.closure (range u) = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    have he : H.subtype '' range u = T := by
      ext a
      constructor
      · rintro ⟨_,⟨x,rfl⟩,rfl⟩
        exact x.property
      · intro ha
        exact ⟨u ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,rfl⟩
    rw [H.subtype.map_closure,he,hT,← MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hCard : Nat.card H ≤ k^d := by
    apply (card_abelian_of_exponent_generators u hu k hk.ne' (fun x => hHex (u x))).trans
    rw [Fintype.card_coe]
    exact Nat.pow_le_pow_right hk hTc
  let i (x : (↑S : Type _)) : H := ⟨x.val,Subgroup.subset_closure x.property⟩
  have hic : S.card ≤ Nat.card H := by
    have hi : Function.Injective i := fun _ _ e => Subtype.ext (congrArg (fun y : H => y.val) e)
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective i hi
  omega

/-- An abelian torsion group of finite Prüfer rank is the increasing union
of the characteristic finite subgroups killed by factorial exponents. -/
theorem torsion_exists_finite_characteristic_exhaustion (h : GeneratorRankLE A d)
    (ht : Monoid.IsTorsion A) :
    ∃ T : ℕ → Subgroup A, Monotone T ∧ (∀ i, (T i).Characteristic ∧ Finite (T i)) ∧
      ∀ a : A, ∃ i, a ∈ T i := by
  let T (i : ℕ) : Subgroup A := (powMonoidHom (α := A) i.factorial).ker
  refine ⟨T,?_,?_,?_⟩
  · intro i j hij a ha
    change a^i.factorial = 1 at ha
    change a^j.factorial = 1
    obtain ⟨m,hm⟩ := Nat.factorial_dvd_factorial hij
    rw [hm,pow_mul,ha,one_pow]
  · intro i
    refine ⟨Subgroup.characteristic_iff_comap_le.mpr ?_,?_⟩
    · intro f a ha
      change f a ^ i.factorial = 1 at ha
      change a ^ i.factorial = 1
      apply f.injective
      rwa [map_one,map_pow]
    · exact finite_of_generatorRankLE_of_exponent (h.subgroup (T i)) (Nat.factorial_pos i)
        (fun a => Subtype.ext a.property)
  · intro a
    obtain ⟨n,hn,he⟩ := (ht a).exists_pow_eq_one
    refine ⟨n,?_⟩
    change a^n.factorial = 1
    obtain ⟨m,hm⟩ := Nat.dvd_factorial hn le_rfl
    rw [hm,pow_mul,he,one_pow]

/-- For the abelian factors in a finite-rank solvable group, the torsion part
is a union of finite characteristic subgroups. The torsion-free quotient has
finite rational rank whenever the ambient abelian factor does. -/
theorem abelian_torsion_and_torsionFree_factors (h : GeneratorRankLE A d)
    [Module.Finite ℚ (ℚ ⊗[ℤ] Additive A)] :
    (∃ T : ℕ → Subgroup (CommGroup.torsion A), Monotone T ∧
      (∀ i, (T i).Characteristic ∧ Finite (T i)) ∧ ∀ a, ∃ i, a ∈ T i) ∧
    IsMulTorsionFree (A ⧸ CommGroup.torsion A) ∧
    Module.Finite ℚ (ℚ ⊗[ℤ] Additive (A ⧸ CommGroup.torsion A)) := by
  let V := CommGroup.torsion A
  have ht : Monoid.IsTorsion V := by
    intro a
    obtain ⟨n,hn,he⟩ := a.property.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,Subtype.ext he⟩
  exact ⟨torsion_exists_finite_characteristic_exhaustion (h.subgroup V) ht,inferInstance,
    finite_rationalization_of_surjective (QuotientGroup.mk' V).toAdditive.toIntLinearMap
      (QuotientGroup.mk'_surjective V)⟩

/-- The torsion and torsion-free layers of each abelian derived factor of a
solvable group of finite Prüfer rank and finite Hirsch length. -/
theorem derived_abelian_factors {G : Type*} [Group G] (h : GeneratorRankLE G d)
    (hh : IsSolvableFiniteHirsch G) (i : ℕ) :
    let A := Abelianization (derivedSeries G i)
    (∃ T : ℕ → Subgroup (CommGroup.torsion A), Monotone T ∧
      (∀ i, (T i).Characteristic ∧ Finite (T i)) ∧ ∀ a, ∃ i, a ∈ T i) ∧
    IsMulTorsionFree (A ⧸ CommGroup.torsion A) ∧
    Module.Finite ℚ (ℚ ⊗[ℤ] Additive (A ⧸ CommGroup.torsion A)) := by
  let D := derivedSeries G i
  letI : Module.Finite ℚ (RationalDerivedFactor G i) := hh.2 i
  exact abelian_torsion_and_torsionFree_factors
    ((h.subgroup D).of_surjective Abelianization.of (QuotientGroup.mk'_surjective (commutator D)))

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.AbelianRankFactors

-- BEGIN COMPLETE MODULE HirschProof.RationalRankBound
section
                                
                                                    

set_option autoImplicit false

namespace LocalHirschHyperfinite
open TensorProduct Set

/-- The rational rank of an abelian group is bounded by its Prüfer rank. -/
theorem rational_finrank_le_generatorRankLE {A : Type*} [CommGroup A] {d : ℕ}
    [Module.Finite ℚ (ℚ ⊗[ℤ] Additive A)] (h : GeneratorRankLE A d) :
    Module.finrank ℚ (ℚ ⊗[ℤ] Additive A) ≤ d := by
  classical
  let V := ℚ ⊗[ℤ] Additive A
  let t := TensorProduct.mk ℤ ℚ (Additive A) 1
  let u (a : A) : V := t (Additive.ofMul a)
  have htop : Submodule.span ℚ (range u) = ⊤ := by
    apply top_unique
    intro x _
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul q a =>
      change q ⊗ₜ[ℤ] a ∈ Submodule.span ℚ (range u)
      have he : q ⊗ₜ[ℤ] a = q • ((1 : ℚ) ⊗ₜ[ℤ] a) := by rw [smul_tmul',smul_eq_mul,mul_one]
      rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a.toMul,rfl⟩)
    | add a b ha hb => exact Submodule.add_mem _ (ha Submodule.mem_top) (hb Submodule.mem_top)
  have hW : (Submodule.span ℚ (range u)).FG := IsNoetherian.noetherian _
  obtain ⟨S,hS,hSW⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hW
  have hpre (s : (↑S : Type _)) : ∃ a : A, u a = s.val := hS s.property
  choose z hz using hpre
  let H := Subgroup.closure (range z)
  have hH : H.FG := (Subgroup.fg_iff _).mpr ⟨_,rfl,finite_range _⟩
  obtain ⟨T,hT,hTc⟩ := h H hH
  let U := T.image u
  let S' := Submodule.span ℚ (U : Set V)
  let M : Subgroup A := {
    carrier := {a | u a ∈ S'}
    one_mem' := by change t 0 ∈ S'; rw [map_zero]; exact S'.zero_mem
    mul_mem' := by
      intro a b ha hb
      change t (Additive.ofMul a + Additive.ofMul b) ∈ S'
      rw [map_add]
      exact S'.add_mem ha hb
    inv_mem' := by
      intro a ha
      change t (-Additive.ofMul a) ∈ S'
      rw [map_neg]
      exact S'.neg_mem ha }
  have hM : H ≤ M := by
    rw [← hT]
    apply (Subgroup.closure_le _).mpr
    intro a ha
    exact Submodule.subset_span (Finset.mem_image_of_mem _ ha)
  have hS' : S' = ⊤ := by
    rw [← htop, hSW]
    apply le_antisymm (hSW ▸ htop ▸ le_top)
    apply Submodule.span_le.mpr
    intro y hy
    let s : (↑S : Type _) := ⟨y,hy⟩
    have h : u (z s) ∈ S' := hM (Subgroup.subset_closure ⟨s,rfl⟩)
    exact (show u (z s) = y from hz s) ▸ h
  have hdim := finrank_span_finset_le_card (R := ℚ) U
  change Module.finrank ℚ S' ≤ U.card at hdim
  rw [hS',finrank_top] at hdim
  exact hdim.trans (Finset.card_image_le.trans hTc)

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.RationalRankBound

-- BEGIN COMPLETE MODULE HirschProof.DerivedFactorLayers
section
                                     
                                    
                                              

set_option autoImplicit false

noncomputable section

namespace LocalHirschHyperfinite

variable {G : Type*} [Group G]

private theorem abelianization_pow_eq_one_iff (i : ℕ) (x : derivedSeries G i) (m : ℕ) :
    Abelianization.of x ^ m = 1 ↔ x.val^m ∈ derivedSeries G (i+1) := by
  let D := derivedSeries G i
  calc
    _ ↔ x^m ∈ (Abelianization.of : D →* _).ker := by
      change _ ↔ Abelianization.of (x^m) = 1
      rw [map_pow]
    _ ↔ x^m ∈ commutator D := by rw [Abelianization.ker_of]
    _ ↔ x.val^m ∈ (commutator D).map D.subtype :=
      (Subgroup.mem_map_iff_mem (f := D.subtype) D.subtype_injective).symm
    _ ↔ _ := by rw [Subgroup.map_subtype_commutator,← derivedSeries_succ]

/-- Between two derived subgroups, insert the preimage of the torsion in
their abelian quotient. -/
def derivedTorsionLayer (G : Type*) [Group G] (i : ℕ) : Subgroup G :=
  let D := derivedSeries G i
  ((CommGroup.torsion (Abelianization D)).comap Abelianization.of).map D.subtype

theorem mem_derivedTorsionLayer (i : ℕ) (g : G) : g ∈ derivedTorsionLayer G i ↔
    g ∈ derivedSeries G i ∧ ∃ m : ℕ, 0 < m ∧ g^m ∈ derivedSeries G (i+1) := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    change IsOfFinOrder (Abelianization.of x) at hx
    obtain ⟨m,hm,hpow⟩ := hx.exists_pow_eq_one
    exact ⟨x.property,m,hm,(abelianization_pow_eq_one_iff i x m).mp hpow⟩
  · rintro ⟨hg,m,hm,hpow⟩
    refine ⟨⟨g,hg⟩,?_,rfl⟩
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,(abelianization_pow_eq_one_iff i ⟨g,hg⟩ m).mpr hpow⟩

instance derivedTorsionLayer_normal (i : ℕ) : (derivedTorsionLayer G i).Normal := by
  constructor
  intro x hx g
  obtain ⟨hx',m,hm,hpow⟩ := (mem_derivedTorsionLayer i x).mp hx
  have hg : g*x*g⁻¹ ∈ derivedSeries G i := (inferInstance : (derivedSeries G i).Normal).conj_mem x hx' g
  refine (mem_derivedTorsionLayer i _).mpr ⟨hg,m,hm,?_⟩
  have he : (g*x*g⁻¹)^m = g*x^m*g⁻¹ := (map_pow (MulAut.conj g) x m).symm
  rw [he]
  exact (inferInstance : (derivedSeries G (i+1)).Normal).conj_mem (x^m) hpow g

theorem derivedSeries_succ_le_derivedTorsionLayer (i : ℕ) :
    derivedSeries G (i+1) ≤ derivedTorsionLayer G i := fun g hg =>
  (mem_derivedTorsionLayer i g).mpr ⟨derivedSeries_antitone G (Nat.le_succ i) hg,1,Nat.one_pos,by simpa⟩

theorem derivedTorsionLayer_le_derivedSeries (i : ℕ) :
    derivedTorsionLayer G i ≤ derivedSeries G i := fun _ hg => ((mem_derivedTorsionLayer i _).mp hg).1

private theorem subgroup_factor_equiv_of_surjective {A : Type*} [Group A]
    (L U : Subgroup G) [L.Normal] (f : U →* A) (hf : Function.Surjective f)
    (hker : f.ker = L.subgroupOf U) : Nonempty (U.map (QuotientGroup.mk' L) ≃* A) := by
  let q := QuotientGroup.mk' L
  let g := q.comp U.subtype
  have h : g.ker = f.ker := by
    rw [hker]
    ext x
    change (QuotientGroup.mk x.val : G ⧸ L) = 1 ↔ x.val ∈ L
    exact QuotientGroup.eq_one_iff _
  have he : g.range = U.map q := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  have e : Nonempty (U.map q ≃* g.range) := he ▸ ⟨MulEquiv.refl _⟩
  obtain ⟨e⟩ := e
  exact ⟨e.trans ((QuotientGroup.quotientKerEquivRange g).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)))⟩

/-- The lower factor of a subdivided derived interval is its torsion subgroup. -/
theorem derivedTorsionLayer_lower_factor (i : ℕ) :
    Nonempty ((derivedTorsionLayer G i).map (QuotientGroup.mk' (derivedSeries G (i+1))) ≃*
      CommGroup.torsion (Abelianization (derivedSeries G i))) := by
  let D := derivedSeries G i
  let A := Abelianization D
  let T := CommGroup.torsion A
  let U := derivedTorsionLayer G i
  let d := Subgroup.inclusion (derivedTorsionLayer_le_derivedSeries (G := G) i)
  let q := (Abelianization.of : D →* A).comp d
  have hq (x : U) : q x ∈ T := by
    obtain ⟨_,m,hm,hpow⟩ := (mem_derivedTorsionLayer i x.val).mp x.property
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,(abelianization_pow_eq_one_iff i (d x) m).mpr hpow⟩
  let p := q.codRestrict T hq
  have hker : p.ker = (derivedSeries G (i+1)).subgroupOf U := by
    ext x
    change p x = 1 ↔ x.val ∈ derivedSeries G (i+1)
    rw [Subtype.ext_iff]
    change Abelianization.of (d x) = 1 ↔ _
    simpa only [pow_one] using abelianization_pow_eq_one_iff i (d x) 1
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (commutator D) x.val
    have hU : y.val ∈ U := by
      refine ⟨y,?_,rfl⟩
      change Abelianization.of y ∈ T
      exact (show Abelianization.of y = x.val from hy).symm ▸ x.property
    refine ⟨⟨y.val,hU⟩,Subtype.ext ?_⟩
    exact hy
  exact subgroup_factor_equiv_of_surjective _ _ p hp hker

/-- The upper factor of a subdivided derived interval is its torsion-free
abelian quotient. -/
theorem derivedTorsionLayer_upper_factor (i : ℕ) :
    Nonempty ((derivedSeries G i).map (QuotientGroup.mk' (derivedTorsionLayer G i)) ≃*
      (Abelianization (derivedSeries G i) ⧸ CommGroup.torsion (Abelianization (derivedSeries G i)))) := by
  let D := derivedSeries G i
  let A := Abelianization D
  let T := CommGroup.torsion A
  let U := derivedTorsionLayer G i
  let p := (QuotientGroup.mk' T).comp (Abelianization.of : D →* A)
  have hp : Function.Surjective p := (QuotientGroup.mk'_surjective T).comp
    (QuotientGroup.mk'_surjective (commutator D))
  have hker : p.ker = U.subgroupOf D := by
    ext x
    change (QuotientGroup.mk (Abelianization.of x) : A ⧸ T) = 1 ↔ x.val ∈ U
    rw [QuotientGroup.eq_one_iff]
    change Abelianization.of x ∈ T ↔ x.val ∈ ((T.comap Abelianization.of).map D.subtype)
    constructor
    · intro hx
      exact ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact (Subtype.ext he : y=x) ▸ hy
  exact subgroup_factor_equiv_of_surjective _ _ p hp hker

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.DerivedFactorLayers

-- BEGIN COMPLETE MODULE HirschProof.AlgebraicPackingSeries
section
                                      

set_option autoImplicit false

namespace LocalHirschHyperfinite
open scoped TensorProduct

universe u

/-- The algebraic alternatives for consecutive CJMST factors. The finite
case is included in the finite characteristic exhaustion alternative. -/
def AbelianPackingFactor (B : Type u) [Group B] (d : ℕ) : Prop :=
  ∃ (A : Type u) (_ : CommGroup A), Nonempty (B ≃* A) ∧
    ((∃ T : ℕ → Subgroup A, Monotone T ∧ (∀ i, (T i).Characteristic ∧ Finite (T i)) ∧
      ∀ a, ∃ i, a ∈ T i) ∨
      (IsMulTorsionFree A ∧ Module.Finite ℚ (ℚ ⊗[ℤ] Additive A) ∧
        Module.finrank ℚ (ℚ ⊗[ℤ] Additive A) ≤ d))

variable {G : Type u} [Group G]

def AbelianPackingFactorBetween (L U : Subgroup G) (d : ℕ) : Prop :=
  ∀ _ : L.Normal, AbelianPackingFactor (U.map (QuotientGroup.mk' L)) d

/-- An increasing finite normal series with an explicit common bound on
the rational ranks of its torsion-free abelian factors. -/
structure AlgebraicPackingSeries (G : Type u) [Group G] (d : ℕ) where
  length : ℕ
  layer : ℕ → Subgroup G
  normal : ∀ i, (layer i).Normal
  mono : Monotone layer
  bottom : layer 0 = ⊥
  top : layer length = ⊤
  factor : ∀ i, i < length → AbelianPackingFactorBetween (layer i) (layer (i+1)) d

private def down (G : Type u) [Group G] (i : ℕ) : Subgroup G :=
  if i%2=0 then derivedSeries G (i/2) else derivedTorsionLayer G (i/2)

@[simp] private theorem down_even (i : ℕ) : down G (2*i) = derivedSeries G i := by
  simp [down,show 2*i%2=0 by omega,show 2*i/2=i by omega]

@[simp] private theorem down_odd (i : ℕ) : down G (2*i+1) = derivedTorsionLayer G i := by
  simp [down,show (2*i+1)/2=i by omega]

private theorem down_normal (i : ℕ) : (down G i).Normal := by
  unfold down
  split <;> infer_instance

private theorem down_antitone : Antitone (down G) := by
  apply antitone_nat_of_succ_le
  intro i
  let k := i/2
  by_cases h : i%2=0
  · have he : i=2*k := by dsimp [k]; omega
    rw [he,down_even,down_odd]
    exact derivedTorsionLayer_le_derivedSeries k
  · have he : i=2*k+1 := by dsimp [k]; omega
    rw [he,down_odd,show 2*k+1+1=2*(k+1) by omega,down_even]
    exact derivedSeries_succ_le_derivedTorsionLayer k

private theorem down_factor {d : ℕ} (h : GeneratorRankLE G d) (hh : IsSolvableFiniteHirsch G)
    (i : ℕ) : AbelianPackingFactorBetween (down G (i+1)) (down G i) d := by
  let k := i/2
  let A := Abelianization (derivedSeries G k)
  let T := CommGroup.torsion A
  obtain ⟨ht,hfree,hfin⟩ := derived_abelian_factors h hh k
  by_cases hpar : i%2=0
  · have he : i=2*k := by dsimp [k]; omega
    rw [he,down_even,down_odd]
    intro hnormal
    letI : Module.Finite ℚ (ℚ ⊗[ℤ] Additive (A ⧸ T)) := hfin
    have hd : GeneratorRankLE (A ⧸ T) d := by
      have hD := h.subgroup (derivedSeries G k)
      have hA := hD.of_surjective Abelianization.of
        (QuotientGroup.mk'_surjective (commutator (derivedSeries G k)))
      exact hA.of_surjective _ (QuotientGroup.mk'_surjective T)
    exact ⟨A ⧸ T,inferInstance,derivedTorsionLayer_upper_factor k,
      Or.inr ⟨hfree,hfin,rational_finrank_le_generatorRankLE hd⟩⟩
  · have he : i=2*k+1 := by dsimp [k]; omega
    rw [he,down_odd,show 2*k+1+1=2*(k+1) by omega,down_even]
    intro hnormal
    exact ⟨T,inferInstance,derivedTorsionLayer_lower_factor k,Or.inl ht⟩

/-- A known bound on derived length bounds the length of the subdivided
normal series uniformly. -/
theorem exists_algebraicPackingSeries_of_derived_eq_bot {d n : ℕ}
    (h : GeneratorRankLE G d) (hh : IsSolvableFiniteHirsch G) (hn : derivedSeries G n = ⊥) :
    ∃ S : AlgebraicPackingSeries G d, S.length = 2*n := by
  refine ⟨{
    length := 2*n
    layer := fun i => down G (2*n-i)
    normal := fun i => down_normal (2*n-i)
    mono := fun i j hij => down_antitone (by omega)
    bottom := by simpa using hn
    top := by simp [down]
    factor := ?_ },rfl⟩
  intro i hi
  let j := 2*n-(i+1)
  have hj : j+1=2*n-i := by dsimp [j]; omega
  change AbelianPackingFactorBetween (down G (2*n-i)) (down G j) d
  rw [← hj]
  exact down_factor h hh j

/-- The derived series of a finite-Hirsch group of bounded Prüfer rank can
be subdivided into the abelian layers used in the CJMST induction. -/
theorem exists_algebraicPackingSeries {d : ℕ} (h : GeneratorRankLE G d) (hh : IsSolvableFiniteHirsch G) :
    Nonempty (AlgebraicPackingSeries G d) := by
  obtain ⟨n,hn⟩ := hh.1.solvable
  obtain ⟨S,_⟩ := exists_algebraicPackingSeries_of_derived_eq_bot h hh hn
  exact ⟨S⟩

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.AlgebraicPackingSeries

-- BEGIN COMPLETE MODULE HirschProof.SolvableQuotientDAD
section
                                     
                                         

set_option autoImplicit false
noncomputable section

namespace LocalHirschHyperfinite

open Set
open scoped TensorProduct

universe u

private theorem packedFactor_of_algebraic {B : Type u} [Group B] {d : ℕ}
    (h : AbelianPackingFactor B d) : PackedFactor B d := by
  classical
  obtain ⟨A,hA,⟨e⟩,ha⟩ := h
  letI := hA
  have hpack : PackedFactor A d := by
    rcases ha with ⟨T,hT,hTf,hTex⟩|⟨hfree,hfin,hrank⟩
    · apply packedFactor_of_finiteCharacteristic
      intro K
      have he (a : A) : ∃ n : ℕ, a ∈ K → a ∈ T n := by
        obtain ⟨n,hn⟩ := hTex a
        exact ⟨n,fun _ => hn⟩
      choose n hn using he
      let m := K.sup n
      exact ⟨T m,(hTf m).1,(hTf m).2,fun a ha => hT (Finset.le_sup ha) (hn a ha)⟩
    · letI := hfree
      letI := hfin
      exact packedFactor_of_torsionFree_rationalRank hrank
  exact hpack.of_equiv e.symm

/-- Uniform compact free-action bound for a countable solvable finite-Hirsch
group with the given generator rank and a bound on its derived length. -/
theorem compactClopenDADLE_of_solvableFiniteHirsch_generatorRank {G : Type u} [Group G] {r n : ℕ}
    (hRank : GeneratorRankLE G r) (hFinite : IsSolvableFiniteHirsch G)
    (hn : derivedSeries G n = ⊥) :
    CompactClopenDADLE G ((13^r+1)^(2*n)-1) := by
  obtain ⟨S,hLength⟩ := exists_algebraicPackingSeries_of_derived_eq_bot hRank hFinite hn
  have hFactors (i : ℕ) (hi : i < S.length) :
      letI := S.normal i
      PackedFactor ((S.layer (i+1)).map (QuotientGroup.mk' (S.layer i))) r :=
    packedFactor_of_algebraic (S.factor i hi (S.normal i))
  simpa only [hLength] using compactClopenDADLE_of_packed_factors S.length r S.layer S.normal
    S.mono S.bottom S.top hFactors

/-- The same rank and derived length bound works for all subquotients. -/
theorem subquotientDADLE_of_solvableFiniteHirsch_generatorRank {Q : Type u} [Group Q] {r n : ℕ}
    (hRank : GeneratorRankLE Q r) (hFinite : IsSolvableFiniteHirsch Q)
    (hn : derivedSeries Q n = ⊥) :
    ∀ (A C : Type u) [Group A] [Group C], ∀ (i : A →* Q) (_ : Function.Injective i)
      (p : A →* C) (_ : Function.Surjective p), CompactClopenDADLE C ((13^r+1)^(2*n)-1) := by
  intro A C _ _ i hi p hp
  have hRankA := GeneratorRankLE.of_injective i hi hRank
  have hRankC := hRankA.of_surjective p hp
  have e := MonoidHom.ofInjective hi
  have hA := (hFinite.subgroup i.range).of_surjective e.symm.toMonoidHom e.symm.surjective
  have hC := hA.of_surjective p hp
  have hnA : derivedSeries A n = ⊥ := by
    apply bot_unique
    intro a ha
    have h : i a ∈ derivedSeries Q n :=
      map_derivedSeries_le_derivedSeries i n ⟨a,ha,rfl⟩
    have he : i a = 1 := Subgroup.mem_bot.mp (hn ▸ h)
    exact Subgroup.mem_bot.mpr (hi (he.trans (map_one i).symm))
  have hnC : derivedSeries C n = ⊥ := by
    rw [← map_derivedSeries_eq hp n,hnA,Subgroup.map_bot]
  exact compactClopenDADLE_of_solvableFiniteHirsch_generatorRank hRankC hC hnC

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.SolvableQuotientDAD

-- BEGIN COMPLETE MODULE HirschProof.SubquotientDimensions
section
                                      

set_option autoImplicit false

namespace LocalHirschHyperfinite

universe u

/-- A uniform compact-action dimension bound for subquotients of one group. -/
def SubquotientDADLE (Q : Type u) [Group Q] (d : ℕ) : Prop :=
  ∀ (A C : Type u) [Group A] [Group C], ∀ (i : A →* Q) (_ : Function.Injective i)
    (p : A →* C) (_ : Function.Surjective p), CompactClopenDADLE C d

theorem SubquotientDADLE.of_injective {A Q : Type u} [Group A] [Group Q]
    {d : ℕ} (h : SubquotientDADLE Q d) (i : A →* Q) (hi : Function.Injective i) :
    SubquotientDADLE A d :=
  fun B C _ _ j hj p hp => h B C (i.comp j) (hi.comp hj) p hp

theorem exists_subquotientDADLE_of_solvableFiniteHirsch_generatorRank {Q : Type u} [Group Q]
    {r : ℕ} (hQ : IsSolvableFiniteHirsch Q) (hRank : GeneratorRankLE Q r) :
    ∃ d : ℕ, SubquotientDADLE Q d := by
  letI : IsSolvable Q := hQ.1
  obtain ⟨n,hn⟩ := IsSolvable.solvable (G := Q)
  exact ⟨_,subquotientDADLE_of_solvableFiniteHirsch_generatorRank hRank hQ hn⟩

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.SubquotientDimensions

-- BEGIN COMPLETE MODULE HirschProof.TaggedSwitches
section
                                          
                                
                                                   
                                

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set
open scoped Pointwise

variable {G Γ X : Type*} [Group G] [Group Γ] [MulAction G X]

abbrev TaggedSpace (Z : Set X) (Γ : Type*) := Z × Γ × Bool

namespace TaggedSpace

variable (Z : Set X) (q : G →* Γ)

def switchForward (g : G) (t : Γ) (x : TaggedSpace Z Γ) : Prop :=
  x.2.1 = t ∧ x.2.2 = false ∧ g • x.1.val ∈ Z

def switchBackward (g : G) (t : Γ) (x : TaggedSpace Z Γ) : Prop :=
  x.2.1 = q g * t ∧ x.2.2 = true ∧ g⁻¹ • x.1.val ∈ Z

noncomputable def switchFun (g : G) (t : Γ) (x : TaggedSpace Z Γ) : TaggedSpace Z Γ := by
  classical
  exact if hf : switchForward Z g t x then
      (⟨g • x.1.val,hf.2.2⟩,q g*t,true)
    else if hb : switchBackward Z q g t x then
      (⟨g⁻¹ • x.1.val,hb.2.2⟩,t,false)
    else x

theorem switch_involutive (g : G) (t : Γ) : Function.Involutive (switchFun Z q g t) := by
  classical
  intro x
  by_cases hF : switchForward Z g t x
  · have hB' : switchBackward Z q g t (⟨g • x.1.val,hF.2.2⟩,q g*t,true) := by
      exact ⟨rfl,rfl,by simp⟩
    have hnF' : ¬ switchForward Z g t (⟨g • x.1.val,hF.2.2⟩,q g*t,true) := by
      simp [switchForward]
    simp only [switchFun,dif_pos hF,dif_neg hnF',dif_pos hB']
    refine Prod.ext (Subtype.ext (inv_smul_smul _ _)) (Prod.ext hF.1.symm hF.2.1.symm)
  · by_cases hB : switchBackward Z q g t x
    · have hF' : switchForward Z g t (⟨g⁻¹ • x.1.val,hB.2.2⟩,t,false) := by
        exact ⟨rfl,rfl,by simp⟩
      simp only [switchFun,dif_neg hF,dif_pos hB,dif_pos hF']
      refine Prod.ext (Subtype.ext (smul_inv_smul _ _)) (Prod.ext hB.1.symm hB.2.1.symm)
    · simp only [switchFun,dif_neg hF,dif_neg hB]

noncomputable def switch (g : G) (t : Γ) : Equiv.Perm (TaggedSpace Z Γ) :=
  (switch_involutive Z q g t).toPerm _

def rightTag (v : Γ) : Equiv.Perm (TaggedSpace Z Γ) where
  toFun x := (x.1,x.2.1*v⁻¹,x.2.2)
  invFun x := (x.1,x.2.1*v,x.2.2)
  left_inv := by rintro ⟨x,t,b⟩; simp [mul_assoc]
  right_inv := by rintro ⟨x,t,b⟩; simp [mul_assoc]

theorem rightTag_mul (v w : Γ) : rightTag Z (v*w) = rightTag Z v * rightTag Z w := by
  ext x : 1
  simp [rightTag,mul_assoc]

theorem rightTag_one : rightTag Z (1 : Γ) = 1 := by
  ext x : 1
  simp [rightTag]

section Measurable

variable [MeasurableSpace X] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

theorem measurableSet_switchForward (hZ : MeasurableSet Z) (hX : BorelAction G X)
    (g : G) (t : Γ) : MeasurableSet {x | switchForward Z g t x} :=
  ((measurableSet_singleton t).preimage measurable_snd.fst).inter
    ((measurableSet_eq_fun measurable_snd.snd measurable_const).inter
      (hZ.preimage ((hX g).comp (measurable_subtype_coe.comp measurable_fst))))

theorem measurableSet_switchBackward (hZ : MeasurableSet Z) (hX : BorelAction G X)
    (g : G) (t : Γ) : MeasurableSet {x | switchBackward Z q g t x} :=
  ((measurableSet_singleton (q g*t)).preimage measurable_snd.fst).inter
    ((measurableSet_eq_fun measurable_snd.snd measurable_const).inter
      (hZ.preimage ((hX g⁻¹).comp (measurable_subtype_coe.comp measurable_fst))))

theorem measurable_switch (hZ : MeasurableSet Z) (hX : BorelAction G X)
    (g : G) (t : Γ) : Measurable (switch Z q g t) := by
  classical
  let A := {x : TaggedSpace Z Γ | switchForward Z g t x}
  let B := {x : TaggedSpace Z Γ | switchBackward Z q g t x}
  have hA : MeasurableSet A := measurableSet_switchForward Z hZ hX g t
  have hB : MeasurableSet B := measurableSet_switchBackward Z q hZ hX g t
  let unpack (x : TaggedSpace Z Γ) : X × Γ × Bool := (x.1.val,x.2)
  let f (x : TaggedSpace Z Γ) : X × Γ × Bool := (g • x.1.val,q g*t,true)
  let e (x : TaggedSpace Z Γ) : X × Γ × Bool := (g⁻¹ • x.1.val,t,false)
  have hu : Measurable unpack := (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hf : Measurable f := ((hX g).comp (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_const
  have he : Measurable e := ((hX g⁻¹).comp (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_const
  let w : TaggedSpace Z Γ → X × Γ × Bool := A.piecewise f (B.piecewise e unpack)
  have hw : Measurable w := hf.piecewise hA (he.piecewise hB hu)
  have hdef (x : TaggedSpace Z Γ) : w x = unpack (switch Z q g t x) := by
    change w x = unpack (switchFun Z q g t x)
    by_cases ha : switchForward Z g t x <;> by_cases hb : switchBackward Z q g t x <;>
      simp [w,A,B,f,e,unpack,switchFun,piecewise,ha,hb]
  have hfst : Measurable (fun x : TaggedSpace Z Γ => (switch Z q g t x).1.val) := by
    simpa only [hdef] using hw.fst
  have hsnd : Measurable (fun x : TaggedSpace Z Γ => (switch Z q g t x).2) := by
    simpa only [hdef] using hw.snd
  exact hfst.subtype_mk.prodMk hsnd

theorem measurable_rightTag [Countable Γ] (v : Γ) : Measurable (rightTag Z v) :=
  measurable_fst.prodMk ((measurable_of_countable (fun t : Γ => t*v⁻¹)).comp measurable_snd.fst
    |>.prodMk measurable_snd.snd)

end Measurable

/-- A tagged map has finitely many possible physical displacements and the given right projection. -/
def finiteTransport (v : Γ) (f : TaggedSpace Z Γ → TaggedSpace Z Γ) : Prop :=
  ∃ U : Finset G, ∀ x : TaggedSpace Z Γ, ∃ g ∈ U,
    (f x).1.val = g • x.1.val ∧ (f x).2.1 = q g * x.2.1 * v⁻¹

theorem finiteTransport_id : finiteTransport Z q 1 id := by
  classical
  exact ⟨{1},fun x => ⟨1,by simp,by simp,by simp⟩⟩

theorem finiteTransport_switch (g : G) (t : Γ) : finiteTransport Z q 1 (switch Z q g t) := by
  classical
  refine ⟨{g,g⁻¹,1},fun x => ?_⟩
  change ∃ a ∈ ({g,g⁻¹,1} : Finset G),
    (switchFun Z q g t x).1.val = a • x.1.val ∧
      (switchFun Z q g t x).2.1 = q a * x.2.1 * (1 : Γ)⁻¹
  by_cases hf : switchForward Z g t x
  · exact ⟨g,by simp,by simp [switchFun,hf],by simp [switchFun,hf,hf.1]⟩
  · by_cases hb : switchBackward Z q g t x
    · exact ⟨g⁻¹,by simp,by simp [switchFun,hf,hb],by simp [switchFun,hf,hb,hb.1,mul_assoc]⟩
    · exact ⟨1,by simp,by simp [switchFun,hf,hb],by simp [switchFun,hf,hb]⟩

theorem finiteTransport_rightTag (v : Γ) : finiteTransport Z q v (rightTag Z v) := by
  classical
  exact ⟨{1},fun _ => ⟨1,by simp,by simp [rightTag],by simp [rightTag]⟩⟩

theorem finiteTransport_comp {v w : Γ} {f e : TaggedSpace Z Γ → TaggedSpace Z Γ}
    (hf : finiteTransport Z q v f) (he : finiteTransport Z q w e) :
    finiteTransport Z q (v*w) (f ∘ e) := by
  classical
  obtain ⟨F,hF⟩ := hf
  obtain ⟨E,hE⟩ := he
  refine ⟨F*E,fun x => ?_⟩
  obtain ⟨a,ha,hax,hat⟩ := hF (e x)
  obtain ⟨b,hb,hbx,hbt⟩ := hE x
  refine ⟨a*b,Finset.mul_mem_mul ha hb,?_,?_⟩
  · simp [Function.comp_def,hax,hbx,mul_smul]
  · simp [Function.comp_def,hat,hbt,mul_assoc]

theorem projection_eq_one_of_fixed {v : Γ} {f : TaggedSpace Z Γ → TaggedSpace Z Γ}
    (hf : finiteTransport Z q v f)
    (hZ : ∀ (z : Z) (g : G), g • z.val = z.val → q g = 1)
    {x : TaggedSpace Z Γ} (fix : f x = x) : v = 1 := by
  obtain ⟨_,h⟩ := hf
  obtain ⟨g,_,hg,ht⟩ := h x
  rw [fix] at hg ht
  rw [hZ x.1 g hg.symm,one_mul] at ht
  have hx : (1 : Γ) = v⁻¹ := mul_left_cancel (show x.2.1 * 1 = x.2.1 * v⁻¹ by simpa using ht)
  simpa using congrArg Inv.inv hx.symm

end TaggedSpace
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.TaggedSwitches

-- BEGIN COMPLETE MODULE HirschProof.TaggedExtension
section
                                 
                                             
                                      

set_option autoImplicit false

namespace LocalHirschHyperfinite.TaggedSpace
open Set

variable {G Γ X : Type*} [Group G] [Group Γ] [MulAction G X]
variable (Z : Set X) (q : G →* Γ)

theorem rightTag_inv (v : Γ) : (rightTag Z v)⁻¹ = rightTag Z v⁻¹ := by
  ext x : 1
  simp [rightTag]

theorem rightTag_switch_commute (v : Γ) (g : G) (t : Γ) :
    rightTag Z v * switch Z q g t = switch Z q g (t*v⁻¹) * rightTag Z v := by
  classical
  ext x : 1
  have hF : switchForward Z g (t*v⁻¹) (rightTag Z v x) ↔ switchForward Z g t x := by
    simp [switchForward,rightTag]
  have hB : switchBackward Z q g (t*v⁻¹) (rightTag Z v x) ↔ switchBackward Z q g t x := by
    simp [switchBackward,rightTag,← mul_assoc]
  change rightTag Z v (switchFun Z q g t x) = switchFun Z q g (t*v⁻¹) (rightTag Z v x)
  by_cases hf : switchForward Z g t x
  · simp only [switchFun,dif_pos hf,dif_pos (hF.mpr hf)]
    simp [rightTag,mul_assoc]
  · by_cases hb : switchBackward Z q g t x
    · simp only [switchFun,dif_neg hf,dif_neg (fun h => hf (hF.mp h)),
        dif_pos hb,dif_pos (hB.mpr hb)]
      rfl
    · simp only [switchFun,dif_neg hf,dif_neg (fun h => hf (hF.mp h)),
        dif_neg hb,dif_neg (fun h => hb (hB.mp h))]

def switchGenerators : Set (Equiv.Perm (TaggedSpace Z Γ)) :=
  {σ | ∃ g : G, ∃ t : Γ, switch Z q g t = σ}

def switchGroup : Subgroup (Equiv.Perm (TaggedSpace Z Γ)) := Subgroup.closure (switchGenerators Z q)

theorem switch_mem_group (g : G) (t : Γ) : switch Z q g t ∈ switchGroup Z q :=
  Subgroup.subset_closure ⟨g,t,rfl⟩

theorem tag_conj_mem_switchGroup (v : Γ) {σ : Equiv.Perm (TaggedSpace Z Γ)}
    (hσ : σ ∈ switchGroup Z q) : rightTag Z v * σ * (rightTag Z v)⁻¹ ∈ switchGroup Z q := by
  change σ ∈ Subgroup.closure (switchGenerators Z q) at hσ
  induction hσ using Subgroup.closure_induction with
  | mem σ hσ =>
    obtain ⟨g,t,rfl⟩ := hσ
    rw [rightTag_switch_commute Z q]
    simpa [mul_assoc] using switch_mem_group Z q g (t*v⁻¹)
  | one => simp
  | mul a b _ _ ha hb =>
    convert (switchGroup Z q).mul_mem ha hb using 1
    group
  | inv a _ ha =>
    simpa only [mul_inv_rev,inv_inv] using (switchGroup Z q).inv_mem ha

/-- The semidirect product realized as a subgroup of permutations paired with their projection. -/
def taggedExtension : Subgroup (Equiv.Perm (TaggedSpace Z Γ) × Γ) where
  carrier := {p | p.1 * (rightTag Z p.2)⁻¹ ∈ switchGroup Z q}
  one_mem' := by simp [rightTag_one]
  mul_mem' := by
    rintro ⟨σ,v⟩ ⟨τ,w⟩ hσ hτ
    change σ * (rightTag Z v)⁻¹ ∈ switchGroup Z q at hσ
    change τ * (rightTag Z w)⁻¹ ∈ switchGroup Z q at hτ
    change σ*τ*(rightTag Z (v*w))⁻¹ ∈ switchGroup Z q
    have hh := (switchGroup Z q).mul_mem hσ (tag_conj_mem_switchGroup Z q v hτ)
    convert hh using 1 <;> rw [rightTag_mul Z v w] <;> group
  inv_mem' := by
    rintro ⟨σ,v⟩ hσ
    change σ * (rightTag Z v)⁻¹ ∈ switchGroup Z q at hσ
    change σ⁻¹ * (rightTag Z v⁻¹)⁻¹ ∈ switchGroup Z q
    have hh := tag_conj_mem_switchGroup Z q v⁻¹ ((switchGroup Z q).inv_mem hσ)
    convert hh using 1 <;> rw [← rightTag_inv Z v] <;> group

def taggedProjection : taggedExtension Z q →* Γ where
  toFun g := g.val.2
  map_one' := rfl
  map_mul' _ _ := rfl

def taggedPerm : taggedExtension Z q →* Equiv.Perm (TaggedSpace Z Γ) where
  toFun g := g.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem taggedProjection_surjective : Function.Surjective (taggedProjection Z q) := by
  intro v
  refine ⟨⟨(rightTag Z v,v),?_⟩,rfl⟩
  change rightTag Z v * (rightTag Z v)⁻¹ ∈ switchGroup Z q
  simp

theorem taggedProjection_eq_one_iff (g : taggedExtension Z q) :
    taggedProjection Z q g = 1 ↔ g.val.2 = 1 := Iff.rfl

theorem tagged_permutation_decomposition (g : taggedExtension Z q) :
    ∃ σ ∈ switchGroup Z q, g.val.1 = σ * rightTag Z g.val.2 := by
  refine ⟨g.val.1 * (rightTag Z g.val.2)⁻¹,g.property,?_⟩
  group

theorem finiteTransport_perm_inv {v : Γ} {f : Equiv.Perm (TaggedSpace Z Γ)}
    (hf : finiteTransport Z q v f) : finiteTransport Z q v⁻¹ (⇑(f⁻¹ : Equiv.Perm (TaggedSpace Z Γ))) := by
  classical
  obtain ⟨A,hA⟩ := hf
  refine ⟨A.image Inv.inv,fun x => ?_⟩
  obtain ⟨g,hg,he,ht⟩ := hA (f⁻¹ x)
  rw [show f (f⁻¹ x) = x from f.apply_symm_apply x] at he ht
  refine ⟨g⁻¹,Finset.mem_image_of_mem _ hg,?_,?_⟩
  · rw [he,inv_smul_smul]
  · rw [ht,map_inv,inv_inv]
    group

theorem finiteTransport_switchGroup {σ : Equiv.Perm (TaggedSpace Z Γ)}
    (h : σ ∈ switchGroup Z q) : finiteTransport Z q 1 σ := by
  change σ ∈ Subgroup.closure (switchGenerators Z q) at h
  induction h using Subgroup.closure_induction with
  | mem σ hσ =>
    obtain ⟨g,t,rfl⟩ := hσ
    exact finiteTransport_switch Z q g t
  | one => exact finiteTransport_id Z q
  | mul a b _ _ ha hb => simpa using finiteTransport_comp Z q ha hb
  | inv a _ ha => simpa using finiteTransport_perm_inv Z q ha

theorem finiteTransport_tagged (g : taggedExtension Z q) :
    finiteTransport Z q (taggedProjection Z q g) (taggedPerm Z q g) := by
  obtain ⟨σ,hσ,he⟩ := tagged_permutation_decomposition Z q g
  change finiteTransport Z q g.val.2 g.val.1
  rw [he]
  simpa using finiteTransport_comp Z q (finiteTransport_switchGroup Z q hσ)
    (finiteTransport_rightTag (G := G) Z q g.val.2)

theorem tagged_stabilizer_in_kernel (g : taggedExtension Z q)
    (hZ : ∀ (z : Z) (a : G), a • z.val = z.val → q a = 1)
    {x : TaggedSpace Z Γ} (hfix : taggedPerm Z q g x = x) : taggedProjection Z q g = 1 :=
  projection_eq_one_of_fixed Z q (finiteTransport_tagged Z q g) hZ hfix

noncomputable def liftSwitch (g : G) (t : Γ) : taggedExtension Z q := by
  refine ⟨(switch Z q g t,1),?_⟩
  change switch Z q g t * (rightTag Z 1)⁻¹ ∈ switchGroup Z q
  simpa only [rightTag_one,inv_one,mul_one] using switch_mem_group Z q g t

def liftTag (v : Γ) : taggedExtension Z q := by
  refine ⟨(rightTag Z v,v),?_⟩
  change rightTag Z v * (rightTag Z v)⁻¹ ∈ switchGroup Z q
  simp

instance taggedMulAction : MulAction (taggedExtension Z q) (TaggedSpace Z Γ) where
  smul g x := taggedPerm Z q g x
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

def entry (z : Z) : TaggedSpace Z Γ := (z,1,false)

noncomputable def physicalMove (g : G) : taggedExtension Z q :=
  liftSwitch Z q 1 1 * liftTag Z q (q g) * liftSwitch Z q g 1

theorem physicalMove_entry {x y : Z} {g : G} (h : g • x.val = y.val) :
    physicalMove Z q g • entry (Γ := Γ) Z x = entry (Γ := Γ) Z y := by
  classical
  change switchFun Z q 1 1
    (rightTag Z (q g) (switchFun Z q g 1 (entry Z x))) = entry Z y
  have hF : switchForward Z g (1 : Γ) (entry (Γ := Γ) Z x) := ⟨rfl,rfl,h.symm ▸ y.property⟩
  have hfirst : switchFun Z q g 1 (entry (Γ := Γ) Z x) =
      (⟨g • x.val,hF.2.2⟩,q g*1,true) := by
    simp only [switchFun,dif_pos hF]
    rfl
  have ht : rightTag Z (q g) (⟨g • x.val,hF.2.2⟩,q g*1,true) = (y,1,true) := by
    exact Prod.ext (Subtype.ext h) (by simp [rightTag])
  have hnF : ¬ switchForward Z (1 : G) 1 ((y,1,true) : TaggedSpace Z Γ) := by simp [switchForward]
  have hB : switchBackward Z q 1 1 ((y,1,true) : TaggedSpace Z Γ) := by
    exact ⟨by simp,rfl,by simpa using y.property⟩
  rw [hfirst,ht]
  simp only [switchFun,dif_neg hnF,dif_pos hB,entry]
  exact Prod.ext (Subtype.ext (by simp)) rfl

theorem entry_injective : Function.Injective (entry (Γ := Γ) Z) := fun _ _ h => congrArg Prod.fst h

theorem entry_reduces_orbit (x y : Z) :
    orbitRel G x.val y.val ↔ orbitRel (taggedExtension Z q)
      (entry (Γ := Γ) Z x) (entry (Γ := Γ) Z y) := by
  constructor
  · rintro ⟨g,h⟩
    exact ⟨physicalMove Z q g,physicalMove_entry Z q h⟩
  · rintro ⟨g,h⟩
    obtain ⟨_,hfin⟩ := finiteTransport_tagged Z q g
    obtain ⟨a,_,ha,_⟩ := hfin (entry Z x)
    exact ⟨a,ha.symm.trans (congrArg (fun z : TaggedSpace Z Γ => z.1.val) h)⟩

theorem countable_switchGroup [Countable G] [Countable Γ] : Countable (switchGroup Z q) := by
  let g (p : G × Γ) := switch Z q p.1 p.2
  have hgen : switchGenerators Z q = Set.range g := by
    ext σ
    constructor
    · rintro ⟨a,b,h⟩; exact ⟨(a,b),h⟩
    · rintro ⟨⟨a,b⟩,h⟩; exact ⟨a,b,h⟩
  have hG : switchGroup Z q = (FreeGroup.lift g).range := by
    unfold switchGroup
    rw [hgen,FreeGroup.range_lift_eq_closure]
  rw [hG]
  exact (MonoidHom.rangeRestrict_surjective (FreeGroup.lift g)).countable

theorem countable_taggedExtension [Countable G] [Countable Γ] : Countable (taggedExtension Z q) := by
  letI : Countable (switchGroup Z q) := countable_switchGroup Z q
  let embedding (g : taggedExtension Z q) : switchGroup Z q × Γ :=
    (⟨g.val.1 * (rightTag Z g.val.2)⁻¹,g.property⟩,g.val.2)
  apply Function.Injective.countable (f := embedding)
  intro g h he
  apply Subtype.ext
  have hΓ : g.val.2 = h.val.2 := congrArg (fun p : switchGroup Z q × Γ => p.2) he
  have hσ : g.val.1 * (rightTag Z g.val.2)⁻¹ = h.val.1 * (rightTag Z h.val.2)⁻¹ :=
    congrArg (fun p : switchGroup Z q × Γ => p.1.val) he
  rw [← hΓ] at hσ
  exact Prod.ext (mul_right_cancel hσ) hΓ

section Measurable
variable [MeasurableSpace X] [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [Countable Γ]

theorem measurable_entry : Measurable (entry (Γ := Γ) Z) := measurable_id.prodMk measurable_const

theorem measurable_switchGroup (hZ : MeasurableSet Z) (hX : BorelAction G X)
    {σ : Equiv.Perm (TaggedSpace Z Γ)} (h : σ ∈ switchGroup Z q) :
    Measurable σ ∧ Measurable (⇑(σ⁻¹ : Equiv.Perm (TaggedSpace Z Γ))) := by
  change σ ∈ Subgroup.closure (switchGenerators Z q) at h
  induction h using Subgroup.closure_induction with
  | mem σ hσ =>
    obtain ⟨g,t,rfl⟩ := hσ
    have hm := measurable_switch Z q hZ hX g t
    exact ⟨hm,hm⟩
  | one => exact ⟨measurable_id,measurable_id⟩
  | mul a b _ _ ha hb =>
    refine ⟨ha.1.comp hb.1,?_⟩
    rw [mul_inv_rev]
    exact hb.2.comp ha.2
  | inv a _ ha => exact ⟨ha.2,by simpa only [inv_inv] using ha.1⟩

theorem borel_taggedAction (hZ : MeasurableSet Z) (hX : BorelAction G X) :
    BorelAction (taggedExtension Z q) (TaggedSpace Z Γ) := by
  intro g
  obtain ⟨σ,hσ,he⟩ := tagged_permutation_decomposition Z q g
  change Measurable (⇑g.val.1)
  rw [he]
  exact (measurable_switchGroup Z q hZ hX hσ).1.comp (measurable_rightTag Z g.val.2)

end Measurable

end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.TaggedExtension

-- BEGIN COMPLETE MODULE HirschProof.GraphColoring
section
                                          
                                                               
                              
                              

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite
namespace FiniteNeighborColoring

variable {X : Type*} {d : ℕ}

/-- The finite maps list the oriented neighbors. Fixed points are ignored. -/
def Proper {C : Type*} (edge : Fin d → X → X) (c : X → C) : Prop :=
  ∀ i x, edge i x ≠ x → c x ≠ c (edge i x)

def Symmetric (edge : Fin d → X → X) : Prop :=
  ∀ i x, edge i x ≠ x → ∃ j, edge j (edge i x) = x

private theorem exists_freshColor (colors : Fin d → Fin (d+1)) :
    ∃ i : Fin (d+1), ∀ j, i ≠ colors j := by
  classical
  let used := Finset.univ.image colors
  have h : ∃ i : Fin (d+1), i ∉ used := by
    by_contra! hc
    have hsub : Finset.univ ⊆ used := fun i _ => hc i
    have hcard : (Finset.univ : Finset (Fin (d+1))).card ≤
        (Finset.univ : Finset (Fin d)).card :=
      (Finset.card_le_card hsub).trans Finset.card_image_le
    simp at hcard
  obtain ⟨i,hi⟩ := h
  exact ⟨i,fun j hEq => hi (hEq.symm ▸ Finset.mem_image_of_mem colors (Finset.mem_univ j))⟩

noncomputable def freshColor (colors : Fin d → Fin (d+1)) : Fin (d+1) :=
  (exists_freshColor colors).choose

theorem freshColor_ne (colors : Fin d → Fin (d+1)) (j : Fin d) :
    freshColor colors ≠ colors j := by
  exact (exists_freshColor colors).choose_spec j

/-- Give a vertex its permanent color when its seed color is reached. -/
noncomputable def greedyState (edge : Fin d → X → X) (seed : X → ℕ) :
    ℕ → X → Fin (d+1)
  | 0, _ => 0
  | n+1, x => if seed x = n then
      freshColor (fun i => greedyState edge seed n (edge i x))
    else greedyState edge seed n x

noncomputable def greedyColor (edge : Fin d → X → X) (seed : X → ℕ) (x : X) : Fin (d+1) :=
  greedyState edge seed (seed x + 1) x

theorem greedyState_stabilizes (edge : Fin d → X → X) (seed : X → ℕ)
    (x : X) {n : ℕ} (h : seed x < n) :
    greedyState edge seed n x = greedyColor edge seed x := by
  change greedyState edge seed n x = greedyState edge seed (seed x+1) x
  refine Nat.le_induction rfl (fun k hk ih => ?_) n (Nat.succ_le_of_lt h)
  rw [greedyState,if_neg (by omega)]
  exact ih

theorem greedyColor_proper (edge : Fin d → X → X) (hSym : Symmetric edge)
    {seed : X → ℕ} (hseed : Proper edge seed) : Proper edge (greedyColor edge seed) := by
  have low (x : X) (i : Fin d) (hle : seed (edge i x) < seed x) :
      greedyColor edge seed x ≠ greedyColor edge seed (edge i x) := by
    change greedyState edge seed (seed x+1) x ≠ greedyColor edge seed (edge i x)
    rw [greedyState,if_pos rfl]
    have h := greedyState_stabilizes edge seed (edge i x) hle
    rw [← h]
    exact freshColor_ne _ i
  intro i x hne
  cases lt_or_gt_of_ne (hseed i x hne) with
  | inl h =>
    obtain ⟨j,hj⟩ := hSym i x hne
    have hh := low (edge i x) j (by simpa only [hj] using h)
    rw [hj] at hh
    exact hh.symm
  | inr h => exact low x i h

section Measurable
variable [MeasurableSpace X]

theorem greedyColor_measurable (edge : Fin d → X → X) (he : ∀ i, Measurable (edge i))
    {seed : X → ℕ} (hseed : Measurable seed) : Measurable (greedyColor edge seed) := by
  classical
  have hstate (n : ℕ) : Measurable (greedyState edge seed n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      have htuple : Measurable (fun x i => greedyState edge seed n (edge i x)) :=
        measurable_pi_lambda _ (fun i => ih.comp (he i))
      have htest : MeasurableSet {x | seed x = n} :=
        hseed (measurableSet_singleton n)
      exact ((measurable_of_countable freshColor).comp htuple).piecewise htest ih
  have hprod : Measurable (fun p : ℕ × X => greedyState edge seed (p.1+1) p.2) :=
    measurable_from_prod_countable_right (fun n => hstate (n+1))
  exact hprod.comp (hseed.prodMk measurable_id)

theorem exists_countable_seed [MeasurableSpace.CountablySeparated X]
    (edge : Fin d → X → X) (he : ∀ i, Measurable (edge i)) :
    ∃ c : X → ℕ, Measurable c ∧ Proper edge c := by
  classical
  obtain ⟨b,hb,hbInj⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated (α := X)
  let test (n : ℕ) (x : X) : Prop :=
    ∀ i : Fin d, edge i x = x ∨ ∃ k : Fin n, b x k.val ≠ b (edge i x) k.val
  have hex (x : X) : ∃ n, test n x := by
    have hw (i : Fin d) : ∃ k, edge i x ≠ x → b x k ≠ b (edge i x) k := by
      by_cases h : edge i x = x
      · exact ⟨0,fun hn => (hn h).elim⟩
      · have hneq : b x ≠ b (edge i x) := fun hh => h (hbInj hh.symm)
        have he : ∃ k, b x k ≠ b (edge i x) k := by
          by_contra! hn
          exact hneq (funext hn)
        obtain ⟨k,hk⟩ := he
        exact ⟨k,fun _ => hk⟩
    choose k hk using hw
    let n := (Finset.univ : Finset (Fin d)).sup k + 1
    refine ⟨n,fun i => ?_⟩
    by_cases hi : edge i x = x
    · exact Or.inl hi
    · have hlt : k i < n := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
      exact Or.inr ⟨⟨k i,hlt⟩,hk i hi⟩
  have hm (n : ℕ) : MeasurableSet {x | test n x} := by
    have heq : {x | test n x} =
        ⋂ i : Fin d, {x | edge i x = x} ∪
          ⋃ k : Fin n, {x | b x k.val ≠ b (edge i x) k.val} := by
      ext x
      simp [test]
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    have hE : {x | edge i x = x} = {x | b (edge i x) = b x} := by
      ext x
      simp [hbInj.eq_iff]
    rw [hE]
    refine (measurableSet_eq_fun (hb.comp (he i)) hb).union (MeasurableSet.iUnion fun k => ?_)
    exact (measurableSet_eq_fun ((measurable_pi_apply k.val).comp hb)
      ((measurable_pi_apply k.val).comp (hb.comp (he i)))).compl
  let Code := Σ n : ℕ, Fin n → Bool
  obtain ⟨enc,henc⟩ := exists_injective_nat Code
  let code (n : ℕ) (x : X) := enc ⟨n,fun i => b x i.val⟩
  have hcode (n : ℕ) : Measurable (code n) := by
    let f (u : Fin n → Bool) := enc ⟨n,u⟩
    exact (measurable_of_countable f).comp
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply i.val).comp hb))
  let depth (x : X) := Nat.find (hex x)
  let seed (x : X) := code (depth x) x
  refine ⟨seed,Measurable.find hcode hm hex,?_⟩
  intro i x hi heq
  have hEq : (⟨depth x,fun j => b x j.val⟩ : Code) =
      ⟨depth (edge i x),fun j => b (edge i x) j.val⟩ := henc heq
  have hDepth : depth x = depth (edge i x) := congrArg Sigma.fst hEq
  have hx := (Nat.find_spec (hex x) i).resolve_left hi
  obtain ⟨j,hj⟩ := hx
  let read (s : Code) := if h : j.val < s.1 then s.2 ⟨j.val,h⟩ else false
  have hbit := congrArg read hEq
  have hi₁ : j.val < depth x := j.isLt
  have hi₂ : j.val < depth (edge i x) := hDepth ▸ hi₁
  exact hj (by simpa only [read,dif_pos hi₁,dif_pos hi₂] using hbit)

/-- A symmetric finite enumeration of Borel neighbors admits a proper Borel coloring. -/
theorem exists_borel_greedy_coloring [StandardBorelSpace X]
    (edge : Fin d → X → X) (he : ∀ i, Measurable (edge i)) (hs : Symmetric edge) :
    ∃ c : X → Fin (d+1), Measurable c ∧ Proper edge c := by
  obtain ⟨seed,hm,hproper⟩ := exists_countable_seed edge he
  exact ⟨greedyColor edge seed,greedyColor_measurable edge he hm,greedyColor_proper edge hs hproper⟩

end Measurable
end FiniteNeighborColoring
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.GraphColoring

-- BEGIN COMPLETE MODULE HirschProof.PaletteCompression
section
                                
                           
                                    

set_option autoImplicit false

namespace LocalHirschHyperfinite.FiniteNeighborColoring

variable {X Y : Type*} {d : ℕ}

def follow (edge : Fin d → X → X) : List (Fin d) → X → X
  | [], x => x
  | a :: w, x => follow edge w (edge a x)

theorem follow_append (edge : Fin d → X → X) (a b : List (Fin d)) (x : X) :
    follow edge (a ++ b) x = follow edge b (follow edge a x) := by
  induction a generalizing x with
  | nil => rfl
  | cons i w ih => exact ih (edge i x)

def AgreeOnBall {C : Type*} (edge : Fin d → X → X) (edge' : Fin d → Y → Y)
    (f : X → C) (f' : Y → C) (x : X) (y : Y) (r : ℕ) : Prop :=
  ∀ w : List (Fin d), w.length ≤ r → f (follow edge w x) = f' (follow edge' w y)

theorem AgreeOnBall.center {C : Type*} {edge : Fin d → X → X} {edge' : Fin d → Y → Y}
    {f : X → C} {f' : Y → C} {x : X} {y : Y} {r : ℕ}
    (h : AgreeOnBall edge edge' f f' x y r) : f x = f' y :=
  h [] (Nat.zero_le _)

theorem AgreeOnBall.mono {C : Type*} {edge : Fin d → X → X} {edge' : Fin d → Y → Y}
    {f : X → C} {f' : Y → C} {x : X} {y : Y} {r s : ℕ}
    (h : AgreeOnBall edge edge' f f' x y s) (hrs : r ≤ s) :
    AgreeOnBall edge edge' f f' x y r := fun w hw => h w (hw.trans hrs)

theorem AgreeOnBall.follow {C : Type*} {edge : Fin d → X → X} {edge' : Fin d → Y → Y}
    {f : X → C} {f' : Y → C} {x : X} {y : Y} {r s : ℕ}
    (h : AgreeOnBall edge edge' f f' x y s) (w : List (Fin d))
    (hw : w.length + r ≤ s) :
    AgreeOnBall edge edge' f f' (follow edge w x) (follow edge' w y) r := by
  intro v hv
  rw [← follow_append, ← follow_append]
  exact h (w ++ v) (by simpa using (Nat.add_le_add_left hv _).trans hw)

theorem greedyState_local (edge : Fin d → X → X) (edge' : Fin d → Y → Y)
    (f : X → ℕ) (f' : Y → ℕ) (n : ℕ) (x : X) (y : Y)
    (h : AgreeOnBall edge edge' f f' x y n) :
    greedyState edge f n x = greedyState edge' f' n y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    simp only [greedyState, h.center]
    split
    · apply congrArg freshColor
      funext i
      apply ih
      exact h.follow [i] (by simp [Nat.add_comm])
    · exact ih _ _ (h.mono (Nat.le_succ _))

theorem greedyColor_local (edge : Fin d → X → X) (edge' : Fin d → Y → Y)
    (f : X → ℕ) (f' : Y → ℕ) (M : ℕ) (x : X) (y : Y)
    (hx : f x < M) (h : AgreeOnBall edge edge' f f' x y M) :
    greedyColor edge f x = greedyColor edge' f' y := by
  unfold greedyColor
  rw [← h.center]
  exact greedyState_local edge edge' f f' (f x+1) x y (h.mono hx)

def binaryWidth (m : ℕ) := Nat.clog 2 m + 1

def bitPalette (d m : ℕ) := (binaryWidth m * 2)^d

private theorem distinguish_bit {m : ℕ} {a b : Fin m} (hn : a ≠ b) :
    ∃ j : Fin (binaryWidth m), a.val.testBit j.val ≠ b.val.testBit j.val := by
  by_contra! he
  apply hn
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < binaryWidth m
  · exact he ⟨j,hj⟩
  · have hM : m ≤ 2^j := (Nat.clog_le_iff_le_pow Nat.one_lt_two).mp
      (by unfold binaryWidth at hj; omega)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hM),
      Nat.testBit_lt_two_pow (b.isLt.trans_le hM)]

noncomputable def bitPosition {m : ℕ} (a b : Fin m) : Fin (binaryWidth m) := by
  classical
  exact if hn : a ≠ b then (distinguish_bit hn).choose else ⟨0,Nat.succ_pos _⟩

theorem bitPosition_works {m : ℕ} {a b : Fin m} (hn : a ≠ b) :
    a.val.testBit (bitPosition a b).val ≠ b.val.testBit (bitPosition a b).val := by
  classical
  unfold bitPosition
  rw [dif_pos hn]
  exact (distinguish_bit hn).choose_spec

noncomputable def tupleCode (d m : ℕ) :
    (Fin d → Fin (binaryWidth m) × Bool) ≃ Fin (bitPalette d m) :=
  (Fintype.equivFin _).trans (finCongr (by simp [bitPalette,Fintype.card_fun,Fintype.card_prod]))

/-- A single recoloring step stores one distinguishing bit and its position per neighbor. -/
noncomputable def bitCompress {m : ℕ} (edge : Fin d → X → X) (q : X → Fin m)
    (x : X) : Fin (bitPalette d m) :=
  tupleCode d m (fun i =>
    let k := bitPosition (q x) (q (edge i x))
    (k,(q x).val.testBit k.val))

theorem bitCompress_proper {m : ℕ} (edge : Fin d → X → X)
    {q : X → Fin m} (h : Proper edge q) : Proper edge (bitCompress edge q) := by
  intro i x he heq
  have htuple := (tupleCode d m).injective heq
  have hi := congrFun htuple i
  have hIdx := congrArg Prod.fst hi
  have hVal := congrArg Prod.snd hi
  have hb := bitPosition_works (h i x he)
  change bitPosition (q x) (q (edge i x)) =
    bitPosition (q (edge i x)) (q (edge i (edge i x))) at hIdx
  change (q x).val.testBit (bitPosition (q x) (q (edge i x))).val =
    (q (edge i x)).val.testBit (bitPosition (q (edge i x)) (q (edge i (edge i x)))).val at hVal
  rw [← hIdx] at hVal
  exact hb hVal

theorem bitCompress_local {m : ℕ} (edge : Fin d → X → X) (edge' : Fin d → Y → Y)
    (q : X → Fin m) (q' : Y → Fin m) (x : X) (y : Y)
    (h : AgreeOnBall edge edge' q q' x y 1) :
    bitCompress edge q x = bitCompress edge' q' y := by
  apply congrArg (tupleCode d m)
  funext i
  have hn := h [i] (by simp)
  change q (edge i x) = q' (edge' i y) at hn
  simp only [h.center,hn]

theorem agree_bitCompress {m r : ℕ} {edge : Fin d → X → X} {edge' : Fin d → Y → Y}
    {q : X → Fin m} {q' : Y → Fin m} {x : X} {y : Y}
    (h : AgreeOnBall edge edge' q q' x y (r+1)) :
    AgreeOnBall edge edge' (bitCompress edge q) (bitCompress edge' q') x y r :=
  fun w hw => bitCompress_local edge edge' q q' _ _
    (h.follow w (Nat.add_le_add_right hw 1))

def compressedRadius (d m : ℕ) := bitPalette d (bitPalette d (bitPalette d m)) + 3

/-- Three bit rounds followed by the finite greedy rule. -/
noncomputable def compress {m : ℕ} (edge : Fin d → X → X) (q : X → Fin m) :
    X → Fin (d+1) :=
  greedyColor edge fun x => (bitCompress edge (bitCompress edge (bitCompress edge q)) x).val

theorem compress_proper {m : ℕ} (edge : Fin d → X → X) (hs : Symmetric edge)
    {q : X → Fin m} (hq : Proper edge q) : Proper edge (compress edge q) := by
  apply greedyColor_proper edge hs
  intro i x hx he
  exact bitCompress_proper _ (bitCompress_proper _ (bitCompress_proper _ hq)) i x hx (Fin.ext he)

theorem compress_local {m : ℕ} (edge : Fin d → X → X) (edge' : Fin d → Y → Y)
    (q : X → Fin m) (q' : Y → Fin m) (x : X) (y : Y)
    (h : AgreeOnBall edge edge' q q' x y (compressedRadius d m)) :
    compress edge q x = compress edge' q' y := by
  let q₃ := bitCompress edge (bitCompress edge (bitCompress edge q))
  let q₃' := bitCompress edge' (bitCompress edge' (bitCompress edge' q'))
  let M := bitPalette d (bitPalette d (bitPalette d m))
  have he : AgreeOnBall edge edge' q₃ q₃' x y M :=
    agree_bitCompress (agree_bitCompress (agree_bitCompress h))
  exact greedyColor_local edge edge' (fun z => (q₃ z).val) (fun z => (q₃' z).val) M x y
    (q₃ x).isLt (fun w hw => congrArg Fin.val (he w hw))

section MeasurableFamilies

variable {A : Type*} [MeasurableSpace A]

theorem bitCompress_measurable_family {m : ℕ} (edge : Fin d → X → X)
    {q : A → X → Fin m} (hq : ∀ x, Measurable (fun a => q a x)) (x : X) :
    Measurable (fun a => bitCompress edge (q a) x) := by
  let f (p : Fin m × Fin m) := (bitPosition p.1 p.2,p.1.val.testBit (bitPosition p.1 p.2).val)
  have hf (i : Fin d) : Measurable (fun a => f (q a x,q a (edge i x))) :=
    (measurable_of_countable f).comp ((hq x).prodMk (hq (edge i x)))
  exact (measurable_of_countable (tupleCode d m)).comp (measurable_pi_lambda _ hf)

theorem greedyColor_measurable_family (edge : Fin d → X → X)
    {q : A → X → ℕ} (hq : ∀ x, Measurable (fun a => q a x)) (x : X) :
    Measurable (fun a => greedyColor edge (q a) x) := by
  classical
  have hs (n : ℕ) (v : X) : Measurable (fun a => greedyState edge (q a) n v) := by
    induction n generalizing v with
    | zero => exact measurable_const
    | succ n ih =>
      have ht : Measurable (fun a i => greedyState edge (q a) n (edge i v)) :=
        measurable_pi_lambda _ (fun i => ih (edge i v))
      exact ((measurable_of_countable freshColor).comp ht).piecewise
        ((hq v) (measurableSet_singleton n)) (ih v)
  have hprod : Measurable (fun p : ℕ × A => greedyState edge (q p.2) (p.1+1) x) :=
    measurable_from_prod_countable_right (fun n => hs (n+1) x)
  exact hprod.comp ((hq x).prodMk measurable_id)

theorem compress_measurable_family {m : ℕ} (edge : Fin d → X → X)
    {q : A → X → Fin m} (hq : ∀ x, Measurable (fun a => q a x)) (x : X) :
    Measurable (fun a => compress edge (q a) x) := by
  apply greedyColor_measurable_family edge _ x
  intro y
  exact (measurable_of_countable Fin.val).comp (bitCompress_measurable_family edge
    (bitCompress_measurable_family edge (bitCompress_measurable_family edge hq)) y)

end MeasurableFamilies

end LocalHirschHyperfinite.FiniteNeighborColoring

end
-- END COMPLETE MODULE HirschProof.PaletteCompression

-- BEGIN COMPLETE MODULE HirschProof.PaletteRadius
section
                                     
                          

set_option autoImplicit false

namespace LocalHirschHyperfinite.FiniteNeighborColoring

private theorem n_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change n + 1 + 1 ≤ 2 ^ (n+1)
    rw [pow_succ]
    omega

private theorem square_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n*n ≤ 2^n := by
  refine Nat.le_induction (by decide) (fun k hk ih => ?_) n hn
  rw [pow_succ]
  have hmul : 3*k ≤ k*k := Nat.mul_le_mul_right k (by omega)
  calc
    (k+1)*(k+1) = k*k+(k+k+1) := by ring
    _ ≤ k*k+k*k := Nat.add_le_add_left (by omega) _
    _ = (k*k)*2 := by ring
    _ ≤ 2^k*2 := Nat.mul_le_mul_right 2 ih

private theorem step_of_exp_bound {m n : ℕ} (d : ℕ) (h : m ≤ 2^n) :
    bitPalette d m ≤ ((n+1)*2)^d := by
  simp only [bitPalette, binaryWidth]
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_right 2
    (Nat.add_le_add_right (Nat.clog_le_of_le_pow h) 1)) _

private theorem twice_power_succ (n : ℕ) : (2^n + 1)*2 ≤ 2^(n+2) := by
  have hpos : 0 < 2^n := by positivity
  rw [pow_add]
  change (2^n+1)*2 ≤ 2^n*4
  omega

set_option maxHeartbeats 1500000 in
/-- The local rule reads fewer than R+1 layers of the chart for a suitable
radius R whenever the initial palettes have a uniform double-exponential bound. -/
theorem exists_radius_for_double_exp (d b : ℕ) (M : ℕ → ℕ)
    (hM : ∀ R, M R ≤ 2^(2^(b*(R+1)))) :
    ∃ R : ℕ, compressedRadius d (M R) ≤ R := by
  let B₀ := 2*b+2
  let B₁ := (d*B₀+1)*2
  let B₂ := (d*(B₁+1)+1)*2
  let a := 4*(d+B₂+2)
  let t := 2^a
  let R := 2^t
  have ht : 1 ≤ t := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < (2 : ℕ)))
  have hR : 1 ≤ R := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < (2 : ℕ)))
  let L := b*(R+1)
  have hL : L+2 ≤ B₀*R := by
    dsimp [L,B₀]
    calc
      b*(R+1)+2 ≤ b*(R+R)+2*R :=
        Nat.add_le_add (Nat.mul_le_mul_left b (by omega)) (by omega)
      _ = (2*b+2)*R := by ring
  have h₁ : bitPalette d (M R) ≤ 2^(d*(L+2)) := by
    calc
      _ ≤ ((2^L+1)*2)^d := step_of_exp_bound d (hM R)
      _ ≤ (2^(L+2))^d := Nat.pow_le_pow_left (twice_power_succ L) _
      _ = 2^(d*(L+2)) := by rw [← pow_mul, Nat.mul_comm (L+2) d]
  have h₁a : (d*(L+2)+1)*2 ≤ 2^(B₁+t) := by
    calc
      _ ≤ (d*(B₀*R)+R)*2 :=
        Nat.mul_le_mul_right 2 (Nat.add_le_add (Nat.mul_le_mul_left d hL) hR)
      _ = B₁*R := by dsimp [B₁]; ring
      _ ≤ 2^B₁*2^t := Nat.mul_le_mul ((n_le_two_pow _).trans' (Nat.le_succ _)) le_rfl
      _ = _ := (pow_add _ _ _).symm
  have h₂ : bitPalette d (bitPalette d (M R)) ≤ 2^(d*(B₁+t)) := by
    calc
      _ ≤ ((d*(L+2)+1)*2)^d := step_of_exp_bound d h₁
      _ ≤ (2^(B₁+t))^d := Nat.pow_le_pow_left h₁a _
      _ = 2^(d*(B₁+t)) := by rw [← pow_mul, Nat.mul_comm (B₁+t) d]
  have h₂a : (d*(B₁+t)+1)*2 ≤ 2^(B₂+a) := by
    have hbt : B₁+t ≤ (B₁+1)*t := by
      have hh := Nat.mul_le_mul_left B₁ ht
      rw [Nat.mul_one] at hh
      rw [Nat.add_mul, one_mul]
      omega
    calc
      _ ≤ (d*((B₁+1)*t)+t)*2 :=
        Nat.mul_le_mul_right 2 (Nat.add_le_add (Nat.mul_le_mul_left d hbt) ht)
      _ = B₂*t := by dsimp [B₂]; ring
      _ ≤ 2^B₂*2^a := Nat.mul_le_mul ((n_le_two_pow _).trans' (Nat.le_succ _)) le_rfl
      _ = _ := (pow_add _ _ _).symm
  have h₃ : bitPalette d (bitPalette d (bitPalette d (M R))) ≤ 2^(d*(B₂+a)) := by
    calc
      _ ≤ ((d*(B₁+t)+1)*2)^d := step_of_exp_bound d h₂
      _ ≤ (2^(B₂+a))^d := Nat.pow_le_pow_left h₂a _
      _ = 2^(d*(B₂+a)) := by rw [← pow_mul, Nat.mul_comm (B₂+a) d]
  have ha : d*(B₂+a)+2 ≤ t := by
    have hd : d+d+1 ≤ a := by dsimp [a]; omega
    have hb : B₂ ≤ a := by dsimp [a]; omega
    have ha₂ : 2 ≤ a := by dsimp [a]; omega
    have ha₄ : 4 ≤ a := by dsimp [a]; omega
    calc
      d*(B₂+a)+2 ≤ d*(a+a)+a :=
        Nat.add_le_add (Nat.mul_le_mul_left d (Nat.add_le_add_right hb _)) ha₂
      _ = (d+d+1)*a := by ring
      _ ≤ a*a := Nat.mul_le_mul_right a hd
      _ ≤ t := square_le_two_pow ha₄
  refine ⟨R,?_⟩
  let n := d*(B₂+a)
  have hplus : 2^n+3 ≤ 2^(n+2) := by
    have hpos : 0 < 2^n := by positivity
    rw [pow_add]
    change 2^n+3 ≤ 2^n*4
    omega
  calc
    compressedRadius d (M R) ≤ 2^n+3 := Nat.add_le_add_right h₃ _
    _ ≤ 2^(n+2) := hplus
    _ ≤ R := Nat.pow_le_pow_right (by decide) ha

end LocalHirschHyperfinite.FiniteNeighborColoring

end
-- END COMPLETE MODULE HirschProof.PaletteRadius

-- BEGIN COMPLETE MODULE HirschProof.RadicalCompression
section
                                
                                 

set_option autoImplicit false

namespace LocalHirschHyperfinite
open FiniteNeighborColoring
open scoped Pointwise

variable {H X : Type*} [Group H] [MulAction H X] [MeasurableSpace X]

theorem wordBall_prepend_mem (S : Finset H) {a b : H} (ha : a ∈ S) {n : ℕ}
    (hb : b ∈ wordBall S n) : a*b ∈ wordBall S (n+1) := by
  classical
  induction n generalizing b with
  | zero =>
    have he : b = 1 := Finset.mem_singleton.mp hb
    rw [he,mul_one,← one_mul a]
    exact wordBall_append_mem S (one_mem_wordBall S 0) ha
  | succ n ih =>
    change b ∈ wordBall S n ∪ wordBall S n * S at hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact wordBall_mono S (Nat.le_succ _) (ih hb)
    · obtain ⟨u,hu,v,hv,rfl⟩ := Finset.mem_mul.mp hb
      rw [← mul_assoc]
      exact wordBall_append_mem S (ih hu) hv

private theorem follow_left_mul_right {d : ℕ} (g : Fin d → H) (w : List (Fin d)) (a b : H) :
    follow (fun i x => g i*x) w (a*b) = follow (fun i x => g i*x) w a * b := by
  induction w generalizing a with
  | nil => rfl
  | cons i w ih =>
    change follow (fun i x => g i*x) w (g i*(a*b)) =
      follow (fun i x => g i*x) w (g i*a) * b
    rw [← mul_assoc,ih]

private theorem follow_wordBall {d : ℕ} (S : Finset H) (g : Fin d → H)
    (hg : ∀ i, g i ∈ S) (w : List (Fin d)) {n : ℕ} {a : H}
    (ha : a ∈ wordBall S n) :
    follow (fun i x => g i*x) w a ∈ wordBall S (n+w.length) := by
  induction w generalizing n a with
  | nil => exact ha
  | cons i w ih =>
    have h := ih (wordBall_prepend_mem S (hg i) ha)
    change follow (fun i x => g i*x) w (g i*a) ∈ wordBall S (n+(w.length+1))
    rwa [show n+(w.length+1) = n+1+w.length by omega]

/-- A local compression rule converts proper colors invariant under a bounded
conjugacy window to a palette uniform over the size of the kernel orbits. -/
theorem exists_radical_compressed_palette (S : Finset H) (hS : SymmetricMoves S)
    (hS₀ : (1 : H) ∉ S) (B : Subgroup H) (hact : BorelAction H X)
    (M : ℕ → ℕ) (b : ℕ) (hGrowth : ∀ R, M R ≤ 2^(2^(b*(R+1))))
    (hApprox : ∀ R, ∃ q : X → Fin (M R), Measurable q ∧
      (∀ c ∈ S, ∀ x, q x ≠ q (c • x)) ∧
      (∀ w ∈ wordBall S (R+1), ∀ a ∈ B, ∀ x, q ((w*a*w⁻¹) • x) = q x)) :
    ∃ q : X → Fin (S.card+1), Measurable q ∧
      ∀ c ∈ S, ∀ a ∈ B, ∀ x, q x ≠ q ((c*a) • x) := by
  classical
  obtain ⟨R,hR⟩ := exists_radius_for_double_exp S.card b M hGrowth
  obtain ⟨p,hp,hproper,hInv⟩ := hApprox R
  let e : Fin S.card ≃ ↥S :=
    (finCongr (Fintype.card_coe S).symm).trans (Fintype.equivFin ↥S).symm
  let g (i : Fin S.card) : H := (e i).val
  have hg (i : Fin S.card) : g i ∈ S := (e i).prop
  let edge (i : Fin S.card) (w : H) := g i*w
  have he : Symmetric edge := by
    intro i w _
    obtain ⟨j,hj⟩ := e.surjective ⟨(g i)⁻¹,hS (hg i)⟩
    have hj' : g j = (g i)⁻¹ := congrArg Subtype.val hj
    exact ⟨j,by change g j*(g i*w)=w; rw [hj',inv_mul_cancel_left]⟩
  let q (x : X) (w : H) := p (w • x)
  have hq (w : H) : Measurable (fun x => q x w) := hp.comp (hact w)
  have hqProper (x : X) : Proper edge (q x) := by
    intro i w _
    change p (w • x) ≠ p ((g i*w) • x)
    rw [mul_smul]
    exact hproper _ (hg i) _
  let color (x : X) := compress edge (q x) 1
  refine ⟨color,compress_measurable_family edge hq 1,?_⟩
  intro c hc a ha x
  obtain ⟨j,hj⟩ := e.surjective ⟨c,hc⟩
  have hgc : g j = c := congrArg Subtype.val hj
  have hcj : edge j 1 = c := by change g j*1=c; rw [mul_one,hgc]
  have hd : edge j 1 ≠ 1 := hcj ▸ fun h => hS₀ (h ▸ hc)
  have hComp := compress_proper edge he (hqProper x) j 1 hd
  have hObs : AgreeOnBall edge edge (q ((c*a) • x)) (q x) 1 c
      (compressedRadius S.card (M R)) := by
    intro w hw
    let y := follow edge w c
    have hy : y = follow edge w 1 * c := by
      simpa only [one_mul] using follow_left_mul_right g w 1 c
    have hcBall : c ∈ wordBall S 1 := by
      rw [← one_mul c]
      exact wordBall_append_mem S (one_mem_wordBall S 0) hc
    have hyBall : y ∈ wordBall S (R+1) :=
      wordBall_mono S (by have := hw.trans hR; omega) (follow_wordBall S g hg w hcBall)
    change p (follow edge w 1 • ((c*a) • x)) = p (y • x)
    rw [← mul_smul, ← mul_assoc, ← hy]
    have hE := hInv y hyBall a ha (y • x)
    rwa [← mul_smul, mul_assoc y a y⁻¹, mul_assoc y (a*y⁻¹) y,
      mul_assoc a y⁻¹ y, inv_mul_cancel, mul_one] at hE
  have hh := compress_local edge edge _ _ _ _ hObs
  change compress edge (q x) 1 ≠ compress edge (q ((c*a) • x)) 1
  rw [hh,← hcj]
  exact hComp

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.RadicalCompression

-- BEGIN COMPLETE MODULE HirschProof.TaggedSupportBounds
section
                                  
                                  
                                     

set_option autoImplicit false

open scoped Pointwise

namespace LocalHirschHyperfinite

theorem wordBall_succ_cases {G : Type*} [Group G] {A : Finset G} {r : ℕ} {w : G}
    (hw : w ∈ wordBall A (r+1)) :
    w ∈ wordBall A r ∨ ∃ u ∈ wordBall A r, ∃ v ∈ A, u * v = w := by
  classical
  rcases Finset.mem_union.mp hw with hw | hw
  · exact Or.inl hw
  · exact Or.inr (Finset.mem_mul.mp hw)

theorem wordBall_mul_mem {G : Type*} [Group G] (A : Finset G)
    {a b : G} {r s : ℕ} (ha : a ∈ wordBall A r) (hb : b ∈ wordBall A s) :
    a * b ∈ wordBall A (r + s) := by
  classical
  induction s generalizing b with
  | zero =>
      have hb' : b = 1 := by simpa [wordBall] using hb
      simpa [hb'] using ha
  | succ s ih =>
      rcases Finset.mem_union.mp hb with hb | hb
      · exact wordBall_mono A (Nat.le_succ _) (ih hb)
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp hb
      simpa only [mul_assoc] using wordBall_append_mem A (ih hu) hv

theorem wordBall_inv_mem {G : Type*} [Group G] (A : Finset G)
    (hA : SymmetricMoves A) {w : G} {r : ℕ} (hw : w ∈ wordBall A r) :
    w⁻¹ ∈ wordBall A r := by
  classical
  induction r generalizing w with
  | zero =>
      have hw' : w = 1 := by simpa [wordBall] using hw
      simp [hw', wordBall]
  | succ r ih =>
      rcases Finset.mem_union.mp hw with hw | hw
      · exact wordBall_mono A (Nat.le_succ _) (ih hw)
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp hw
      rw [mul_inv_rev]
      exact wordBall_prepend_mem A (hA hv) (ih hu)

namespace TaggedSpace

variable {G Γ X : Type*} [Group G] [Group Γ] [MulAction G X]
variable {Z : Set X} {q : G →* Γ}

abbrev tag (x : TaggedSpace Z Γ) : Γ := x.2.1

/-- Pointwise stabilizer of the points whose tags are outside the given set. -/
def supportedPerm (Z : Set X) (T : Set Γ) : Subgroup (Equiv.Perm (TaggedSpace Z Γ)) where
  carrier := {σ | ∀ x : TaggedSpace Z Γ, tag x ∉ T → σ x = x}
  one_mem' _ _ := rfl
  mul_mem' hσ hτ x hx := by
    rw [Equiv.Perm.mul_apply, hτ x hx, hσ x hx]
  inv_mem' {σ} hσ x hx := by
    apply σ.injective
    change σ (σ.symm x) = σ x
    rw [σ.apply_symm_apply, hσ x hx]

omit [Group Γ] in
theorem supportedPerm_mono {A B : Set Γ} (h : A ⊆ B) :
    supportedPerm Z A ≤ supportedPerm Z B := fun _ hσ x hx => hσ x (fun ha => hx (h ha))

theorem supportedPerm_preserves {T : Set Γ} {σ : Equiv.Perm (TaggedSpace Z Γ)}
    (hσ : σ ∈ supportedPerm Z T) (x : TaggedSpace Z Γ) :
    tag (σ x) ∈ T ↔ tag x ∈ T := by
  constructor
  · intro hout
    by_contra hx
    exact hx (hσ x hx ▸ hout)
  · intro hx
    by_contra hout
    have hfix := (supportedPerm Z T).inv_mem hσ (σ x) hout
    change σ.symm (σ x) = σ x at hfix
    rw [σ.symm_apply_apply] at hfix
    exact hout (hfix ▸ hx)

theorem switch_support (g : G) (t : Γ) :
    switch Z q g t ∈ supportedPerm Z ({t, q g * t} : Set Γ) := by
  classical
  intro x hx
  change switchFun Z q g t x = x
  have hF : ¬ switchForward Z g t x := fun h => hx (by simp [h.1])
  have hB : ¬ switchBackward Z q g t x := fun h => hx (by simp [h.1])
  simp [switchFun, hF, hB]

/-- Every finite switch-group word is the identity outside finitely many tags. -/
theorem switchGroup_finite_support {σ : Equiv.Perm (TaggedSpace Z Γ)}
    (hσ : σ ∈ switchGroup Z q) :
    ∃ T : Finset Γ, σ ∈ supportedPerm Z (T : Set Γ) := by
  classical
  change σ ∈ Subgroup.closure (switchGenerators Z q) at hσ
  induction hσ using Subgroup.closure_induction with
  | mem σ hσ =>
      obtain ⟨g,t,rfl⟩ := hσ
      exact ⟨{t, q g * t}, by simpa using switch_support (Z := Z) (q := q) g t⟩
  | one => exact ⟨∅, (supportedPerm Z _).one_mem⟩
  | mul σ τ _ _ hσ hτ =>
      obtain ⟨A,hA⟩ := hσ
      obtain ⟨B,hB⟩ := hτ
      refine ⟨A ∪ B, (supportedPerm Z (↑(A ∪ B) : Set Γ)).mul_mem ?_ ?_⟩
      · exact supportedPerm_mono (fun _ hx => Finset.mem_union_left _ hx) hA
      · exact supportedPerm_mono (fun _ hx => Finset.mem_union_right _ hx) hB
  | inv σ _ hσ =>
      obtain ⟨T,hT⟩ := hσ
      exact ⟨T,(supportedPerm Z (T : Set Γ)).inv_mem hT⟩

/-- Degree of tag transport under one letter, with a subsequent bound for words. -/
def TracksTags (T : Finset Γ) (a : taggedExtension Z q) : Prop :=
  ∀ (s : ℕ) (x : TaggedSpace Z Γ), tag x ∈ wordBall T s →
    tag (a • x) ∈ wordBall T (s + 2)

theorem tracksTags_of_finiteTransport {T : Finset Γ} {a : taggedExtension Z q}
    (ha : ∀ x : TaggedSpace Z Γ, ∃ g : G, q g ∈ T ∧
      tag (a • x) = q g * tag x * (taggedProjection Z q a)⁻¹)
    (hv : (taggedProjection Z q a)⁻¹ ∈ T) : TracksTags T a := by
  intro s x hx
  obtain ⟨g, hg, he⟩ := ha x
  rw [he]
  exact wordBall_append_mem T (wordBall_prepend_mem T hg hx) hv

theorem tag_word_mem {T : Finset Γ} {S : Finset (taggedExtension Z q)}
    (hS : ∀ a ∈ S, TracksTags T a) {w : taggedExtension Z q} {r s : ℕ}
    (hw : w ∈ wordBall S r) {x : TaggedSpace Z Γ} (hx : tag x ∈ wordBall T s) :
    tag (w • x) ∈ wordBall T (s + 2*r) := by
  classical
  induction r generalizing w s x with
  | zero =>
      have h : w = 1 := by simpa [wordBall] using hw
      simpa [h] using hx
  | succ r ih =>
      rcases wordBall_succ_cases hw with hw | ⟨u,hu,v,hv,rfl⟩
      · exact wordBall_mono T (by omega : s + 2*r ≤ s + 2*(r+1)) (ih hw hx)
      rw [mul_smul, show s + 2*(r+1) = (s+2) + 2*r by omega]
      exact ih hu (hS v hv s x hx)

theorem conjugateGroup_supported {T : Finset Γ} {S B : Finset (taggedExtension Z q)}
    (hS : ∀ a ∈ S, TracksTags T a)
    (s r : ℕ) (hB : ∀ b ∈ B, taggedPerm Z q b ∈
      supportedPerm Z (↑(wordBall T s) : Set Γ)) :
    conjugateGroup S B r ≤ (supportedPerm Z (↑(wordBall T (s + 2*r)) : Set Γ)).comap
      (taggedPerm Z q) := by
  apply (Subgroup.closure_le _).2
  rintro _ ⟨⟨w,b⟩,rfl⟩ x hx
  change (w.val * b.val * w.val⁻¹) • x = x
  have hOut : tag (w.val⁻¹ • x) ∉ wordBall T s := by
    intro hin
    have h := tag_word_mem hS w.property hin
    exact hx (by simpa using h)
  have hFix : b.val • (w.val⁻¹ • x) = w.val⁻¹ • x := hB b.val b.property _ hOut
  simp only [mul_smul, hFix, smul_inv_smul]

/-- A branch of a conjugate subgroup followed by one middle move and another
conjugate subgroup is the pure right translation unless both endpoint tags
lie in one enlarged word ball. -/
theorem double_move_support {T : Finset Γ} {S B : Finset (taggedExtension Z q)}
    (hSym : SymmetricMoves S) (hS : ∀ a ∈ S, TracksTags T a) (s r : ℕ)
    (hB : ∀ b ∈ B, taggedPerm Z q b ∈ supportedPerm Z (↑(wordBall T s) : Set Γ))
    (hMid : ∀ a ∈ S, ∀ x : TaggedSpace Z Γ,
      tag x ∉ wordBall T s → a • x = rightTag Z (taggedProjection Z q a) x)
    {a l d : taggedExtension Z q} (ha : a ∈ S)
    (hl : l ∈ conjugateGroup S B r) (hd : d ∈ conjugateGroup S B r)
    (x : TaggedSpace Z Γ)
    (hne : (l * a * d) • x ≠ rightTag Z (taggedProjection Z q a) x) :
    tag x ∈ wordBall T (s + 2*r + 2) ∧
      tag ((l * a * d) • x) ∈ wordBall T (s + 2*r + 2) := by
  let F := wordBall T (s + 2*r)
  have hFle : F ⊆ wordBall T (s + 2*r + 2) := wordBall_mono T (by omega)
  have hleF : wordBall T s ⊆ F := wordBall_mono T (by omega)
  have hL : taggedPerm Z q l ∈ supportedPerm Z (F : Set Γ) :=
    conjugateGroup_supported hS s r hB hl
  have hD : taggedPerm Z q d ∈ supportedPerm Z (F : Set Γ) :=
    conjugateGroup_supported hS s r hB hd
  have hDout (y : TaggedSpace Z Γ) (hy : tag y ∈ wordBall T (s + 2*r + 2)) :
      tag (l • y) ∈ wordBall T (s + 2*r + 2) := by
    by_cases hin : tag y ∈ F
    · exact hFle ((supportedPerm_preserves hL y).mpr hin)
    · have he : l • y = y := hL y hin
      rwa [he]
  have hTransport (y : TaggedSpace Z Γ) (hy : tag y ∈ F) :
      tag (a • y) ∈ wordBall T (s + 2*r + 2) := hS a ha _ y hy
  have hBack (y : TaggedSpace Z Γ) (hy : tag (a • y) ∈ F) :
      tag y ∈ wordBall T (s + 2*r + 2) := by
    have h := hS a⁻¹ (hSym ha) (s+2*r) (a • y) hy
    simpa using h
  simp only [mul_smul] at hne ⊢
  by_cases hx : tag x ∈ F
  · exact ⟨hFle hx, hDout _ (hTransport _ ((supportedPerm_preserves hD x).mpr hx))⟩
  have heD : d • x = x := hD x hx
  rw [heD] at hne ⊢
  by_cases hy : tag (a • x) ∈ F
  · exact ⟨hBack _ hy, hDout _ (hFle hy)⟩
  have heL : l • (a • x) = a • x := hL _ hy
  rw [heL] at hne
  exact (hne (hMid a ha x (fun ht => hx (hleF ht)))).elim

/-- One finite physical alphabet suffices for the branches of every letter
in a finite tagged alphabet. -/
theorem exists_transport_alphabet (A : Finset (taggedExtension Z q)) :
    ∃ P : Finset G, ∀ a ∈ A, ∀ x : TaggedSpace Z Γ, ∃ g ∈ P,
      (a • x).1.val = g • x.1.val ∧
      tag (a • x) = q g * tag x * (taggedProjection Z q a)⁻¹ := by
  classical
  choose P hP using fun a : A => finiteTransport_tagged Z q a.val
  refine ⟨A.attach.biUnion P, fun a ha x => ?_⟩
  obtain ⟨g,hg,he,ht⟩ := hP ⟨a,ha⟩ x
  exact ⟨g,Finset.mem_biUnion.mpr ⟨⟨a,ha⟩,Finset.mem_attach _ _,hg⟩,he,ht⟩

/-- A short permutation word has a physical label that is a word of at
most the same length in the finite physical alphabet. -/
theorem physical_word_transport {A : Finset (taggedExtension Z q)} {P : Finset G}
    (hA : ∀ a ∈ A, ∀ x : TaggedSpace Z Γ, ∃ g ∈ P,
      (a • x).1.val = g • x.1.val ∧
      tag (a • x) = q g * tag x * (taggedProjection Z q a)⁻¹)
    (r : ℕ) {w : taggedExtension Z q} (hw : w ∈ wordBall A r) (x : TaggedSpace Z Γ) :
    ∃ g ∈ wordBall P r, (w • x).1.val = g • x.1.val ∧
      tag (w • x) = q g * tag x * (taggedProjection Z q w)⁻¹ := by
  classical
  induction r generalizing w x with
  | zero =>
      have he : w = 1 := by simpa [wordBall] using hw
      subst w
      exact ⟨1,one_mem_wordBall P 0,by simp,by simp⟩
  | succ r ih =>
      rcases wordBall_succ_cases hw with hw | ⟨u,hu,a,ha,rfl⟩
      · obtain ⟨g,hg,hp,ht⟩ := ih hw x
        exact ⟨g, wordBall_mono P (Nat.le_succ _) hg,hp,ht⟩
      obtain ⟨g,hg,hp,ht⟩ := ih hu (a • x)
      obtain ⟨b,hb,hpb,htb⟩ := hA a ha x
      refine ⟨g*b,wordBall_append_mem P hg hb, ?_, ?_⟩
      · rw [mul_smul,hp,hpb,mul_smul]
      · rw [mul_smul,ht,htb,map_mul,map_mul,mul_inv_rev]
        group

theorem kernel_finite_support {b : taggedExtension Z q} (hb : taggedProjection Z q b = 1) :
    ∃ T : Finset Γ, taggedPerm Z q b ∈ supportedPerm Z (T : Set Γ) := by
  obtain ⟨σ,hσ,he⟩ := tagged_permutation_decomposition Z q b
  change b.val.2 = 1 at hb
  simp only [hb,rightTag_one,mul_one] at he
  change ∃ T : Finset Γ, b.val.1 ∈ supportedPerm Z (T : Set Γ)
  rw [he]
  exact switchGroup_finite_support hσ

theorem pure_outside_finite_support (a : taggedExtension Z q) :
    ∃ T : Finset Γ, ∀ x : TaggedSpace Z Γ, tag x ∉ T →
      a • x = rightTag Z (taggedProjection Z q a) x := by
  classical
  obtain ⟨σ,hσ,he⟩ := tagged_permutation_decomposition Z q a
  obtain ⟨T,hT⟩ := switchGroup_finite_support hσ
  refine ⟨T.image (fun t => t * taggedProjection Z q a),fun x hx => ?_⟩
  have hout : tag (rightTag Z (taggedProjection Z q a) x) ∉ T := by
    intro h
    exact hx (Finset.mem_image.mpr ⟨_,h,by simp [rightTag,tag,mul_assoc]⟩)
  change a.val.1 x = rightTag Z a.val.2 x
  rw [he,Equiv.Perm.mul_apply]
  exact hT _ hout

/-- The physical and tag alphabets used to control all conjugated generators
and all exceptional double moves at once. -/
theorem exists_finite_tagSupport_alphabet (S B : Finset (taggedExtension Z q))
    (hB : ∀ b ∈ B, taggedProjection Z q b = 1) :
    ∃ (P : Finset G) (T : Finset Γ),
      (∀ a, a ∈ S ∨ a ∈ B → ∀ x : TaggedSpace Z Γ, ∃ g ∈ P,
        (a • x).1.val = g • x.1.val ∧
        tag (a • x) = q g * tag x * (taggedProjection Z q a)⁻¹) ∧
      (∀ p ∈ P, q p ∈ T) ∧
      (∀ a ∈ S, (taggedProjection Z q a)⁻¹ ∈ T) ∧
      (∀ a ∈ S, TracksTags T a) ∧
      (∀ b ∈ B, taggedPerm Z q b ∈ supportedPerm Z (↑(wordBall T 1) : Set Γ)) ∧
      (∀ a ∈ S, ∀ x : TaggedSpace Z Γ, tag x ∉ wordBall T 1 →
        a • x = rightTag Z (taggedProjection Z q a) x) := by
  classical
  obtain ⟨P,hP⟩ := exists_transport_alphabet (S ∪ B)
  choose Bsup hBsup using fun b : B => kernel_finite_support (hB b.val b.property)
  choose Ssup hSsup using fun a : S => pure_outside_finite_support a.val
  let T : Finset Γ :=
    ((P.image q ∪ S.image (fun a => (taggedProjection Z q a)⁻¹)) ∪ B.attach.biUnion Bsup) ∪
      S.attach.biUnion Ssup
  have h₁ (p : G) (hp : p ∈ P) : q p ∈ T :=
    Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)))
  have h₂ (a : taggedExtension Z q) (ha : a ∈ S) : (taggedProjection Z q a)⁻¹ ∈ T :=
    Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)))
  have h₃ (b : B) {t : Γ} (ht : t ∈ Bsup b) : t ∈ wordBall T 1 := by
    have he : t ∈ T := Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨b, Finset.mem_attach _ _, ht⟩))
    simpa using wordBall_append_mem T (one_mem_wordBall T 0) he
  have h₄ (a : S) {t : Γ} (ht : t ∈ Ssup a) : t ∈ wordBall T 1 := by
    have he : t ∈ T := Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨a, Finset.mem_attach _ _, ht⟩)
    simpa using wordBall_append_mem T (one_mem_wordBall T 0) he
  refine ⟨P,T,fun a ha => hP a (Finset.mem_union.mpr ha),h₁,h₂,?_,?_,?_⟩
  · intro a ha
    apply tracksTags_of_finiteTransport (hv := h₂ a ha)
    intro x
    obtain ⟨g,hg,_,ht⟩ := hP a (Finset.mem_union_left _ ha) x
    exact ⟨g,h₁ g hg,ht⟩
  · exact fun b hb => supportedPerm_mono (fun _ ht => h₃ ⟨b,hb⟩ ht) (hBsup ⟨b,hb⟩)
  · exact fun a ha x hx => hSsup ⟨a,ha⟩ x (fun ht => hx (h₄ ⟨a,ha⟩ ht))

end TaggedSpace

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.TaggedSupportBounds

-- BEGIN COMPLETE MODULE HirschProof.TaggedOrbits
section
                                  
                                       
                            

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

variable {G X Y W A : Type*} [Group G] [MulAction G X]

/-- A finite set of tags and locally finite normalized displacements bounds path orbits. -/
theorem uniform_finite_path_orbits_of_lifts [Finite A]
    (edge : Y → Y → Prop) (ι : Y ↪ W) (recover : A → X → W)
    (U : Set Y) (L : Subgroup G) (hL : IsLocallyFiniteGroup L) (S : Finset L)
    (outside : ∀ y z, y ∉ U → edge y z → z = y)
    (cover : ∀ y ∈ U, ∃ a x, ι y = recover a x)
    (transport : ∀ y z, y ∈ U → edge y z → ∀ a x, ι y = recover a x →
      z ∈ U ∧ ∃ (a' : A) (l : L), l ∈ S ∧ ι z = recover a' (l.val • x)) :
    ∃ N : ℕ, ∀ y : Y, ({z | Relation.ReflTransGen edge y z} : Set Y).Finite ∧
      ({z | Relation.ReflTransGen edge y z} : Set Y).ncard ≤ N := by
  classical
  let K := Subgroup.closure (S : Set L)
  letI : Finite K := hL K ⟨S,rfl⟩
  let N := max 1 (Nat.card (A × K))
  refine ⟨N,fun y => ?_⟩
  by_cases hy : y ∈ U
  · obtain ⟨a,x,hyx⟩ := cover y hy
    have walk {z : Y} (h : Relation.ReflTransGen edge y z) :
        z ∈ U ∧ ∃ (a' : A) (g : K), ι z = recover a' (g.val.val • x) := by
      induction h with
      | refl => exact ⟨hy,a,1,by simpa using hyx⟩
      | @tail u v hu huv ih =>
        obtain ⟨hU,a',g,hu⟩ := ih
        obtain ⟨hv,a'',l,hl,hv'⟩ := transport u v hU huv a' (g.val.val • x) hu
        let lK : K := ⟨l,Subgroup.subset_closure hl⟩
        exact ⟨hv,a'',lK*g,by simpa [lK,mul_smul] using hv'⟩
    let f (p : A × K) := recover p.1 (p.2.val.val • x)
    have hs : {z | Relation.ReflTransGen edge y z} ⊆ ι ⁻¹' Set.range f := by
      intro z hz
      obtain ⟨_,a',g,h⟩ := walk hz
      exact ⟨(a',g),h.symm⟩
    have hfin : (Set.range f).Finite := Set.finite_range f
    refine ⟨(hfin.preimage ι.injective.injOn).subset hs,?_⟩
    have hbound := Set.ncard_le_ncard_of_injOn ι
      (s := {z | Relation.ReflTransGen edge y z}) (t := Set.range f) hs ι.injective.injOn hfin
    have hb : (Set.range f).ncard ≤ Nat.card (A × K) := by
      rw [← image_univ, ← ncard_univ (A × K)]
      exact Set.ncard_image_le
    exact hbound.trans (hb.trans (le_max_right _ _))
  · have heq : {z | Relation.ReflTransGen edge y z} = ({y} : Set Y) := by
      ext z
      constructor
      · intro hz
        change Relation.ReflTransGen edge y z at hz
        induction hz with
        | refl => rfl
        | @tail u v hu huv ih =>
          have huv' : edge y v := (mem_singleton_iff.mp ih) ▸ huv
          exact outside y v hy huv'
      · intro hz
        obtain rfl := mem_singleton_iff.mp hz
        exact .refl
    rw [heq]
    exact ⟨finite_singleton _,by simp [N]⟩

theorem normalized_move_of_stabilizer
    {Q : Type*} [Group Q] (π : G →* Q) (D : Subgroup G) {x : X}
    (hD : ∀ d ∈ D, d • x = x) {g : G} (hg : π g ∈ D.map π) :
    ∃ l : π.ker, g • x = l.val • x := by
  obtain ⟨d,hd,he⟩ := hg
  have hl : g*d⁻¹ ∈ π.ker := by change π (g*d⁻¹) = 1; simp [← he]
  refine ⟨⟨g*d⁻¹,hl⟩,?_⟩
  change g • x = (g*d⁻¹) • x
  rw [mul_smul,hD _ (D.inv_mem hd)]

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.TaggedOrbits

-- BEGIN COMPLETE MODULE HirschProof.TaggedCosetOrbits
section
                               
                                              

set_option autoImplicit false

namespace LocalHirschHyperfinite.TaggedSpace
open Set

variable {G Γ X Q : Type*} [Group G] [Group Γ] [Group Q] [MulAction G X]

/-- Directed physical branches for a finite set of switches. The relation also
retains the identity moves of switches outside the working tags. -/
def finiteBranch (Z : Set X) (q : G →* Γ) (T : Finset Γ) (P : Finset G)
    (x y : TaggedSpace Z Γ) : Prop := x = y ∨
  (x.2.1 ∈ T ∧ y.2.1 ∈ T ∧ ∃ g ∈ P,
    q g * x.2.1 = y.2.1 ∧ g • x.1.val = y.1.val)

private theorem mem_insert_image_univ {A B : Type*} [Fintype A] [DecidableEq B]
    (base : B) (f : A → B) (a : A) : f a ∈ insert base (Finset.univ.image f) :=
  Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)

set_option maxHeartbeats 2000000 in
/-- The coset normalization argument for finite collections of tagged branches. -/
theorem bounded_orbits_of_finite_coset_lifts (Z : Set X) (q : G →* Γ) (π : G →* Q)
    (T : Finset Γ) (P : Finset G) (s : Γ → G) (J : Subgroup G)
    (N : Subgroup J) [N.Normal] [N.FiniteIndex]
    (hj : ∀ t ∈ T, ∀ u ∈ T, ∀ g ∈ P, q g*t=u → (s u)⁻¹*g*s t ∈ J)
    (hfix : ∀ t ∈ T, ∀ k : J, k ∈ N → ∃ d : G,
        π d = π k.val ∧ ∀ x : Z, d • ((s t)⁻¹ • x.val) = (s t)⁻¹ • x.val)
    (hL : IsLocallyFiniteGroup π.ker) :
    ∃ B : ℕ, ∀ x : TaggedSpace Z Γ,
      {y | Relation.ReflTransGen (finiteBranch Z q T P) x y}.Finite ∧
      {y | Relation.ReflTransGen (finiteBranch Z q T P) x y}.ncard ≤ B := by
  classical
  let C := J ⧸ N
  let proj : J →* C := QuotientGroup.mk' N
  obtain ⟨repr,hrepr⟩ := (QuotientGroup.mk'_surjective N).hasRightInverse
  let idx : Type _ := {a : ((↑T : Type _) × (↑T : Type _) × (↑P : Type _)) //
    q a.2.2.val * a.1.val = a.2.1.val}
  let delta (a : idx) : J := ⟨(s a.val.2.1.val)⁻¹*a.val.2.2.val*s a.val.1.val,
    hj _ a.val.1.property _ a.val.2.1.property _ a.val.2.2.property a.property⟩
  let next (a : idx) (c : C) : C := proj (delta a)*c
  let residual (a : idx) (c : C) : J := (repr (next a c))⁻¹ * delta a * repr c
  have hres (a : idx) (c : C) : residual a c ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change proj (residual a c) = 1
    simp only [residual,map_mul,map_inv,show ∀ v, proj (repr v) = v from hrepr,next]
    group
  let rotate (c : C) (k : J) := repr c*k*(repr c)⁻¹
  have hrot (c : C) (k : J) (hk : k ∈ N) : rotate c k ∈ N :=
    ‹N.Normal›.conj_mem k hk (repr c)
  have hchoice (a : idx) (c : C) := hfix _ a.val.1.property
    (rotate c (residual a c)) (hrot c (residual a c) (hres a c))
  choose d hdEq hdFix using hchoice
  let normalizedFix (a : idx) (c : C) : G := (repr c).val⁻¹*d a c*(repr c).val
  let correction (a : idx) (c : C) : π.ker := ⟨(residual a c).val*(normalizedFix a c)⁻¹, by
    change π ((residual a c).val*(normalizedFix a c)⁻¹) = 1
    rw [map_mul,map_inv]
    simp only [normalizedFix,map_mul,map_inv,hdEq,rotate,Subgroup.coe_mul,Subgroup.coe_inv]
    group⟩
  let idxPair : Type _ := idx × C
  letI : Fintype idxPair := Fintype.ofFinite _
  let corrections (a : idxPair) : π.ker := correction a.1 a.2
  let allowed : Finset π.ker := insert 1 (Finset.univ.image corrections)
  have hallowed (a : idx) (c : C) : correction a c ∈ allowed :=
    mem_insert_image_univ 1 corrections (a,c)
  let State : Type _ := (↑T : Type _) × C × Bool
  let recover (a : State) (v : X) : X × Γ × Bool :=
    ((s a.1.val * (repr a.2.1).val) • v,a.1.val,a.2.2)
  let embed : TaggedSpace Z Γ ↪ X × Γ × Bool :=
    ⟨fun x => (x.1.val,x.2),by
      intro x y h
      exact Prod.ext (Subtype.ext (congrArg (fun p : X × Γ × Bool => p.1) h))
        (congrArg (fun p : X × Γ × Bool => p.2) h)⟩
  let U : Set (TaggedSpace Z Γ) := {x | x.2.1 ∈ T}
  apply uniform_finite_path_orbits_of_lifts (finiteBranch Z q T P) embed recover U π.ker hL allowed
  · intro x y hU h
    rcases h with h | ⟨hT,_,_⟩
    · exact h.symm
    · exact False.elim (hU hT)
  · intro y hy
    let a : State := (⟨y.2.1,hy⟩,1,y.2.2)
    refine ⟨a,(s a.1.val*(repr a.2.1).val)⁻¹ • y.1.val,?_⟩
    exact Prod.ext (smul_inv_smul (s a.1.val*(repr a.2.1).val) y.1.val).symm rfl
  · intro x y hx he state v hv
    rcases he with rfl | ⟨ht,hu,g,hg,hproj,hxy⟩
    · exact ⟨hx,state,1,by simp [allowed],by simpa using hv⟩
    · let a : idx := ⟨(⟨x.2.1,ht⟩,⟨y.2.1,hu⟩,⟨g,hg⟩),hproj⟩
      let c := state.2.1
      have hst : state.1 = a.val.1 := by
        apply Subtype.ext
        exact (congrArg (fun w : X × Γ × Bool => w.2.1) hv).symm
      have hp : x.1.val = (s a.val.1.val*(repr c).val) • v := by
        rw [← hst]
        exact congrArg (fun p : X × Γ × Bool => p.1) hv
      have hd : normalizedFix a c • v = v := by
        have hh := hdFix a c x.1
        rw [hp] at hh
        have h0 : (s a.val.1.val)⁻¹ • ((s a.val.1.val * (repr c).val) • v) = (repr c).val • v := by
          rw [mul_smul,inv_smul_smul]
        rw [h0] at hh
        simp only [normalizedFix,mul_smul,hh,inv_smul_smul]
      let a' : State := (a.val.2.1,next a c,y.2.2)
      refine ⟨hu,a',correction a c,hallowed a c,?_⟩
      have hfst : y.1.val =
          (s a.val.2.1.val*(repr (next a c)).val) • ((correction a c).val • v) := by
        have hcancel : (normalizedFix a c)⁻¹ • v = v := calc
          _ = (normalizedFix a c)⁻¹ • (normalizedFix a c • v) := congrArg _ hd.symm
          _ = v := inv_smul_smul _ _
        have hword : (s a.val.2.1.val*(repr (next a c)).val) * (residual a c).val =
            g * (s a.val.1.val*(repr c).val) := by
          change (s y.2.1*(repr (next a c)).val) *
            ((repr (next a c)).val⁻¹*((s y.2.1)⁻¹*g*s x.2.1)*(repr c).val) =
            g * (s x.2.1*(repr c).val)
          group
        rw [← hxy,hp]
        change g • ((s a.val.1.val*(repr c).val) • v) =
          (s a.val.2.1.val*(repr (next a c)).val) •
            (((residual a c).val*(normalizedFix a c)⁻¹) • v)
        rw [mul_smul (residual a c).val (normalizedFix a c)⁻¹ v,hcancel,
          ← mul_smul (s a.val.2.1.val*(repr (next a c)).val) (residual a c).val v,
          hword]
        exact (mul_smul g (s a.val.1.val*(repr c).val) v).symm
      exact Prod.ext hfst rfl

end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.TaggedCosetOrbits

-- BEGIN COMPLETE MODULE HirschProof.TaggedKernelBounds
section
                                    
                            

set_option autoImplicit false

namespace LocalHirschHyperfinite.TaggedSpace

variable {G Γ X Q : Type*} [Group G] [Group Γ] [Group Q] [MulAction G X]

set_option maxHeartbeats 900000 in
/-- The nilpotent isolator and the locally finite radical give finite orbits for
any fixed family of switches. No uniform index estimate in the family is needed. -/
theorem bounded_switch_orbits_of_isolator (Z : Set X) (q : G →* Γ) (π : G →* Q)
    (T : Finset Γ) (P : Finset G) (s : Γ → G) (I : Subgroup Q) [Group.IsNilpotent I]
    (H : (↑T : Type _) → Subgroup I) (hH : ∀ t, (H t).FG)
    (hroot : ∀ t, nilpotentIsolator (H t) = ⊤)
    (hfix : ∀ (t : T) (a : I), a ∈ H t → ∃ d : G,
      π d = a.val ∧ ∀ x : Z, d • ((s t.val)⁻¹ • x.val) = (s t.val)⁻¹ • x.val)
    (hI : ∀ t ∈ T, ∀ u ∈ T, ∀ g ∈ P, q g*t=u → π ((s u)⁻¹*g*s t) ∈ I)
    (hL : IsLocallyFiniteGroup π.ker) :
    ∃ B : ℕ, ∀ x : TaggedSpace Z Γ,
      {y | Relation.ReflTransGen (finiteBranch Z q T P) x y}.Finite ∧
      {y | Relation.ReflTransGen (finiteBranch Z q T P) x y}.ncard ≤ B := by
  classical
  let U : Type _ := {a : (↑T : Type _) × (↑T : Type _) × (↑P : Type _) //
    q a.2.2.val*a.1.val = a.2.1.val}
  let delta (a : U) : I := ⟨π ((s a.val.2.1.val)⁻¹*a.val.2.2.val*s a.val.1.val),
    hI _ a.val.1.property _ a.val.2.1.property _ a.val.2.2.property a.property⟩
  let J := Subgroup.closure (Set.range delta) ⊔ iSup H
  have hJ : J.FG := (show (Subgroup.closure (Set.range delta)).FG from
    (Subgroup.fg_iff _).2 ⟨_,rfl,Set.finite_range _⟩).sup (Subgroup.FG.iSup H hH)
  let M (t : T) := (H t).subgroupOf J
  have hM (t : T) : (M t).FiniteIndex := finiteIndex_of_fg_le_nilpotentIsolator (H t) J hJ
    (by rw [hroot]; exact le_top)
  let J₀ : Subgroup J := ⨅ t : T, (M t).normalCore
  have hJ₀ (t : T) : J₀ ≤ M t := (iInf_le _ t).trans (Subgroup.normalCore_le (M t))
  letI : J₀.Normal := Subgroup.normal_iInf_normal fun t => Subgroup.normalCore_normal (M t)
  letI : J₀.FiniteIndex := Subgroup.finiteIndex_iInf fun t =>
    letI : (M t).FiniteIndex := hM t
    inferInstance
  let JQ := J.map I.subtype
  let JG := JQ.comap π
  let ofI := J.equivMapOfInjective I.subtype I.subtype_injective
  let intoQ : JG →* JQ :=
    { toFun := fun x => ⟨π x.val,x.property⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun x y => Subtype.ext (map_mul π x.val y.val) }
  let f : JG →* J := ofI.symm.toMonoidHom.comp intoQ
  have hf (k : JG) : (f k).val.val = π k.val := by
    have h := congrArg Subtype.val (ofI.apply_symm_apply (intoQ k))
    exact h
  let N := J₀.comap f
  letI : N.Normal := Subgroup.Normal.comap ‹J₀.Normal› f
  letI : N.FiniteIndex := by
    refine ⟨?_⟩
    change (J₀.comap f).index ≠ 0
    rw [Subgroup.index_comap]
    haveI : J₀.IsFiniteRelIndex f.range := Subgroup.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  apply bounded_orbits_of_finite_coset_lifts Z q π T P s JG N _ _ hL
  · intro t ht u hu g hg hd
    let a : U := ⟨(⟨t,ht⟩,⟨u,hu⟩,⟨g,hg⟩),hd⟩
    change π ((s u)⁻¹*g*s t) ∈ J.map I.subtype
    have hδ : delta a ∈ Subgroup.closure (Set.range delta) := Subgroup.subset_closure ⟨a,rfl⟩
    exact ⟨delta a, (show Subgroup.closure (Set.range delta) ≤ J from le_sup_left) hδ,rfl⟩
  · intro t ht k hk
    let t' : T := ⟨t,ht⟩
    have hk' : (f k).val ∈ H t' := hJ₀ t' hk
    obtain ⟨d,hd,hdf⟩ := hfix t' (f k).val hk'
    exact ⟨d,hd.trans (hf k),hdf⟩

end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.TaggedKernelBounds

-- BEGIN COMPLETE MODULE HirschProof.FiniteOrbitSelector
section
                                          
                                                               
                                                           
                                     
                            

set_option autoImplicit false

open Set MeasureTheory

namespace LocalHirschHyperfinite

variable {G X : Type*} [Group G] [Countable G] [MulAction G X]
  [MeasurableSpace X] [StandardBorelSpace X]

/-- Every Borel action with finite orbits admits a Borel representative constant on orbits. -/
theorem exists_finite_orbit_selector (hact : BorelAction G X)
    (hfin : ∀ x : X, {y | orbitRel G x y}.Finite) :
    ∃ r : X → X, Measurable r ∧ (∀ x, orbitRel G x (r x)) ∧
      ∀ x y, orbitRel G x y → r x = r y := by
  classical
  obtain ⟨g,hg⟩ := exists_surjective_nat G
  let act (i : ℕ) (x : X) := g i • x
  let code := embeddingReal X
  have hc := measurableEmbedding_embeddingReal X
  let P (i : ℕ) (x : X) := ∀ j : ℕ, code (act i x) ≤ code (act j x)
  have hex (x : X) : ∃ i, P i x := by
    obtain ⟨y,hy,hyMin⟩ := Set.exists_min_image {y | orbitRel G x y} code (hfin x)
      ⟨x,1,one_smul _ _⟩
    obtain ⟨b,hb⟩ := hy
    obtain ⟨i,rfl⟩ := hg b
    refine ⟨i,fun j => ?_⟩
    change act i x = y at hb
    rw [hb]
    exact hyMin _ ⟨g j,rfl⟩
  let i₀ (x : X) := Nat.find (hex x)
  let r (x : X) := act (i₀ x) x
  have hA (i : ℕ) : Measurable (act i) := hact (g i)
  have hP (i : ℕ) : MeasurableSet {x | P i x} := by
    change MeasurableSet {x : X | ∀ j : ℕ, code (act i x) ≤ code (act j x)}
    rw [setOf_forall]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le (hc.measurable.comp (hA i)) (hc.measurable.comp (hA j))
  have hrmin (x y : X) (hxy : orbitRel G x y) : code (r x) ≤ code y := by
    obtain ⟨t,ht⟩ := hxy
    obtain ⟨j,rfl⟩ := hg t
    exact ht ▸ Nat.find_spec (hex x) j
  have hrAct (x : X) : orbitRel G x (r x) := ⟨g (i₀ x),rfl⟩
  refine ⟨r,Measurable.find hA hP hex,hrAct,fun x y hxy => ?_⟩
  apply hc.injective
  obtain ⟨t,ht⟩ := hxy
  obtain ⟨a,ha⟩ := hrAct x
  obtain ⟨b,hb⟩ := hrAct y
  apply le_antisymm
  · apply hrmin x (r y)
    exact ⟨b*t,by rw [mul_smul,ht,hb]⟩
  · apply hrmin y (r x)
    refine ⟨a*t⁻¹,?_⟩
    rw [mul_smul,← ht,inv_smul_smul,ha]

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.FiniteOrbitSelector

-- BEGIN COMPLETE MODULE HirschProof.ChartCorrections
section
                                  
                                      
                                              

set_option autoImplicit false

namespace LocalHirschHyperfinite.ChartModel

variable {H Γ : Type*} [Group H] [Group Γ]

theorem exists_chart_corrections (π : H →* Γ) (s : Γ → H) (hs : ∀ g, π (s g) = g)
    (W : Finset Γ) (P : Finset H) :
    ∃ D : Subgroup H, D.FG ∧ D ≤ π.ker ∧
      ∀ w ∈ W, ∀ g ∈ P, s w * g * (s (w*π g))⁻¹ ∈ D := by
  classical
  let A := (W ×ˢ P).image fun q : Γ × H => s q.1 * q.2 * (s (q.1*π q.2))⁻¹
  let D := Subgroup.closure (A : Set H)
  refine ⟨D,⟨A,rfl⟩,(Subgroup.closure_le _).mpr ?_,?_⟩
  · intro x hx
    obtain ⟨⟨w,g⟩,_,rfl⟩ := Finset.mem_image.mp hx
    simp [hs]
  · intro w hw g hg
    exact Subgroup.subset_closure (Finset.mem_image.mpr ⟨(w,g),Finset.mem_product.mpr ⟨hw,hg⟩,rfl⟩)

theorem exists_palette_corrections (π : H →* Γ) (s : Γ → H) (hs : ∀ g, π (s g) = g)
    {D : Subgroup H} (hD : D.FG) (hker : D ≤ π.ker) (V : Finset Γ) :
    ∃ B : Subgroup H, B.FG ∧ B ≤ π.ker ∧
      ∀ a ∈ V, ∀ b ∈ V, ∀ x ∈ D, ∀ y ∈ D,
        ∃ r ∈ B, x * s b * (s a)⁻¹ * y = s (b*a⁻¹) * r := by
  classical
  obtain ⟨G,hG⟩ := hD
  let C := V ×ˢ V
  let e (q : Γ × Γ) := s (q.2*q.1⁻¹)
  let correction (q : Γ × Γ) := (e q)⁻¹ * s q.2 * (s q.1)⁻¹
  let conjugate (q : Γ × Γ) (g : H) := (e q)⁻¹ * g * e q
  let A := (G ∪ C.image correction) ∪ (C ×ˢ G).image
    (fun p : (Γ × Γ) × H => conjugate p.1 p.2)
  let B := Subgroup.closure (A : Set H)
  have hGker (g : H) (hg : g ∈ G) : π g = 1 :=
    hker (hG ▸ Subgroup.subset_closure (show g ∈ (G : Set H) from hg))
  have hcor (q : Γ × Γ) : π (correction q) = 1 := by
    simp [correction,e,hs,mul_assoc]
  have hconj (q : Γ × Γ) (g : H) (hg : g ∈ G) : π (conjugate q g) = 1 := by
    simp [conjugate,hGker g hg]
  have hAker : (A : Set H) ⊆ π.ker := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact hGker x hx
      · obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hx
        exact hcor q
    · obtain ⟨⟨q,g⟩,hq,rfl⟩ := Finset.mem_image.mp hx
      exact hconj q g (Finset.mem_product.mp hq).2
  refine ⟨B,⟨A,rfl⟩,(Subgroup.closure_le _).mpr hAker,?_⟩
  have hDB : D ≤ B := by
    rw [← hG]
    exact (Subgroup.closure_le _).mpr fun g hg =>
      Subgroup.subset_closure (Finset.mem_union_left _ (Finset.mem_union_left _ hg))
  intro a ha b hb x hx y hy
  have hab : (a,b) ∈ C := Finset.mem_product.mpr ⟨ha,hb⟩
  let f : H →* H := (MulAut.conj (e (a,b))⁻¹).toMonoidHom
  have hf (g : H) : f g = conjugate (a,b) g := by simp [f, conjugate, MulAut.conj_apply]
  have hDconj : D ≤ B.comap f := by
    rw [← hG]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change f g ∈ B
    rw [hf]
    exact Subgroup.subset_closure (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨((a,b),g),Finset.mem_product.mpr ⟨hab,hg⟩,rfl⟩))
  have hcx : conjugate (a,b) x ∈ B := by
    rw [← hf]
    exact hDconj hx
  have hcb : correction (a,b) ∈ B :=
    Subgroup.subset_closure (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem correction hab)))
  refine ⟨conjugate (a,b) x * correction (a,b) * y,
    B.mul_mem (B.mul_mem hcx hcb) (hDB hy),?_⟩
  simp [conjugate,correction,e,mul_assoc]

end LocalHirschHyperfinite.ChartModel

end
-- END COMPLETE MODULE HirschProof.ChartCorrections

-- BEGIN COMPLETE MODULE HirschProof.ChartRules
section
                                  
                                 

set_option autoImplicit false

open Set Topology

namespace LocalHirschHyperfinite.ChartModel

variable {Γ : Type*} [Group Γ] [Countable Γ] (cap : Layer Γ → ℕ)

/-- The finite observations, output color, and normalizing displacement of a chart. -/
structure Rules (K : Finset Γ) (d : ℕ) where
  V : Finset Γ
  W : Finset (Addr Γ)
  color : Space cap → Fin (d+1)
  normalizer : Space cap → Γ
  normalizer_mem : ∀ z, normalizer z ∈ V
  read : ∀ x y, (∀ a ∈ W, x.val a = y.val a) →
    color x = color y ∧ normalizer x = normalizer y
  equivariant : ∀ z g, g ∈ K → color z = color (g • z) →
    normalizer (g • z) * g = normalizer z

set_option maxHeartbeats 1000000 in
theorem exists_rules (K : Finset Γ) (hK : SymmetricMoves K) (h1 : (1 : Γ) ∈ K) (d : ℕ)
    (hDAD : CompactClopenDADLE Γ d) : Nonempty (Rules cap K d) := by
  classical
  obtain ⟨U,hU,hCover,N,hN⟩ := hDAD (Space cap) (clopen_basis cap) (continuous_translate cap)
    (free cap) K hK
  let V := wordBall K N
  have hV₁ : (1 : Γ) ∈ V := one_mem_wordBall K N
  have hV (i : Fin (d+1)) (z w : Space cap) (h : TestComponent K (U i) z w) :
      ∃ t ∈ V, t • z = w := components_in_wordBall cap K hK h1 (hN i) h
  let J : Layer Γ := ⟨((V ×ˢ V).image fun p : Γ × Γ => p.2 * p.1⁻¹).erase 1, by simp⟩
  let label (z : Space cap) : Palette cap J := z.val (J,1)
  have hLabel (z : Space cap) {a b : Γ} (ha : a ∈ V) (hb : b ∈ V) (he : a ≠ b) :
      label (a • z) ≠ label (b • z) := by
    have hba : b*a⁻¹ ≠ 1 := by
      intro h
      have hg := congrArg (fun t : Γ => t*a) h
      apply he
      simpa [mul_assoc] using hg.symm
    have hmem : b*a⁻¹ ∈ J.val := Finset.mem_erase.mpr
      ⟨hba, Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩⟩
    have h := z.property J (b*a⁻¹) hmem a
    have hb' : b*a⁻¹*a = b := by simp [mul_assoc]
    rw [hb'] at h
    change z.val (J,1*a) ≠ z.val (J,1*b)
    rw [one_mul,one_mul]
    exact h.symm
  have hc (z : Space cap) : ∃ i : Fin (d+1), z ∈ U i ∧ ∀ j, z ∈ U j → i ≤ j := by
    let A := Finset.univ.filter (fun i : Fin (d+1) => z ∈ U i)
    have hA : A.Nonempty := by
      obtain ⟨i,hi⟩ := hCover z
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    exact ⟨A.min' hA,(Finset.mem_filter.mp (A.min'_mem hA)).2,
      fun j hj => A.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)⟩
  choose c hcMem hcMin using hc
  have hm (z : Space cap) :
      ∃ t ∈ V, TestComponent K (U (c z)) z (t • z) ∧
        ∀ w, TestComponent K (U (c z)) z w → label (t • z) ≤ label w := by
    let A := V.filter (fun t => TestComponent K (U (c z)) z (t • z))
    have hA : A.Nonempty := by
      refine ⟨1,Finset.mem_filter.mpr ⟨hV₁,?_⟩⟩
      rw [one_smul]
      exact ⟨hcMem z,.refl⟩
    obtain ⟨t,ht,htMin⟩ := A.exists_min_image (fun t => label (t • z)) hA
    refine ⟨t,(Finset.mem_filter.mp ht).1,(Finset.mem_filter.mp ht).2,fun w hw => ?_⟩
    obtain ⟨s,hs,rfl⟩ := hV _ _ _ hw
    exact htMin s (Finset.mem_filter.mpr ⟨hs,hw⟩)
  choose m hmV hmComp hmMin using hm
  have obs (j : Fin (d+1) × ↥V) : ∃ win : Finset (Addr Γ),
      ∀ x y : Space cap, (∀ a ∈ win, x.val a = y.val a) →
        (j.2.val • x ∈ U j.1 ↔ j.2.val • y ∈ U j.1) := by
    let A := (fun z : Space cap => j.2.val • z) ⁻¹' U j.1
    have hA : IsClopen A := (hU j.1).preimage (continuous_translate cap j.2.val)
    let bit (z : Space cap) := if z ∈ A then true else false
    have hb : Continuous bit := by
      show Continuous (A.piecewise (fun _ => true) (fun _ => false))
      exact continuous_piecewise (by rw [hA.frontier_eq]; simp) continuousOn_const continuousOn_const
    obtain ⟨W,hW⟩ := finite_window cap bit hb
    refine ⟨W,fun x y h => ?_⟩
    have he := hW x y h
    change x ∈ A ↔ y ∈ A
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp_all [bit]
  choose win hwin using obs
  let W : Finset (Addr Γ) := Finset.univ.biUnion win ∪ V.image (J,·)
  have ho {x y : Space cap} (hxy : ∀ a ∈ W, x.val a = y.val a) :
      ∀ i t, t ∈ V → (t • x ∈ U i ↔ t • y ∈ U i) := by
    intro i t ht
    let j : Fin (d+1) × ↥V := (i,⟨t,ht⟩)
    exact hwin j x y fun a ha => hxy a (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,ha⟩))
  have hLabels {x y : Space cap} (hxy : ∀ a ∈ W, x.val a = y.val a) :
      ∀ t ∈ V, label (t • x) = label (t • y) := by
    intro t ht
    change x.val (J,1*t) = y.val (J,1*t)
    rw [one_mul]
    exact hxy _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (J,·) ht))
  refine ⟨⟨V,W,c,m,hmV,?_,?_⟩⟩
  · intro x y hxy
    have hcc : c x = c y := by
      apply le_antisymm
      · apply hcMin x
        have hh := ho hxy (c y) 1 hV₁
        simpa only [one_smul] using hh.mpr (by simpa only [one_smul] using hcMem y)
      · apply hcMin y
        have hh := ho hxy (c x) 1 hV₁
        simpa only [one_smul] using hh.mp (by simpa only [one_smul] using hcMem x)
    refine ⟨hcc,?_⟩
    have hTest (g : Γ) :
        TestComponent K (U (c x)) x (g • x) ↔ TestComponent K (U (c y)) y (g • y) := by
      rw [← hcc]
      exact components_agree cap K V hV₁ (U (c x)) (hV (c x)) (ho hxy (c x)) g
    have hle₁ := hmMin x _ ((hTest (m y)).mpr (hmComp y))
    have hle₂ := hmMin y _ ((hTest (m x)).mp (hmComp x))
    have hmx := hLabels hxy (m x) (hmV x)
    have hmy := hLabels hxy (m y) (hmV y)
    rw [← hmx,← hmy] at hle₂
    by_contra hn
    exact hLabel x (hmV x) (hmV y) hn (le_antisymm hle₁ hle₂)
  · intro z g hg heq
    have hzg : TestComponent K (U (c z)) z (g • z) :=
      ⟨hcMem z,.single ⟨hcMem z,heq.symm ▸ hcMem (g • z),g,hg,rfl⟩⟩
    have hgNorm := hmComp (g • z)
    rw [← heq] at hgNorm
    have h₁ := test_trans cap hzg hgNorm
    have h₂ := test_trans cap (test_symm cap hK hzg) (hmComp z)
    have hle₁ := hmMin z _ h₁
    have hle₂ := hmMin (g • z) _ (heq ▸ h₂)
    obtain ⟨t,ht,hEq⟩ := hV _ _ _ h₁
    have hmark : label (m z • z) = label (t • z) := by
      rw [hEq]
      exact le_antisymm hle₁ hle₂
    have hmEq : m z = t := by
      by_contra hn
      exact hLabel z (hmV z) ht hn hmark
    apply smul_injective cap z
    change (m (g • z) * g) • z = m z • z
    rw [mul_smul, hmEq, hEq]

end LocalHirschHyperfinite.ChartModel

end
-- END COMPLETE MODULE HirschProof.ChartRules

-- BEGIN COMPLETE MODULE HirschProof.PhysicalCharts
section
                                   
                             

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite.ChartModel

variable {H Γ X : Type*} [Group H] [Group Γ] [Countable H] [Countable Γ]
  [MulAction H X] [MeasurableSpace X] [StandardBorelSpace X]

/-- The palette may depend on the outer finite list, and is uniform over the kernel test. -/
def HasKernelPalettes (π : H →* Γ) (X : Type*) [MulAction H X] [MeasurableSpace X] : Prop :=
  ∀ C : Finset H, (∀ c ∈ C, π c ≠ 1) →
    ∃ m : ℕ, ∀ B : Subgroup H, B.FG → B ≤ π.ker →
      ∃ q : X → Fin m, Measurable q ∧
        ∀ c ∈ C, ∀ b ∈ B, ∀ x, q x ≠ q ((c*b) • x)

/-- On each parameter fiber a finitely generated kernel subgroup has uniformly small orbits. -/
def FiniteKernelOrbitBounds {T : Type*} (π : H →* Γ) (p : X → T) : Prop :=
  ∀ B : Subgroup H, B.FG → B ≤ π.ker → ∀ t : T,
    ∃ N : ℕ, ∀ x, p x = t → ∃ F : Finset X, F.card ≤ N ∧
      ∀ b ∈ B, b • x ∈ F

structure ObservedChart (cap : Layer Γ → ℕ) (π : H →* Γ) (P : Finset H)
    (W : Finset (Addr Γ)) (X : Type*) [MulAction H X] [MeasurableSpace X] where
  z : X → Space cap
  label : ∀ (a : Addr Γ), X → Palette cap a.1
  measurable_label : ∀ a, Measurable (label a)
  realize : ∀ a ∈ W, ∀ x, (z x).val a = label a x
  shift_agree : ∀ a ∈ W, ∀ g ∈ P, ∀ x, (z (g • x)).val a = (π g • z x).val a

set_option maxHeartbeats 1000000 in
theorem exists_observed_chart {T : Type*} (π : H →* Γ) (s : Γ → H) (hs : ∀ v, π (s v) = v)
    (P : Finset H) (h1 : (1 : H) ∈ P) (W : Finset (Addr Γ))
    (hact : BorelAction H X) (p : X → T) (hfin : FiniteKernelOrbitBounds π p)
    (cap : Layer Γ → ℕ)
    (hcap : ∀ j : Layer Γ, ∀ B : Subgroup H, B.FG → B ≤ π.ker →
      ∃ q : X → Fin (cap j), Measurable q ∧
        ∀ c ∈ j.val, ∀ b ∈ B, ∀ x, q x ≠ q ((s c*b) • x)) :
    Nonempty (ObservedChart cap π P W X) := by
  classical
  let Ws := W.image Prod.snd
  let F := P.image π
  let V₀ := (Ws ×ˢ F).image fun a : Γ × Γ => a.1*a.2
  have hW {a : Addr Γ} (ha : a ∈ W) : a.2 ∈ Ws := Finset.mem_image_of_mem _ ha
  have hobserve {a : Addr Γ} (ha : a ∈ W) {g : H} (hg : g ∈ P) : a.2*π g ∈ V₀ :=
    Finset.mem_image.mpr ⟨(a.2,π g),
      Finset.mem_product.mpr ⟨hW ha,Finset.mem_image_of_mem π hg⟩,rfl⟩
  have hW0 {a : Addr Γ} (ha : a ∈ W) : a.2 ∈ V₀ := by
    have hh := hobserve ha h1
    simpa only [map_one,mul_one] using hh
  obtain ⟨D,hD,hDker,hDcorrect⟩ := exists_chart_corrections π s hs Ws P
  obtain ⟨B,hB,hBker,hBcorrect⟩ := exists_palette_corrections π s hs hD hDker V₀
  have hfinD (x : X) : {y | orbitRel D x y}.Finite := by
    obtain ⟨N,hN⟩ := hfin D hD hDker (p x)
    obtain ⟨F,_,hF⟩ := hN x rfl
    apply F.finite_toSet.subset
    rintro _ ⟨d,rfl⟩
    exact hF d.val d.prop
  obtain ⟨r,hr,hrOrb,hrInv⟩ := exists_finite_orbit_selector
    (fun g : D => hact g.val) hfinD
  choose c hc hsep using fun j => hcap j B hB hBker
  let q (a : Addr Γ) (x : X) : Palette cap a.1 :=
    ⟨(c a.1 (r (s a.2 • x))).val,
      (c a.1 (r (s a.2 • x))).isLt.trans_le (le_trans (le_max_left _ _) (Nat.le_succ _))⟩
  have hq (a : Addr Γ) : Measurable (q a) := by
    let emb (i : Fin (cap a.1)) : Palette cap a.1 :=
      ⟨i.val,i.isLt.trans_le (le_trans (le_max_left _ _) (Nat.le_succ _))⟩
    exact (measurable_of_countable emb).comp ((hc a.1).comp (hr.comp (hact (s a.2))))
  have hproper (x : X) (j : Layer Γ) : ProperOn cap j V₀ (fun v => q (j,v) x) := by
    intro u hu v hv huv
    obtain ⟨a,ha⟩ := hrOrb (s v • x)
    obtain ⟨b,hb⟩ := hrOrb (s (u*v) • x)
    obtain ⟨d,hd,he⟩ := hBcorrect v hv (u*v) huv b.val b.prop a.val⁻¹ (D.inv_mem a.prop)
    rw [mul_assoc u v v⁻¹, mul_inv_cancel, mul_one] at he
    have hxy : (s u*d) • r (s v • x) = r (s (u*v) • x) := by
      rw [← he, ← ha, ← hb]
      change (b.val*s (u*v)*(s v)⁻¹*a.val⁻¹) • (a.val • s v • x) =
        b.val • s (u*v) • x
      simp [mul_assoc,mul_smul]
    intro heq
    have hh := hsep j u hu d hd (r (s v • x))
    rw [hxy] at hh
    apply hh
    have hraw : (q (j,v) x).val = (q (j,u*v) x).val :=
      congrArg (fun i : Palette cap j => i.val) heq.symm
    exact Fin.ext hraw
  have extension (x : X) := extend_patterns cap (fun _ => V₀) (fun a => q a x) (hproper x)
  choose z hz using extension
  refine ⟨⟨z,q,hq,fun a ha x => hz x a.1 a.2 (hW0 ha),?_⟩⟩
  intro a ha g hg x
  change (z (g • x)).val (a.1,a.2) = (z x).val (a.1,a.2*π g)
  rw [hz (g • x) a.1 a.2 (hW0 ha), hz x a.1 (a.2*π g) (hobserve ha hg)]
  have hCorr := hDcorrect a.2 (hW ha) g hg
  let d : D := ⟨s a.2*g*(s (a.2*π g))⁻¹,hCorr⟩
  have he : d • (s (a.2*π g) • x) = s a.2 • (g • x) := by
    change ((s a.2*g)*(s (a.2*π g))⁻¹) • (s (a.2*π g) • x) = s a.2 • (g • x)
    simp [mul_smul]
  have heq := hrInv _ _ ⟨d,he⟩
  change (⟨(c a.1 (r (s a.2 • (g • x)))).val,_⟩ : Palette cap a.1) =
    ⟨(c a.1 (r (s (a.2*π g) • x))).val,_⟩
  apply Fin.ext
  exact congrArg (fun y => (c a.1 y).val) heq.symm

theorem observed_color_measurable {π : H →* Γ} {P : Finset H} {W : Finset (Addr Γ)}
    {cap : Layer Γ → ℕ} (C : ObservedChart cap π P W X) {Y : Type*} [MeasurableSpace Y]
    (f : Space cap → Y)
    (hread : ∀ z w, (∀ a ∈ W, z.val a = w.val a) → f z = f w) :
    Measurable (fun x => f (C.z x)) := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX => exact measurable_of_countable _
  | inr hX =>
    let V := (a : ↥W) → Palette cap a.val.1
    let obs (x : X) : V := fun a => C.label a.val x
    have hobs : Measurable obs := measurable_pi_lambda _ (fun a => C.measurable_label a.val)
    let canRead (v : V) := ∃ z : Space cap, ∀ a : ↥W, z.val a.val = v a
    let rep (v : V) : Space cap := if h : canRead v then h.choose else C.z hX.some
    have hrep (x : X) : ∀ a : ↥W, (rep (obs x)).val a.val = obs x a := by
      have h : canRead (obs x) :=
        ⟨C.z x,fun a => C.realize a.val a.prop x⟩
      dsimp only [rep]
      rw [dif_pos h]
      exact h.choose_spec
    letI : Finite V := inferInstanceAs (Finite ((a : ↥W) → Palette cap a.val.1))
    have hMeas : Measurable (fun x => f (rep (obs x))) :=
      (measurable_of_countable (f ∘ rep)).comp hobs
    convert hMeas using 1
    funext x
    exact (hread _ _ (fun a ha => (hrep x ⟨a,ha⟩).trans (C.realize a ha x).symm)).symm

end LocalHirschHyperfinite.ChartModel

end
-- END COMPLETE MODULE HirschProof.PhysicalCharts

-- BEGIN COMPLETE MODULE HirschProof.FiniteOrbitActions
section
                                          
                                            
                                            
                                            
                                    
                                

set_option autoImplicit false

namespace LocalHirschHyperfinite

/-- A finitely generated group acting faithfully with uniformly bounded orbits is finite.
Every orbit action occurs among the finitely many actions on a fixed alphabet. -/
theorem finite_of_faithful_bounded_orbits
    (G X : Type*) [Group G] [MulAction G X] [FaithfulSMul G X]
    (S : Finset G) (hS : Subgroup.closure (S : Set G) = ⊤) (n : ℕ)
    (hO : ∀ x : X, (MulAction.orbit G x).Finite ∧ Nat.card (MulAction.orbit G x) ≤ n) :
    Finite G := by
  classical
  let P := Equiv.Perm (Fin n)
  let evaluate : (G →* P) → ((↑S : Type _) → P) := fun f s => f s.val
  have heval : Function.Injective evaluate := by
    intro f g hfg
    apply MonoidHom.eq_of_eqOn_dense hS
    intro g hg
    exact congrFun hfg ⟨g,hg⟩
  letI : Finite (G →* P) := Finite.of_injective evaluate heval
  have emb (x : X) : Nonempty (MulAction.orbit G x ↪ Fin n) := by
    letI := (hO x).1.fintype
    have h := (hO x).2
    rw [Nat.card_eq_fintype_card] at h
    exact Function.Embedding.nonempty_of_card_le (by simpa using h)
  let ι (x : X) : MulAction.orbit G x ↪ Fin n := Classical.choice (emb x)
  let act (x : X) : G →* P := (Equiv.Perm.viaEmbeddingHom (ι x)).comp
    (MulAction.toPermHom G (MulAction.orbit G x))
  let test (g : G) : (G →* P) → P := fun ρ => ρ g
  apply Finite.of_injective test
  intro a b hab
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  have h := Equiv.Perm.viaEmbeddingHom_injective (ι x) (congrFun hab (act x))
  let v : MulAction.orbit G x := ⟨x,MulAction.mem_orbit_self x⟩
  exact congrArg Subtype.val (congrArg (fun e : Equiv.Perm (MulAction.orbit G x) => e v) h)

section Borel

variable {G X : Type*} [Group G] [Countable G] [MulAction G X]
  [MeasurableSpace X] [MeasurableEq X]

theorem orbitRel_borel (hX : BorelAction G X) : BorelEquivalence (orbitRel G (X := X)) := by
  constructor
  · refine ⟨fun x => ⟨1,one_smul _ _⟩,?_,?_⟩
    · rintro x y ⟨g,rfl⟩
      exact ⟨g⁻¹,inv_smul_smul g x⟩
    · rintro x y z ⟨g,rfl⟩ ⟨h,rfl⟩
      exact ⟨h*g,mul_smul h g x⟩
  · have heq : {p : X × X | orbitRel G p.1 p.2} =
        ⋃ g : G, {p : X × X | g • p.1 = p.2} := by
      ext p
      simp [orbitRel]
    rw [heq]
    exact MeasurableSet.iUnion fun g => measurableSet_eq_fun ((hX g).comp measurable_fst) measurable_snd

/-- All Borel actions of countable locally finite groups are hyperfinite. -/
theorem hyperfinite_of_locally_finite (hX : BorelAction G X)
    (hG : ∀ H : Subgroup G, H.FG → Finite H) : IsHyperfinite (orbitRel G (X := X)) := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat G
  let S (n : ℕ) : Finset G := (Finset.range (n+1)).image e
  let H (n : ℕ) := Subgroup.closure (S n : Set G)
  have hmono : Monotone H := fun n m hnm => Subgroup.closure_mono (by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr
      ((Finset.mem_range.mp hi).trans_le (Nat.succ_le_succ hnm)),rfl⟩)
  let F (n : ℕ) := orbitRel (H n) (X := X)
  refine ⟨orbitRel_borel hX,F,?_,?_,?_⟩
  · intro n m hnm x y hxy
    obtain ⟨g,hg⟩ := hxy
    exact ⟨⟨g.val,hmono hnm g.property⟩,hg⟩
  · intro n
    have hh : BorelAction (H n) X := fun g => hX g.val
    letI : Finite (H n) := hG (H n) ⟨S n,rfl⟩
    refine ⟨orbitRel_borel hh,fun x => ?_⟩
    have hc : {y | F n x y} = Set.range (fun g : H n => g • x) := rfl
    exact hc ▸ Set.finite_range _
  · intro x y
    constructor
    · rintro ⟨g,hg⟩
      obtain ⟨n,rfl⟩ := he g
      exact ⟨n,⟨e n,Subgroup.subset_closure
        (Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr (Nat.lt_succ_self n),rfl⟩)⟩,hg⟩
    · rintro ⟨n,g,hg⟩
      exact ⟨g.val,hg⟩

end Borel
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.FiniteOrbitActions

-- BEGIN COMPLETE MODULE HirschProof.TaggedFiniteKernel
section
                                      
                                     
                                 
                                     

set_option autoImplicit false

namespace LocalHirschHyperfinite.TaggedSpace
open Set

variable {G Γ X Q : Type*} [Group G] [Group Γ] [Group Q] [MulAction G X]
variable {Z : Set X} {q : G →* Γ}

lemma finiteBranch_symmetric {T : Finset Γ} {P : Finset G} (hP : SymmetricMoves P) :
    Symmetric (finiteBranch Z q T P) := by
  rintro x y (h | ⟨hx,hy,g,hg,ht,he⟩)
  · exact Or.inl h.symm
  · refine Or.inr ⟨hy,hx,g⁻¹,hP hg,?_,?_⟩
    · rw [← ht,map_inv,inv_mul_cancel_left]
    · rw [← he,inv_smul_smul]

/-- Every element of a finitely generated tagged kernel acts by a path
through one fixed finite list of tags and physical labels. -/
theorem exists_finite_branch_moves (D : Subgroup (taggedExtension Z q)) (hD : D.FG)
    (hproj : D ≤ (taggedProjection Z q).ker) :
    ∃ (T : Finset Γ) (P : Finset G),
      ∀ d ∈ D, ∀ x : TaggedSpace Z Γ, Relation.ReflTransGen (finiteBranch Z q T P) x (d • x) := by
  classical
  obtain ⟨S,rfl⟩ := hD
  obtain ⟨A,hA⟩ := exists_transport_alphabet S
  choose F hF using fun a : S => kernel_finite_support
    (show taggedProjection Z q a.val = 1 from hproj (Subgroup.subset_closure a.property))
  let T := S.attach.biUnion F
  let P := A ∪ A.image Inv.inv
  have hP : SymmetricMoves P := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg)
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mem_union_left _ (by simpa using ha)
  let R := Relation.ReflTransGen (finiteBranch Z q T P)
  let J : Subgroup (taggedExtension Z q) :=
    { carrier := {a | ∀ x : TaggedSpace Z Γ, R x (a • x)}
      one_mem' := by intro x; simpa using Relation.ReflTransGen.refl (a := x) (r := finiteBranch Z q T P)
      mul_mem' := by
        intro a b ha hb x
        simpa only [mul_smul] using (hb x).trans (ha (b • x))
      inv_mem' := by
        intro a ha x
        have H := Relation.ReflTransGen.symmetric (finiteBranch_symmetric (Z := Z) (q := q) (T := T) hP)
          (ha (a⁻¹ • x))
        simpa using H }
  have hJ : Subgroup.closure (S : Set (taggedExtension Z q)) ≤ J := by
    apply (Subgroup.closure_le _).2
    intro a ha x
    change a ∈ S at ha
    change R x (a • x)
    apply Relation.ReflTransGen.single
    have hsupp : taggedPerm Z q a ∈ supportedPerm Z (T : Set Γ) := by
      apply supportedPerm_mono (A := (F ⟨a,ha⟩ : Set Γ)) _ (hF ⟨a,ha⟩)
      exact fun _ ht => Finset.mem_biUnion.mpr ⟨⟨a,ha⟩,Finset.mem_attach _ _,ht⟩
    by_cases hx : tag x ∈ T
    · obtain ⟨g,hg,hbase,htag⟩ := hA a ha x
      have hπ : taggedProjection Z q a = 1 := hproj (Subgroup.subset_closure ha)
      exact Or.inr ⟨hx,(supportedPerm_preserves hsupp x).mpr hx,
        g,Finset.mem_union_left _ hg,by simpa [hπ] using htag.symm,hbase.symm⟩
    · exact Or.inl (hsupp x hx).symm
  exact ⟨T,P,fun d hd => hJ hd⟩

/-- Uniform finite orbit lists on the constant stage, under the manuscript's
normalized isolator and locally finite radical conditions. -/
theorem finiteKernelOrbitBounds_constant_of_isolator (π : G →* Q)
    (s : Γ → G) (hs : ∀ t, q (s t) = t)
    (I : Subgroup Q) [Group.IsNilpotent I]
    (H : Γ → Subgroup I) (hH : ∀ t, (H t).FG)
    (hroot : ∀ t, nilpotentIsolator (H t) = ⊤)
    (hfix : ∀ (t : Γ) (a : I), a ∈ H t → ∃ d : G,
      π d = a.val ∧ ∀ x : Z, d • ((s t)⁻¹ • x.val) = (s t)⁻¹ • x.val)
    (hI : ∀ g : G, q g = 1 → π g ∈ I) (hL : IsLocallyFiniteGroup π.ker) :
    ChartModel.FiniteKernelOrbitBounds (taggedProjection Z q) (fun _ : TaggedSpace Z Γ => ()) := by
  classical
  intro D hD hproj _
  obtain ⟨T,P,hB⟩ := exists_finite_branch_moves D hD hproj
  have hNorm : ∀ t ∈ T, ∀ u ∈ T, ∀ g ∈ P, q g*t=u → π ((s u)⁻¹*g*s t) ∈ I := by
    intro t _ u _ g _ ht
    apply hI
    rw [map_mul,map_mul,map_inv,hs,hs,mul_assoc,ht,inv_mul_cancel]
  obtain ⟨N,hN⟩ := bounded_switch_orbits_of_isolator Z q π T P s I
    (fun t => H t.val) (fun t => hH t.val) (fun t => hroot t.val)
    (fun t => hfix t.val) hNorm hL
  refine ⟨N,fun x _ => ?_⟩
  obtain ⟨hf,hc⟩ := hN x
  refine ⟨hf.toFinset,(Set.ncard_eq_toFinset_card _ hf).symm.le.trans hc,fun d hd => ?_⟩
  exact hf.mem_toFinset.mpr (hB d hd x)

/-- On a constant stage the tagged kernel is locally finite as an abstract
group, by uniform orbit cardinalities and faithfulness on its permutations. -/
theorem finite_kernel_subgroup_of_orbitBounds
    (hb : ChartModel.FiniteKernelOrbitBounds (taggedProjection Z q) (fun _ : TaggedSpace Z Γ => ()))
    (D : Subgroup (taggedExtension Z q)) (hD : D.FG) (hπ : D ≤ (taggedProjection Z q).ker) :
    Finite D := by
  classical
  have hFaith : FaithfulSMul D (TaggedSpace Z Γ) := ⟨by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Equiv.ext
      exact hab
    · show taggedProjection Z q a.val = taggedProjection Z q b.val
      exact (hπ a.property).trans (hπ b.property).symm⟩
  letI := hFaith
  obtain ⟨K,hK⟩ := hb D hD hπ ()
  have hfg : Group.FG D := (Group.fg_iff_subgroup_fg D).mpr hD
  obtain ⟨S,hS,hfinite⟩ := Group.fg_iff.mp hfg
  refine finite_of_faithful_bounded_orbits D (TaggedSpace Z Γ) hfinite.toFinset
    (by simpa using hS) K (fun x => ?_)
  obtain ⟨F,hF,hx⟩ := hK x rfl
  have hsub : MulAction.orbit D x ⊆ (F : Set (TaggedSpace Z Γ)) := by
    rintro y ⟨d,rfl⟩
    exact hx d.val d.property
  refine ⟨F.finite_toSet.subset hsub,?_⟩
  simpa [Set.ncard] using (Set.ncard_le_ncard hsub F.finite_toSet).trans
    (show (F : Set (TaggedSpace Z Γ)).ncard ≤ K by simpa using hF)

end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.TaggedFiniteKernel

-- BEGIN COMPLETE MODULE HirschProof.TaggedFixedWitness
section
                                     
                                              

set_option autoImplicit false

namespace LocalHirschHyperfinite.TaggedSpace

variable {G Q : Type*} [Group G] [Group Q]

/-- Stabilizer image in the physical coordinates belonging to the
section element `g`. -/
def conjugateStabilizerSubgroup (π : G →* Q) (I : Subgroup Q) [I.Normal]
    (H : Subgroup I) (g : G) : Subgroup I :=
  H.map ((MulAut.conjNormal (H := I) (π g)).symm.toMonoidHom)

/-- Physical fixed-point lifts conjugate along with the witness subgroup. -/
theorem conjugateStabilizerSubgroup_fixed_lifts {X : Type*} [MulAction G X] {Z : Set X}
    (π : G →* Q) (I : Subgroup Q) [I.Normal] (H : Subgroup I)
    (hfix : ∀ a ∈ H, ∃ d : G, π d = a.val ∧ ∀ x : Z, d • x.val = x.val) :
    ∀ g : G, ∀ a ∈ conjugateStabilizerSubgroup π I H g, ∃ d : G, π d = a.val ∧
      ∀ x : Z, d • (g⁻¹ • x.val) = g⁻¹ • x.val := by
  rintro g a ⟨b,hb,rfl⟩
  obtain ⟨d,hd,hfixed⟩ := hfix b hb
  refine ⟨g⁻¹*d*g, ?_, fun x => ?_⟩
  · simp [map_mul,map_inv,hd,MulAut.conjNormal_symm_apply]
  · simp only [mul_smul,smul_inv_smul,hfixed]

theorem conjugateStabilizerSubgroup_fg (π : G →* Q) (I : Subgroup Q) [I.Normal]
    (H : Subgroup I) (hH : H.FG) (g : G) : (conjugateStabilizerSubgroup π I H g).FG :=
  IsLocallyFiniteGroup.fg_map ((MulAut.conjNormal (H := I) (π g)).symm.toMonoidHom) H hH

theorem conjugateStabilizerSubgroup_isolator_top (π : G →* Q) (I : Subgroup Q)
    [I.Normal] [Group.IsNilpotent I] (H : Subgroup I) (hH : nilpotentIsolator H = ⊤)
    (g : G) : nilpotentIsolator (conjugateStabilizerSubgroup π I H g) = ⊤ := by
  let e := (MulAut.conjNormal (H := I) (π g)).symm
  change nilpotentIsolator (H.map e.toMonoidHom) = ⊤
  rw [← nilpotentIsolator_map_equiv e H,hH]
  apply top_unique
  intro a _
  obtain ⟨b,rfl⟩ := e.surjective a
  exact ⟨b,Subgroup.mem_top b,rfl⟩

/-- Uniform tagged kernel orbits directly from the fixed stabilizer image. -/
theorem finiteKernelOrbitBounds_constant_of_fixed_witness {Γ X : Type*}
    [Group Γ] [MulAction G X] {Z : Set X} {q : G →* Γ}
    (π : G →* Q) (s : Γ → G) (hs : ∀ t, q (s t) = t)
    (I : Subgroup Q) [I.Normal] [Group.IsNilpotent I]
    (H : Subgroup I) (hH : H.FG) (hroot : nilpotentIsolator H = ⊤)
    (hfix : ∀ a ∈ H, ∃ d : G, π d = a.val ∧ ∀ x : Z, d • x.val = x.val)
    (hI : ∀ g : G, q g = 1 → π g ∈ I) (hL : IsLocallyFiniteGroup π.ker) :
    ChartModel.FiniteKernelOrbitBounds (taggedProjection Z q) (fun _ : TaggedSpace Z Γ => ()) :=
  finiteKernelOrbitBounds_constant_of_isolator π s hs I
    (fun t => conjugateStabilizerSubgroup π I H (s t))
    (fun t => conjugateStabilizerSubgroup_fg π I H hH (s t))
    (fun t => conjugateStabilizerSubgroup_isolator_top π I H hroot (s t))
    (fun t => conjugateStabilizerSubgroup_fixed_lifts π I H hfix (s t)) hI hL

end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.TaggedFixedWitness

-- BEGIN COMPLETE MODULE HirschProof.RadicalApproximation
section
                                      
                                

set_option autoImplicit false

namespace LocalHirschHyperfinite

variable {G Q X : Type*} [Group G] [Group Q] [Countable G] [MulAction G X]
  [MeasurableSpace X] [StandardBorelSpace X]

/-- Uniform relative palettes for a kernel contained in a forbidden subgroup. -/
def HasRelativePalettes (J K : Subgroup G) (X : Type*) [MulAction G X] [MeasurableSpace X] : Prop :=
  ∀ (S : Finset G), (∀ g ∈ S, g ∉ J) → ∀ B : Subgroup G, B.FG → B ≤ K →
    ∃ c : X → Fin (2*S.card+1), Measurable c ∧
      ∀ g ∈ S, ∀ b ∈ B, ∀ x, c x ≠ c ((g*b) • x)

set_option maxHeartbeats 800000 in
/-- Transfer a quotient-relative coloring to a finite-orbit-invariant approximate coloring.
The number of outer labels is controlled by the image of the finite subgroup. -/
theorem exists_invariant_palette_of_finite_subgroup (J : Subgroup G) (p : G →* Q) (D : Subgroup G)
    [Finite D] (hD : D ≤ J) (S : Finset G) (hS : ∀ g ∈ S, g ∉ J)
    (hact : BorelAction G X) (hpal : HasRelativePalettes J p.ker X) :
    ∃ c : X → Fin (2 * (S.card * (Nat.card (D.map p))^2) + 1), Measurable c ∧
      (∀ s ∈ S, ∀ x, c x ≠ c (s • x)) ∧ ∀ d ∈ D, ∀ x, c (d • x) = c x := by
  classical
  let A := D.map p
  let f (a : D) : A := ⟨p a.val,⟨a.val,a.property,rfl⟩⟩
  have hf : Function.Surjective f := by rintro ⟨_,a,ha,rfl⟩; exact ⟨⟨a,ha⟩,rfl⟩
  letI : Finite A := Finite.of_surjective f hf
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype D := Fintype.ofFinite D
  obtain ⟨l,hl⟩ := hf.hasRightInverse
  let outer (a : A) (s : S) (b : A) : G := (l a).val*s.val*(l b).val⁻¹
  let inner (a : D) (s : S) (b : D) : G := (outer (f a) s (f b))⁻¹*(a.val*s.val*b.val⁻¹)
  let C : Finset G := Finset.univ.image (fun z : A × (↑S : Type _) × A => outer z.1 z.2.1 z.2.2)
  let T : Finset G := Finset.univ.image (fun z : D × (↑S : Type _) × D => inner z.1 z.2.1 z.2.2)
  let B := Subgroup.closure (T : Set G)
  have hC : ∀ g ∈ C, g ∉ J := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨⟨a,s,b⟩,_,rfl⟩
    intro ho
    apply hS s.val s.property
    have h : (l a).val⁻¹ * outer a s b * (l b).val ∈ J :=
      J.mul_mem (J.mul_mem (J.inv_mem (hD (l a).property)) ho) (hD (l b).property)
    simpa only [outer,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using h
  have himg (a : A) : p (l a).val = a.val := congrArg Subtype.val (hl a)
  have hT : B ≤ p.ker := by
    apply (Subgroup.closure_le _).2
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨⟨a,s,b⟩,_,rfl⟩
    change p (inner a s b) = 1
    simp only [inner,outer,map_mul,map_inv,himg,f,inv_mul_cancel]
  obtain ⟨c,hc,hproper⟩ := hpal C hC B ⟨T,rfl⟩ hT
  have hfin (x : X) : {y | orbitRel D x y}.Finite := by
    apply (Set.finite_range (fun d : D => d • x)).subset
    exact fun y ⟨d,hd⟩ => ⟨d,hd⟩
  obtain ⟨r,hr,hrmem,hrconst⟩ := exists_finite_orbit_selector (G := D)
    (fun d => hact d.val) hfin
  have hcap : C.card ≤ S.card*(Nat.card A)^2 := by
    refine Finset.card_image_le.trans_eq ?_
    simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_coe,Nat.card_eq_fintype_card]
    ring
  have hLE : 2*C.card+1 ≤ 2*(S.card*(Nat.card A)^2)+1 := by omega
  let extend := Fin.castLE hLE
  refine ⟨extend ∘ c ∘ r,(measurable_of_finite extend).comp (hc.comp hr),?_,?_⟩
  · intro s hs x h
    have heq : c (r x) = c (r (s • x)) := Fin.castLE_injective hLE h
    obtain ⟨a,ha⟩ := hrmem (s • x)
    obtain ⟨b,hb⟩ := hrmem x
    let ss : S := ⟨s,hs⟩
    let o := outer (f a) ss (f b)
    let i := inner a ss b
    have ho : o ∈ C := Finset.mem_image.mpr ⟨(f a,ss,f b),Finset.mem_univ _,rfl⟩
    have hi : i ∈ B := Subgroup.subset_closure
      (Finset.mem_image.mpr ⟨(a,ss,b),Finset.mem_univ _,rfl⟩)
    have hmove : o*i = a.val*s*b.val⁻¹ := by simp [o,i,inner,ss]
    have hrmove : (o*i) • r x = r (s • x) := by
      rw [hmove,← hb,← ha]
      change (a.val*s*b.val⁻¹) • (b.val • x) = a.val • (s • x)
      simp only [mul_smul,inv_smul_smul]
    exact hproper o ho i hi (r x) (heq.trans (congrArg c hrmove).symm)
  · intro d hd x
    change extend (c (r (d • x))) = extend (c (r x))
    rw [← hrconst x (d • x) ⟨⟨d,hd⟩,rfl⟩]

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.RadicalApproximation

-- BEGIN COMPLETE MODULE HirschProof.RadicalPalettes
section
                                       
                                     
                                  

set_option autoImplicit false

open scoped Pointwise commutatorElement

namespace LocalHirschHyperfinite

variable {G X : Type*} [Group G] [Countable G] [MulAction G X]
  [MeasurableSpace X] [StandardBorelSpace X]

omit [Countable G] in
private theorem finite_of_fg_le_locally_finite {K D : Subgroup G}
    (hD : D ≤ K) (hf : D.FG) (hK : IsLocallyFiniteGroup K) : Finite D := by
  letI : Group.FG D := (Group.fg_iff_subgroup_fg D).2 hf
  exact (IsLocallyFiniteGroup.of_injective (Subgroup.inclusion hD)
    (Subgroup.inclusion_injective hD) hK).finite_of_fg

private theorem double_exp_growth (e u s n : ℕ) (he : 0 < e) (hn : 0 < n) :
    2*(s*(e^(u*(s+1)^n))^2)+1 ≤ 2^(2^((e+u+2*s+5)*n)) := by
  let a := e^(u*(s+1)^n)
  let k := e+u+s+1
  have ha : 1 ≤ a := Nat.one_le_pow _ _ he
  have hu : u*(s+1)^n ≤ 2^(u+(s+1)*n) := calc
    _ ≤ 2^u * (2^(s+1))^n := Nat.mul_le_mul (Nat.lt_two_pow_self (n := u)).le
      (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := s+1)).le n)
    _ = _ := by rw [← pow_mul,← pow_add]
  have hexp : e*(u*(s+1)^n) ≤ 2^(k*n) := calc
    _ ≤ 2^e * 2^(u+(s+1)*n) := Nat.mul_le_mul (Nat.lt_two_pow_self (n := e)).le hu
    _ = 2^(e+u+(s+1)*n) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      rw [show k*n = (e+u)*n+(s+1)*n by dsimp [k]; ring]
      exact Nat.add_le_add_right (Nat.le_mul_of_pos_right (e+u) hn) _)
  have hA : a ≤ 2^(2^(k*n)) := calc
    _ ≤ (2^e)^(u*(s+1)^n) := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := e)).le _
    _ = 2^(e*(u*(s+1)^n)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp
  have hbound : s+2+2*2^(k*n) ≤ 2^((e+u+2*s+5)*n) := calc
    _ ≤ (s+4)*2^(k*n) := by
      rw [show (s+4)*2^(k*n) = (s+2)*2^(k*n)+2*2^(k*n) by ring]
      exact Nat.add_le_add_right (Nat.le_mul_of_pos_right (s+2) (by positivity)) _
    _ ≤ 2^(s+4)*2^(k*n) := Nat.mul_le_mul_right _ (Nat.lt_two_pow_self (n := s+4)).le
    _ = 2^(s+4+k*n) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      have h : s+4 ≤ (s+4)*n := Nat.le_mul_of_pos_right _ hn
      rw [show (e+u+2*s+5)*n = (s+4)*n+k*n by dsimp [k]; ring]
      exact Nat.add_le_add_right h _)
  change 2*(s*a^2)+1 ≤ _
  calc
    _ ≤ 2*((s+1)*a^2) := by
      rw [Nat.add_mul,one_mul,Nat.mul_add]
      have := Nat.one_le_pow 2 a ha
      omega
    _ ≤ 2*((2^(s+1))*(2^(2^(k*n)))^2) := by
      gcongr
      exact (Nat.lt_two_pow_self (n := s+1)).le
    _ = 2^(s+2+2*2^(k*n)) := by
      change 2^1*(2^(s+1)*(2^(2^(k*n)))^2) = _
      rw [← pow_mul,← pow_add,← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hbound

private noncomputable def symmetricMoves (S : Finset G) : Finset G := by
  classical
  exact S ∪ S⁻¹

private theorem symmetric_completion (S : Finset G) : SymmetricMoves (symmetricMoves S) := by
  classical
  intro g hg
  change g ∈ S ∪ S⁻¹ at hg
  rcases Finset.mem_union.mp hg with h | h
  · exact Finset.mem_union_right _ (Finset.inv_mem_inv h)
  · obtain ⟨u,hu,rfl⟩ := Finset.mem_inv.mp h
    exact Finset.mem_union_left _ (by simpa using hu)

private theorem card_symmetric_completion (S : Finset G) : (symmetricMoves S).card ≤ 2*S.card := by
  classical
  exact (Finset.card_union_le S S⁻¹).trans_eq (by rw [Finset.card_inv,two_mul])

private theorem bot_relative_palettes (J : Subgroup G) (hact : BorelAction G X)
    (hstab : ∀ (g : G) (x : X), g • x = x → g ∈ J) :
    HasRelativePalettes J (⊥ : Subgroup G) X := by
  classical
  intro S hS B _ hB
  let T := symmetricMoves S
  let e : Fin T.card ≃ ↥T := (finCongr (Fintype.card_coe T).symm).trans (Fintype.equivFin ↥T).symm
  let edge (i : Fin T.card) (x : X) := (e i).val • x
  have hT : ∀ g ∈ T, g ∉ J := by
    intro g hg hJ
    rcases Finset.mem_union.mp hg with hs | hi
    · exact hS g hs hJ
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_inv.mp hi
      exact hS u hu (by simpa using J.inv_mem hJ)
  have hSym : FiniteNeighborColoring.Symmetric edge := by
    intro i x _
    obtain ⟨j,hj⟩ := e.surjective ⟨(e i).val⁻¹,symmetric_completion S (e i).property⟩
    refine ⟨j,?_⟩
    change (e j).val • ((e i).val • x) = x
    rw [congrArg Subtype.val hj,inv_smul_smul]
  obtain ⟨c,hc,hcproper⟩ := FiniteNeighborColoring.exists_borel_greedy_coloring edge
    (fun i => hact (e i).val) hSym
  have hLe : T.card+1 ≤ 2*S.card+1 := Nat.add_le_add_right (card_symmetric_completion S) 1
  let p := Fin.castLE hLe
  refine ⟨p ∘ c,(measurable_of_finite p).comp hc,?_⟩
  intro g hg b hb x h
  have hb1 : b = 1 := hB hb
  obtain ⟨i,hi⟩ := e.surjective ⟨g,Finset.mem_union_left _ hg⟩
  have hei : edge i x = g • x := congrArg (fun z : ↥T => z.val • x) hi
  apply hcproper i x (fun hx => hS g hg (hstab g x (hei ▸ hx)))
  rw [hei]
  have hh : c x = c ((g*b) • x) := Fin.castLE_injective hLe h
  rwa [hb1,mul_one] at hh

set_option maxHeartbeats 900000 in
private theorem relative_palettes_of_commutator_step (J K N : Subgroup G)
    [K.Normal] [N.Normal] (hKJ : K ≤ J) (hK : IsLocallyFiniteGroup K)
    (hcomm : ⁅K,K⁆ ≤ N) (hact : BorelAction G X)
    (hind : HasRelativePalettes J N X) : HasRelativePalettes J K X := by
  classical
  intro S hS B hBf hBK
  obtain ⟨U,rfl⟩ := hBf
  let B := Subgroup.closure (U : Set G)
  letI : Finite B := finite_of_fg_le_locally_finite hBK ⟨U,rfl⟩ hK
  let e := Nat.card B
  have he : 0 < e := Nat.card_pos
  let T := symmetricMoves S
  have hT : ∀ g ∈ T, g ∉ J := by
    intro g hg hJ
    rcases Finset.mem_union.mp hg with hs | hi
    · exact hS g hs hJ
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_inv.mp hi
      exact hS u hu (by simpa using J.inv_mem hJ)
  have hU : ∀ u ∈ U, u ∈ K := fun u hu => hBK (Subgroup.subset_closure hu)
  let p := QuotientGroup.mk' N
  have hpker : p.ker = N := QuotientGroup.ker_mk' N
  have hpc : ∀ x ∈ K, ∀ y ∈ K, Commute (p x) (p y) := by
    intro x hx y hy
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := N) ⁅x,y⁆).2
      (hcomm (Subgroup.commutator_mem_commutator hx hy))
  have hpow : ∀ u ∈ U, (p u)^e = 1 := by
    intro u hu
    let v : B := ⟨u,Subgroup.subset_closure hu⟩
    have hv : v^e = 1 := pow_card_eq_one'
    exact (map_pow (p.comp B.subtype) v e).symm.trans
      ((congrArg (p.comp B.subtype) hv).trans (map_one _))
  let D (R : ℕ) := conjugateGroup T U (R+1)
  have hD (R : ℕ) : D R ≤ K := conjugateGroup_le T U (R+1) K hU
  have hfin (R : ℕ) : Finite (D R) :=
    finite_of_fg_le_locally_finite (hD R) (conjugateGroup_fg _ _ _) hK
  let M (R : ℕ) := 2*(T.card * (Nat.card ((D R).map p))^2)+1
  have hGrow (R : ℕ) : M R ≤ 2^(2^((e+U.card+2*T.card+5)*(R+1))) := by
    letI : Finite (conjugateGroup T U (R+1)) := hfin R
    have hcard := card_image_conjugateGroup_le T U (R+1) e he.ne' p K hU hpc hpow
    calc
      M R ≤ 2*(T.card*(e^(U.card*(T.card+1)^(R+1)))^2)+1 := by
        dsimp only [M,D]; gcongr
      _ ≤ _ := double_exp_growth e U.card T.card (R+1) he (by omega)
  have hInd : HasRelativePalettes J p.ker X := hpker.symm ▸ hind
  obtain ⟨c,hc,hproper⟩ := exists_radical_compressed_palette T (symmetric_completion S)
    (fun h => hT 1 h J.one_mem) B hact M _ hGrow (by
      intro R
      letI : Finite (D R) := hfin R
      obtain ⟨q,hq,hEdge,hInv⟩ := exists_invariant_palette_of_finite_subgroup J p (D R)
        ((hD R).trans hKJ) T hT hact hInd
      exact ⟨q,hq,hEdge,fun w hw b hb x => hInv _ (conj_mem_conjugateGroup T U (R+1) hw hb) x⟩)
  have hLe : T.card+1 ≤ 2*S.card+1 := Nat.add_le_add_right (card_symmetric_completion S) 1
  let f := Fin.castLE hLe
  exact ⟨f ∘ c,(measurable_of_finite f).comp hc,fun g hg b hb x h =>
    hproper g (Finset.mem_union_left _ hg) b hb x (Fin.castLE_injective hLe h)⟩

private def derivedKernel (L : Subgroup G) (n : ℕ) : Subgroup G :=
  (derivedSeries L n).map L.subtype

omit [Countable G] in
@[simp] private theorem derivedKernel_zero (L : Subgroup G) : derivedKernel L 0 = L := by
  rw [derivedKernel,derivedSeries_zero,← MonoidHom.range_eq_map,L.range_subtype]

omit [Countable G] in
private theorem derivedKernel_succ (L : Subgroup G) (n : ℕ) :
    derivedKernel L (n+1) = ⁅derivedKernel L n,derivedKernel L n⁆ := by
  simp only [derivedKernel,derivedSeries_succ,Subgroup.map_commutator]

private instance derivedKernel_normal (L : Subgroup G) [L.Normal] (n : ℕ) :
    (derivedKernel L n).Normal := by
  induction n with
  | zero => rw [derivedKernel_zero]; infer_instance
  | succ n ih => rw [derivedKernel_succ]; infer_instance

omit [Countable G] in
private theorem derivedKernel_le (L : Subgroup G) (n : ℕ) : derivedKernel L n ≤ L := by
  rintro _ ⟨a,_,rfl⟩
  exact a.property

/-- A locally finite solvable normal subgroup has Borel palettes with a bound
depending only on the number of tested moves outside the forbidden subgroup. -/
theorem relative_palettes_of_locally_finite_solvable (J L : Subgroup G)
    [L.Normal] [IsSolvable L] (hLJ : L ≤ J) (hL : IsLocallyFiniteGroup L)
    (hact : BorelAction G X) (hstab : ∀ (g : G) (x : X), g • x = x → g ∈ J) :
    HasRelativePalettes J L X := by
  obtain ⟨n,hn⟩ := IsSolvable.solvable (G := L)
  have hbase : HasRelativePalettes J (derivedKernel L n) X := by
    rw [derivedKernel,hn,Subgroup.map_bot]
    exact bot_relative_palettes J hact hstab
  have hdown (m : ℕ) (hm : HasRelativePalettes J (derivedKernel L (m+1)) X) :
      HasRelativePalettes J (derivedKernel L m) X := by
    have hl := derivedKernel_le L m
    have hLf := IsLocallyFiniteGroup.of_injective (Subgroup.inclusion hl)
      (Subgroup.inclusion_injective hl) hL
    apply relative_palettes_of_commutator_step J (derivedKernel L m) (derivedKernel L (m+1))
      (hl.trans hLJ) hLf (derivedKernel_succ L m).ge hact hm
  have fall (m : ℕ) (hm : HasRelativePalettes J (derivedKernel L m) X) :
      HasRelativePalettes J (derivedKernel L 0) X := by
    induction m with
    | zero => exact hm
    | succ m ih => exact ih (hdown m hm)
  have hzero := fall n hbase
  rwa [derivedKernel_zero] at hzero

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.RadicalPalettes

-- BEGIN COMPLETE MODULE HirschProof.TaggedRelativePalettes
section
                                      
                                     
                                  

set_option autoImplicit false

namespace LocalHirschHyperfinite.TaggedSpace

variable {G Γ X : Type*} [Group G] [Group Γ] [MulAction G X]
variable {Z : Set X} {q : G →* Γ}

/-- The physical coordinate normalized by the lift of a point's tag. -/
def normalizedPoint (s : Γ → G) (x : TaggedSpace Z Γ) : X := (s (tag x))⁻¹ • x.1.val

/-- The finite exceptional labels and the scale bound furnished by the
lattice computation. Each branch is tested only when it differs from pure
right translation. -/
def ExceptionalLabels (L : Subgroup G) (s : Γ → G)
    (S : Finset (taggedExtension Z q)) (D : Subgroup (taggedExtension Z q)) (N : ℕ) : Prop :=
  ∃ C A : Finset G, C.card ≤ N ∧ (∀ c ∈ C, q c ≠ 1) ∧ (∀ a ∈ A, a ∈ L) ∧
    ∀ l ∈ D, ∀ c ∈ S, ∀ d ∈ D, ∀ x : TaggedSpace Z Γ,
      (l*c*d) • x ≠ rightTag Z (taggedProjection Z q c) x →
      ∃ g ∈ C, ∃ a ∈ A, normalizedPoint s ((l*c*d) • x) = (g*a) • normalizedPoint s x

variable {Q : Type*} [Group Q]

/-- Finite residual branch data and coset representatives. The finite
relation is allowed to retain explicitly the cases in the denominator bound. -/
structure ResidualPaletteData (π : G →* Q) (s : Γ → G)
    (S : Finset (taggedExtension Z q)) (D : Subgroup (taggedExtension Z q)) (N : ℕ) where
  tags : Finset Γ
  labels : Finset G
  outer : Finset G
  card_outer : outer.card ≤ N
  outer_off : ∀ c ∈ outer, q c ≠ 1
  admissible : Γ → Γ → G → taggedExtension Z q → Prop
  branch : ∀ l ∈ D, ∀ c ∈ S, ∀ d ∈ D, ∀ x : TaggedSpace Z Γ,
    (l*c*d) • x ≠ rightTag Z (taggedProjection Z q c) x →
    let y := (l*c*d) • x
    tag x ∈ tags ∧ tag y ∈ tags ∧ ∃ g ∈ labels,
      admissible (tag x) (tag y) g c ∧ y.1.val = g • x.1.val
  represent : ∀ t ∈ tags, ∀ u ∈ tags, ∀ g ∈ labels, ∀ c ∈ S,
    admissible t u g c →
    ∃ o ∈ outer, ∃ a : G, π ((s u)⁻¹*g*s t) = π (o*a) ∧
      ∀ x : Z, a • ((s t)⁻¹ • x.val) = (s t)⁻¹ • x.val

/-- Choosing corrections for the finite branch list gives one finite list in
the physical radical, even though the underlying action has infinitely many
points. -/
theorem ResidualPaletteData.exceptionalLabels {π : G →* Q} {s : Γ → G}
    {S : Finset (taggedExtension Z q)} {D : Subgroup (taggedExtension Z q)} {N : ℕ}
    (data : ResidualPaletteData π s S D N) : ExceptionalLabels π.ker s S D N := by
  classical
  let Raw := (↑data.tags : Type _) × (↑data.tags : Type _) × (↑data.labels : Type _) × (↑S : Type _)
  let Idx := {p : Raw // data.admissible p.1.val p.2.1.val p.2.2.1.val p.2.2.2.val}
  let delta (i : Idx) := (s i.val.2.1.val)⁻¹ * i.val.2.2.1.val * s i.val.1.val
  have hi (i : Idx) : ∃ o ∈ data.outer, ∃ a : G,
      π (delta i) = π (o*a) ∧
      ∀ x : Z, a • ((s i.val.1.val)⁻¹ • x.val) = (s i.val.1.val)⁻¹ • x.val :=
    data.represent _ i.val.1.property _ i.val.2.1.property _ i.val.2.2.1.property
      _ i.val.2.2.2.property i.property
  choose o ho a hπ hfix using hi
  let b (i : Idx) := (o i)⁻¹ * delta i * (a i)⁻¹
  have hb (i : Idx) : b i ∈ π.ker := by
    change π ((o i)⁻¹ * delta i * (a i)⁻¹) = 1
    rw [map_mul,map_mul,map_inv,map_inv,hπ,map_mul]
    group
  letI : Fintype Idx := Fintype.ofFinite Idx
  let A := Finset.univ.image b
  refine ⟨data.outer,A,data.card_outer,data.outer_off,?_,?_⟩
  · intro l hl
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hl
    exact hb i
  · intro l hl c hc d hd x hne
    obtain ⟨ht,hu,g,hg,hAdm,hphys⟩ := data.branch l hl c hc d hd x hne
    let y := (l*c*d) • x
    let i : Idx := ⟨(⟨tag x,ht⟩,⟨tag y,hu⟩,⟨g,hg⟩,⟨c,hc⟩),hAdm⟩
    have hba : b i ∈ A := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    refine ⟨o i,ho i,b i,hba,?_⟩
    have hNorm : normalizedPoint s y = delta i • normalizedPoint s x := by
      change (s (tag y))⁻¹ • y.1.val =
        ((s (tag y))⁻¹ * g * s (tag x)) • ((s (tag x))⁻¹ • x.1.val)
      rw [hphys]
      simp only [mul_smul,smul_inv_smul]
    have hF : a i • normalizedPoint s x = normalizedPoint s x := hfix i x.1
    have hF' : (a i)⁻¹ • normalizedPoint s x = normalizedPoint s x := by
      calc
        _ = (a i)⁻¹ • (a i • normalizedPoint s x) := congrArg ((a i)⁻¹ • ·) hF.symm
        _ = _ := inv_smul_smul _ _
    have hCancel : o i * b i = delta i * (a i)⁻¹ := by dsimp [b]; group
    change normalizedPoint s y = (o i * b i) • normalizedPoint s x
    rw [hNorm,hCancel]
    simp only [mul_smul,hF']

section Borel

/-- The tagged space of a measurable core is standard Borel when the tag
group has its countable discrete measurable structure. -/
theorem standardBorel_tagged {Γ X : Type*} {Z : Set X}
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Γ]
    [Countable Γ] [MeasurableSingletonClass Γ] (hZ : MeasurableSet Z) :
    StandardBorelSpace (TaggedSpace Z Γ) := by
  letI : StandardBorelSpace Z := hZ.standardBorel
  infer_instance

variable [Countable G] [Countable Γ] [MeasurableSpace X] [StandardBorelSpace X]
variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [StandardBorelSpace (TaggedSpace Z Γ)]

theorem measurable_normalizedPoint (s : Γ → G) (hX : BorelAction G X) :
    Measurable (normalizedPoint s : TaggedSpace Z Γ → X) := by
  let f (z : X × Γ) : X := (s z.2)⁻¹ • z.1
  have hf : Measurable f := measurable_from_prod_countable_left fun t => hX (s t)⁻¹
  exact hf.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd.fst)

theorem exists_tag_palette (S : Finset (taggedExtension Z q)) (hS : SymmetricMoves S)
    (hoff : ∀ c ∈ S, taggedProjection Z q c ≠ 1) :
    ∃ f : Γ → Fin (S.card+1), Measurable f ∧
      ∀ c ∈ S, ∀ t, f t ≠ f (t * (taggedProjection Z q c)⁻¹) := by
  classical
  let e : Fin S.card ≃ ↥S :=
    (finCongr (Fintype.card_coe S).symm).trans (Fintype.equivFin ↥S).symm
  let v (i : Fin S.card) : Γ := taggedProjection Z q (e i).val
  let edge (i : Fin S.card) (t : Γ) := t * (v i)⁻¹
  have he : FiniteNeighborColoring.Symmetric edge := by
    intro i t _
    obtain ⟨j,hj⟩ := e.surjective ⟨(e i).val⁻¹,hS (e i).property⟩
    have hj' : v j = (v i)⁻¹ := by
      have hw := congrArg (fun a : S => taggedProjection Z q a.val) hj
      simpa [v] using hw
    exact ⟨j,by simp [edge,hj',mul_assoc]⟩
  obtain ⟨seed,hseed⟩ := Countable.exists_injective_nat Γ
  have hp : FiniteNeighborColoring.Proper edge seed := fun _i _t h => hseed.ne h.symm
  let f := FiniteNeighborColoring.greedyColor edge seed
  have hf := FiniteNeighborColoring.greedyColor_proper edge he hp
  refine ⟨f, measurable_of_countable f, fun c hc t => ?_⟩
  obtain ⟨i,hi⟩ := e.surjective ⟨c,hc⟩
  have he' : v i = taggedProjection Z q c := congrArg (fun a : S => taggedProjection Z q a.val) hi
  rw [← he']
  apply hf i t
  intro ht
  have hh : (v i)⁻¹ = 1 := mul_left_cancel (show t * (v i)⁻¹ = t * 1 by simpa [edge] using ht)
  exact hoff c hc (by simpa [he'] using hh)

/-- Finite exceptional branches use the physical relative palette, and
pure right translations use the tag palette. Selecting one representative
in each finite orbit gives the invariant approximate palette. -/
theorem exists_invariant_tagged_palette (L : Subgroup G) (s : Γ → G)
    (S : Finset (taggedExtension Z q)) (hS : SymmetricMoves S)
    (hoff : ∀ c ∈ S, taggedProjection Z q c ≠ 1)
    (D : Subgroup (taggedExtension Z q)) [Finite D] (N : ℕ)
    (hlabel : ExceptionalLabels L s S D N)
    (hpal : HasRelativePalettes q.ker L X)
    (hZ : MeasurableSet Z) (hX : BorelAction G X) :
    ∃ f : TaggedSpace Z Γ → Fin ((2*N+1)*(S.card+1)), Measurable f ∧
      (∀ c ∈ S, ∀ x, f x ≠ f (c • x)) ∧
      (∀ d ∈ D, ∀ x, f (d • x) = f x) := by
  classical
  obtain ⟨C,A,hCN,hC,hA,hMove⟩ := hlabel
  let A' := Subgroup.closure (A : Set G)
  have hA' : A' ≤ L := (Subgroup.closure_le _).2 hA
  obtain ⟨p,hp,hProper⟩ := hpal C hC A' ⟨A,rfl⟩ hA'
  obtain ⟨k,hk,hkProper⟩ := exists_tag_palette (Z := Z) (q := q) S hS hoff
  have hF (x : TaggedSpace Z Γ) : {y | orbitRel D x y}.Finite :=
    (Set.finite_range (fun d : D => d • x)).subset (fun _ ⟨d,hd⟩ => ⟨d,hd⟩)
  have hYZ := borel_taggedAction Z q hZ hX
  obtain ⟨r,hr,hrmem,hrconst⟩ :=
    exists_finite_orbit_selector (G := D) (fun d => hYZ d.val) hF
  let base (x : TaggedSpace Z Γ) := (p (normalizedPoint s x), k (tag x))
  have hbase : Measurable base :=
    (hp.comp (measurable_normalizedPoint s hX)).prodMk (hk.comp measurable_snd.fst)
  have hDbl (l c d : taggedExtension Z q) (hl : l ∈ D) (hc : c ∈ S) (hd : d ∈ D)
      (x : TaggedSpace Z Γ) : base x ≠ base ((l*c*d) • x) := by
    intro he
    by_cases hmove : (l*c*d) • x = rightTag Z (taggedProjection Z q c) x
    · have h := congrArg Prod.snd he
      exact hkProper c hc (tag x) (by simpa [base,hmove,rightTag] using h)
    · obtain ⟨g,hg,a,ha,hlabel⟩ := hMove l hl c hc d hd x hmove
      have h := congrArg Prod.fst he
      exact hProper g hg a (Subgroup.subset_closure ha) (normalizedPoint s x)
        (by simpa only [base,hlabel] using h)
  have hcap : (2*C.card+1)*(S.card+1) ≤ (2*N+1)*(S.card+1) :=
    Nat.mul_le_mul_right _ (by omega)
  let e : Fin (2*C.card+1) × Fin (S.card+1) ↪ Fin ((2*N+1)*(S.card+1)) :=
    finProdFinEquiv.toEmbedding.trans ⟨Fin.castLE hcap, Fin.castLE_injective hcap⟩
  refine ⟨fun x => e (base (r x)),(measurable_of_finite e).comp (hbase.comp hr),?_,?_⟩
  · intro c hc x heq
    obtain ⟨l,hl⟩ := hrmem (c • x)
    obtain ⟨d,hd⟩ := hrmem x
    have hmove : (l.val*c*d.val⁻¹) • r x = r (c • x) := by
      rw [← hl,← hd]
      change (l.val*c*d.val⁻¹) • (d.val • x) = l.val • (c • x)
      simp only [mul_smul,inv_smul_smul]
    exact hDbl l.val c d.val⁻¹ l.property hc (D.inv_mem d.property) (r x)
      ((e.injective heq).trans (congrArg base hmove).symm)
  · intro d hd x
    exact congrArg (fun v => e (base v)) (hrconst x (d • x) ⟨⟨d,hd⟩,rfl⟩).symm

/-- Apply invariant approximate palettes at every radius and compress to a
palette depending only on the outer list. -/
theorem kernelPalettes_of_exceptionalLabels (L : Subgroup G)
    (hpal : HasRelativePalettes q.ker L X)
    (hZ : MeasurableSet Z) (hX : BorelAction G X)
    (horbits : ChartModel.FiniteKernelOrbitBounds (taggedProjection Z q)
      (fun _ : TaggedSpace Z Γ => ()))
    (hlabel : ∀ (S : Finset (taggedExtension Z q)), SymmetricMoves S →
      (∀ c ∈ S, taggedProjection Z q c ≠ 1) →
      ∀ (U : Finset (taggedExtension Z q)), (∀ u ∈ U, taggedProjection Z q u = 1) →
        ∃ (s : Γ → G) (N : ℕ → ℕ) (b : ℕ),
          (∀ R, (2*N R+1)*(S.card+1) ≤ 2^(2^(b*(R+1)))) ∧
          (∀ R, ExceptionalLabels L s S (conjugateGroup S U (R+1)) (N R))) :
    ChartModel.HasKernelPalettes (taggedProjection Z q) (TaggedSpace Z Γ) := by
  classical
  intro C hC
  let S := C ∪ C.image Inv.inv
  have hSym : SymmetricMoves S := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)
    · obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_union_left _ (by simpa using hc)
  have hoff : ∀ c ∈ S, taggedProjection Z q c ≠ 1 := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact hC c hc
    · obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hc
      rw [← he]
      intro hh
      apply hC a ha
      simpa [map_inv] using congrArg Inv.inv hh
  have hOne : (1 : taggedExtension Z q) ∉ S := fun h => hoff 1 h (map_one _)
  refine ⟨S.card+1,fun B hB hBK => ?_⟩
  obtain ⟨U,rfl⟩ := hB
  have hU : ∀ u ∈ U, taggedProjection Z q u = 1 :=
    fun _ hu => hBK (Subgroup.subset_closure hu)
  obtain ⟨s,N,b,hGrowth,hLab⟩ := hlabel S hSym hoff U hU
  let M (R : ℕ) := (2*N R+1)*(S.card+1)
  let D (R : ℕ) := conjugateGroup S U (R+1)
  have hYZ := borel_taggedAction Z q hZ hX
  have hApprox (R : ℕ) : ∃ p : TaggedSpace Z Γ → Fin (M R), Measurable p ∧
      (∀ c ∈ S, ∀ x, p x ≠ p (c • x)) ∧
      (∀ w ∈ wordBall S (R+1), ∀ a ∈ Subgroup.closure (U : Set (taggedExtension Z q)),
        ∀ x, p ((w*a*w⁻¹) • x) = p x) := by
    have hDproj : D R ≤ (taggedProjection Z q).ker := conjugateGroup_le S U (R+1)
      (taggedProjection Z q).ker hU
    letI : Finite (D R) := finite_kernel_subgroup_of_orbitBounds horbits (D R)
      (conjugateGroup_fg S U (R+1)) hDproj
    obtain ⟨p,hp,he,hD⟩ := exists_invariant_tagged_palette L s S hSym hoff (D R) (N R)
      (hLab R) hpal hZ hX
    exact ⟨p,hp,he,fun w hw a ha => hD _ (conj_mem_conjugateGroup S U (R+1) hw ha)⟩
  obtain ⟨p,hp,hr⟩ := exists_radical_compressed_palette S hSym hOne
    (Subgroup.closure (U : Set (taggedExtension Z q))) hYZ M b hGrowth hApprox
  exact ⟨p,hp,fun c hc => hr c (Finset.mem_union_left _ hc)⟩

end Borel
end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.TaggedRelativePalettes

-- BEGIN COMPLETE MODULE HirschProof.TaggedResidualCosets
section
                                         

set_option autoImplicit false

namespace LocalHirschHyperfinite.TaggedSpace

variable {G Γ X Q : Type*} [Group G] [Group Γ] [Group Q] [MulAction G X]
variable {Z : Set X} {q : G →* Γ}

/-- The finite coset calculation for exceptional branches. The working
subgroup may contain the normalized residuals of arbitrarily long kernel
moves. The outer palette depends on the coset bound, while the list of
radical corrections only needs to be finite. -/
theorem exceptionalLabels_of_residual_cosets (π : G →* Q) (s c₀ : Γ → G)
    (hc₀ : ∀ v, q (c₀ v) = v)
    (I : Subgroup Q) (P : Subgroup I) (H : Γ → Subgroup I)
    (T : Finset Γ) (A : Finset G) (S : Finset (taggedExtension Z q))
    (D : Subgroup (taggedExtension Z q)) (M : ℕ)
    (hOff : ∀ c ∈ S, taggedProjection Z q c ≠ 1)
    (hfinite : ∀ t ∈ T, (H t).IsFiniteRelIndex P)
    (hIndex : ∀ t ∈ T, (H t).relIndex P ≤ M)
    (hLift : ∀ b : P, ∃ g : G, π g = b.val.val ∧ q g = 1)
    (hfix : ∀ t ∈ T, ∀ a ∈ H t, ∃ d : G, π d = a.val ∧
      ∀ x : Z, d • ((s t)⁻¹ • x.val) = (s t)⁻¹ • x.val)
    (hres : ∀ l ∈ D, ∀ c ∈ S, ∀ d ∈ D, ∀ x : TaggedSpace Z Γ,
      (l*c*d) • x ≠ rightTag Z (taggedProjection Z q c) x →
      let y := (l*c*d) • x
      tag x ∈ T ∧ tag y ∈ T ∧ ∃ g ∈ A, y.1.val = g • x.1.val ∧
        ∃ b : P, π (((c₀ (taggedProjection Z q c))⁻¹) * (s (tag y))⁻¹ * g * s (tag x)) =
          b.val.val) :
    ExceptionalLabels π.ker s S D (T.card * M * S.card) := by
  classical
  let J (t : T) := (H t.val).subgroupOf P
  let Cos (t : T) := P ⧸ J t
  letI (t : T) : (H t.val).IsFiniteRelIndex P := hfinite t.val t.property
  letI (t : T) : (J t).FiniteIndex := inferInstance
  letI (t : T) : Fintype (Cos t) := Fintype.ofFinite (P ⧸ J t)
  let toCos (t : T) : P → Cos t := QuotientGroup.mk
  choose b hb using fun t : T =>
    (show Function.Surjective (toCos t) from QuotientGroup.mk_surjective).hasRightInverse
  choose g hgπ hgq using hLift
  let Idx := (Σ t : T, Cos t) × (↑S : Type _)
  let outer (a : Idx) : G := c₀ (taggedProjection Z q a.2.val) * g (b a.1.1 a.1.2)
  let C := Finset.univ.image outer
  have hcap : C.card ≤ T.card * M * S.card := by
    refine Finset.card_image_le.trans ?_
    simp only [Idx,Finset.card_univ,Fintype.card_prod,Fintype.card_sigma,Fintype.card_coe]
    apply Nat.mul_le_mul_right
    calc
      ∑ t : T, Fintype.card (Cos t) ≤ ∑ _t : T, M := by
        apply Finset.sum_le_sum
        intro t _
        rw [← Nat.card_eq_fintype_card]
        exact hIndex t.val t.property
      _ = T.card * M := by simp
  have hC : ∀ o ∈ C, q o ≠ 1 := by
    intro o ho
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ho
    simpa only [outer,map_mul,hc₀,hgq,mul_one] using hOff a.2.val a.2.property
  let adm (t u : Γ) (g : G) (c : taggedExtension Z q) : Prop :=
    ∃ b : P, π (((c₀ (taggedProjection Z q c))⁻¹) * (s u)⁻¹ * g * s t) = b.val.val
  let data : ResidualPaletteData π s S D (T.card*M*S.card) := {
    tags := T
    labels := A
    outer := C
    card_outer := hcap
    outer_off := hC
    admissible := adm
    branch := by
      intro l hl c hc d hd x hne
      obtain ⟨ht,hu,g,hg,hphys,hres⟩ := hres l hl c hc d hd x hne
      exact ⟨ht,hu,g,hg,hres,hphys⟩
    represent := by
      intro t ht u hu p hp c hc he
      obtain ⟨w,hw⟩ := he
      let t' : T := ⟨t,ht⟩
      let j := toCos t' w
      let w₀ := b t' j
      have hEq : QuotientGroup.mk w₀ = (QuotientGroup.mk w : Cos t') := hb t' j
      have hmem : w₀⁻¹ * w ∈ J t' :=
        QuotientGroup.leftRel_apply.mp (Quotient.exact' hEq)
      let a : I := (w₀⁻¹ * w).val
      obtain ⟨d,hd,hdFix⟩ := hfix t ht a hmem
      let k : Idx := (⟨t',j⟩,⟨c,hc⟩)
      refine ⟨outer k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩,d,?_,hdFix⟩
      let f := c₀ (taggedProjection Z q c)
      let δ := (s u)⁻¹*p*s t
      have hh : π f⁻¹ * π δ = w.val.val := by
        rw [← map_mul]
        convert hw using 2 <;> simp only [δ,f] <;> group
      have hh' : π δ = π f * w.val.val := by
        rw [← hh,map_inv,mul_inv_cancel_left]
      have hprod : w₀.val.val * a.val = w.val.val := by
        change w₀.val.val * (w₀⁻¹*w).val.val = w.val.val
        simp [mul_assoc]
      change π δ = π ((f * g w₀) * d)
      simpa only [map_mul,hgπ,hd,mul_assoc,hprod] using hh' }
  exact data.exceptionalLabels

end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.TaggedResidualCosets

-- BEGIN COMPLETE MODULE HirschProof.TriangularWordBounds
section
                                   
                                         
                                          

set_option autoImplicit false

open scoped BigOperators

namespace LocalHirschHyperfinite.TriangularWordBounds

variable {K : Type*} [CommRing K] {n : ℕ}

abbrev Square (K : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) K

/-- One power of the fixed denominator clears every entry. -/
def Cleared (O : Subring K) (q : K) (d : ℕ) (A : Square K n) : Prop :=
  ∀ i j, q ^ d * A i j ∈ O

lemma clear_mul {O : Subring K} {q x y : K} {d e : ℕ}
    (hx : q ^ d * x ∈ O) (hy : q ^ e * y ∈ O) :
    q ^ (d + e) * (x * y) ∈ O := by
  rw [pow_add, mul_mul_mul_comm]
  exact O.mul_mem hx hy

lemma clear_mono {O : Subring K} {q x : K} (hq : q ∈ O) {d e : ℕ}
    (hde : d ≤ e) (hx : q ^ d * x ∈ O) : q ^ e * x ∈ O := by
  rw [← Nat.sub_add_cancel hde, pow_add, mul_assoc]
  exact O.mul_mem (O.pow_mem hq _) hx

lemma Cleared.mono {O : Subring K} {q : K} (hq : q ∈ O) {d e : ℕ}
    {A : Square K n} (hde : d ≤ e) (hA : Cleared O q d A) :
    Cleared O q e A :=
  fun i j => clear_mono hq hde (hA i j)

lemma Cleared.one (O : Subring K) (q : K) :
    Cleared (n := n) O q 0 1 := by
  intro i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

lemma Cleared.mul {O : Subring K} {q : K} {d e : ℕ} {A B : Square K n}
    (hA : Cleared O q d A) (hB : Cleared O q e B) :
    Cleared O q (d + e) (A * B) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact O.sum_mem fun k _ => clear_mul (hA i k) (hB k j)

/-- A word of length `l` in letters cleared by `q^d` is cleared by `q^(d*l)`. -/
theorem cleared_word {O : Subring K} {q : K} {d : ℕ}
    (w : List (Square K n)) (hw : ∀ A ∈ w, Cleared O q d A) :
    Cleared O q (d * w.length) w.prod := by
  induction w with
  | nil => simpa using Cleared.one (n := n) O q
  | cons A w ih =>
      simp only [List.length_cons, List.prod_cons, Nat.mul_succ]
      rw [Nat.add_comm]
      exact (hw A (List.mem_cons_self ..)).mul (ih fun B hB => hw B (List.mem_cons_of_mem _ hB))

/-- Weighted clearance on the upper triangular algebra. The clearing
power on the `j-i` superdiagonal is `q^(d*(j-i))`. -/
def UpperCleared (O : Subring K) (q : K) (d : ℕ) (A : Square K n) : Prop :=
  (∀ i j, j < i → A i j = 0) ∧
    ∀ i j, q ^ (d * (j.val - i.val)) * A i j ∈ O

/-- The weighted denominator bound on a unitriangular matrix. -/
def TriangularCleared (O : Subring K) (q : K) (d : ℕ) (A : Square K n) : Prop :=
  UpperCleared O q d A ∧ ∀ i, A i i = 1

variable {O : Subring K} {q : K} {d : ℕ} {A B : Square K n}

lemma UpperCleared.one : UpperCleared (n := n) O q d 1 := by
  refine ⟨fun i j h => ?_, fun i j => ?_⟩
  · simp [ne_of_gt h]
  · by_cases h : i = j
    · subst j
      simp
    · simp [h]

lemma UpperCleared.zero : UpperCleared (n := n) O q d 0 := by
  simp [UpperCleared]

lemma UpperCleared.add (hA : UpperCleared O q d A) (hB : UpperCleared O q d B) :
    UpperCleared O q d (A + B) := by
  refine ⟨fun i j h => ?_, fun i j => ?_⟩
  · simp [Matrix.add_apply, hA.1 i j h, hB.1 i j h]
  · rw [Matrix.add_apply, mul_add]
    exact O.add_mem (hA.2 i j) (hB.2 i j)

lemma UpperCleared.sub (hA : UpperCleared O q d A) (hB : UpperCleared O q d B) :
    UpperCleared O q d (A - B) := by
  refine ⟨fun i j h => ?_, fun i j => ?_⟩
  · simp [Matrix.sub_apply, hA.1 i j h, hB.1 i j h]
  · rw [Matrix.sub_apply, mul_sub]
    exact O.sub_mem (hA.2 i j) (hB.2 i j)

lemma UpperCleared.mul (hA : UpperCleared O q d A) (hB : UpperCleared O q d B) :
    UpperCleared O q d (A * B) := by
  refine ⟨fun i j h => ?_, fun i j => ?_⟩
  · rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k < i
    · simp [hA.1 i k hk]
    · simp [hB.1 k j (h.trans_le (le_of_not_gt hk))]
  · rw [Matrix.mul_apply, Finset.mul_sum]
    apply O.sum_mem
    intro k _
    by_cases hki : k < i
    · simp [hA.1 i k hki]
    by_cases hjk : j < k
    · simp [hB.1 k j hjk]
    have hv₁ : i.val ≤ k.val := le_of_not_gt hki
    have hv₂ : k.val ≤ j.val := le_of_not_gt hjk
    have hd : j.val - i.val = (k.val - i.val) + (j.val - k.val) := by omega
    rw [hd, Nat.mul_add]
    exact clear_mul (hA.2 i k) (hB.2 k j)

lemma UpperCleared.pow (hA : UpperCleared O q d A) (k : ℕ) :
    UpperCleared O q d (A ^ k) := by
  induction k with
  | zero => simpa using UpperCleared.one (n := n) (O := O) (q := q) (d := d)
  | succ k hk => simpa only [pow_succ] using hk.mul hA

lemma UpperCleared.sum {ι : Type*} (s : Finset ι) (f : ι → Square K n)
    (hf : ∀ i ∈ s, UpperCleared O q d (f i)) :
    UpperCleared O q d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UpperCleared.zero (n := n) (O := O) (q := q) (d := d)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma UpperCleared.cleared (hq : q ∈ O) (hA : UpperCleared O q d A) :
    Cleared O q (d * n) A := by
  intro i j
  exact clear_mono hq (Nat.mul_le_mul_left d (by omega)) (hA.2 i j)

lemma TriangularCleared.one : TriangularCleared (n := n) O q d 1 :=
  ⟨UpperCleared.one, fun i => Matrix.one_apply_eq i⟩

lemma TriangularCleared.mul (hA : TriangularCleared O q d A)
    (hB : TriangularCleared O q d B) : TriangularCleared O q d (A * B) := by
  classical
  refine ⟨hA.1.mul hB.1, fun i => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [hA.2 i, hB.2 i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · simp [hA.1.1 i k hk]
    · simp [hB.1.1 k i hk]
  · simp

lemma TriangularCleared.of_cleared (hq : q ∈ O)
    (h_lower : ∀ i j, j < i → A i j = 0) (h_diag : ∀ i, A i i = 1)
    (hA : Cleared O q d A) : TriangularCleared O q d A := by
  refine ⟨⟨h_lower, fun i j => ?_⟩, h_diag⟩
  rcases lt_trichotomy i j with h | rfl | h
  · have hdist : 1 ≤ j.val - i.val := by
      have hv : i.val < j.val := h
      omega
    exact clear_mono hq (by simpa using Nat.mul_le_mul_left d hdist) (hA i j)
  · simp [h_diag]
  · simp [h_lower i j h]

/-- Powers of a strictly upper triangular matrix vanish below their
corresponding superdiagonal. -/
lemma strict_upper_pow (hA : ∀ i j, j ≤ i → A i j = 0)
    (k : ℕ) (i j : Fin n) (hij : j.val < i.val + k) :
    (A ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
      rw [pow_zero, Matrix.one_apply]
      have hne : i ≠ j := fun h => by subst j; omega
      simp [hne]
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l.val < i.val + k
      · rw [ih i l hl, zero_mul]
      · have hle : j ≤ l := by change j.val ≤ l.val; omega
        rw [hA l j hle, mul_zero]

lemma strict_upper_nilpotent (hA : ∀ i j, j ≤ i → A i j = 0) : A ^ n = 0 := by
  ext i j
  exact strict_upper_pow hA n i j (by omega)

/-- The finite inverse formula preserves the weighted denominator bound. -/
lemma TriangularCleared.inv (U : (Square K n)ˣ)
    (hU : TriangularCleared O q d (U : Square K n)) :
    TriangularCleared O q d ((U⁻¹ : (Square K n)ˣ) : Square K n) := by
  let N : Square K n := 1 - U.val
  have hN : UpperCleared O q d N := UpperCleared.one.sub hU.1
  have hs : ∀ i j, j ≤ i → N i j = 0 := by
    intro i j hij
    rcases lt_or_eq_of_le hij with h | rfl
    · exact hN.1 i j h
    · simp [N, hU.2]
  have hn : N ^ n = 0 := strict_upper_nilpotent hs
  let V : Square K n := ∑ k ∈ Finset.range n, N ^ k
  have hV : UpperCleared O q d V :=
    UpperCleared.sum _ _ fun k _ => hN.pow k
  have he : V * U.val = 1 := by
    have hgeom := geom_sum_mul_neg N n
    simpa [← show 1 - N = U.val by simp [N], hn, V] using hgeom
  have hv : V = ((U⁻¹ : (Square K n)ˣ) : Square K n) := by
    calc
      V = V * (U.val * (↑U⁻¹ : Square K n)) := by simp
      _ = (U⁻¹ : (Square K n)ˣ).val := by rw [← mul_assoc, he, one_mul]
  rw [← hv]
  refine ⟨hV, fun i => ?_⟩
  have hnpos : 0 < n := i.isLt.pos
  rw [show V i i = ∑ k ∈ Finset.range n, (N ^ k) i i by simp [V, Matrix.sum_apply]]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    exact strict_upper_pow hs k i i (by omega)
  · intro h
    exact (h (Finset.mem_range.mpr hnpos)).elim

/-- The group of unitriangular matrices satisfying the denominator bounds.
Intersecting this with the representation of the rational isolator gives the
group denoted by `𝒫_R` in the manuscript. -/
def triangularDenominatorSubgroup (O : Subring K) (q : K) (d : ℕ) (n : ℕ) :
    Subgroup (Square K n)ˣ where
  carrier := { U | TriangularCleared O q d U.val }
  one_mem' := TriangularCleared.one
  mul_mem' hU hV := TriangularCleared.mul hU hV
  inv_mem' {U} hU := TriangularCleared.inv U hU

/-- Combining an arbitrary left and right move in the weighted subgroup
with a short middle move and a fixed correction retains a linear denominator
exponent. -/
theorem cleared_residual (hq : q ∈ O) {L M R C : Square K n} {e f : ℕ}
    (hL : TriangularCleared O q d L) (hM : Cleared O q e M)
    (hR : TriangularCleared O q d R) (hC : Cleared O q f C) :
    Cleared O q (f + d * n + e + d * n) (C * L * M * R) :=
  ((hC.mul (hL.1.cleared hq)).mul hM).mul (hR.1.cleared hq)

section EntrySize

variable {F : Type*} [SeminormedRing F]

/-- A simultaneous bound for the norms of all entries at a fixed embedding. -/
def EntriesBounded (φ : K →+* F) (c : ℝ) (A : Square K n) : Prop :=
  ∀ i j, ‖φ (A i j)‖ ≤ c

lemma EntriesBounded.mul {φ : K →+* F} {a b : ℝ}
    (ha : 0 ≤ a) (hA : EntriesBounded φ a A) (hB : EntriesBounded φ b B) :
    EntriesBounded φ ((n : ℝ) * (a * b)) (A * B) := by
  intro i j
  rw [Matrix.mul_apply, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑ k : Fin n, ‖φ (A i k * B k j)‖ ≤ ∑ _k : Fin n, a * b := by
      apply Finset.sum_le_sum
      intro k _
      rw [map_mul]
      exact (norm_mul_le _ _).trans (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha)
    _ = (n : ℝ) * (a * b) := by simp

variable [NormOneClass F]

lemma EntriesBounded.one (φ : K →+* F) :
    EntriesBounded (n := n) φ 1 1 := by
  intro i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- A uniform entry bound at an embedding grows at most exponentially in the
length of a matrix word. -/
theorem entriesBounded_word {φ : K →+* F} {c : ℝ} (hc : 1 ≤ c)
    (w : List (Square K n)) (hw : ∀ A ∈ w, EntriesBounded φ c A) :
    EntriesBounded φ ((max (n : ℝ) 1 * c) ^ w.length) w.prod := by
  let C := max (n : ℝ) 1 * c
  have hC : 0 ≤ C := mul_nonneg ((zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_right _ _))
    (zero_le_one.trans hc)
  induction w with
  | nil => simpa using EntriesBounded.one (n := n) φ
  | cons a w ih =>
      have hp := (hw a (List.mem_cons_self ..)).mul (zero_le_one.trans hc)
        (ih fun A hA => hw A (List.mem_cons_of_mem _ hA))
      intro i j
      simp only [List.prod_cons, List.length_cons]
      change ‖φ ((a * w.prod) i j)‖ ≤ C ^ (w.length + 1)
      refine (hp i j).trans ?_
      have hmul : (n : ℝ) * c ≤ C :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hc)
      rw [← mul_assoc, pow_succ']
      exact mul_le_mul_of_nonneg_right hmul (pow_nonneg hC _)

/-- After clearing a short word by a power of the fixed denominator, the
scaled entries still have an exponential norm bound. -/
theorem scaled_entry_word {φ : K →+* F} {c : ℝ} (hc : 1 ≤ c)
    (w : List (Square K n)) (hw : ∀ A ∈ w, EntriesBounded φ c A)
    (d : ℕ) (i j : Fin n) :
    ‖φ (q ^ (d * w.length) * w.prod i j)‖ ≤
      (‖φ q‖ ^ d * (max (n : ℝ) 1 * c)) ^ w.length := by
  have he := entriesBounded_word hc w hw i j
  rw [map_mul, map_pow, mul_pow, pow_mul]
  have hq : ‖(φ q ^ d) ^ w.length‖ ≤ (‖φ q‖ ^ d) ^ w.length := by
    rw [← pow_mul]
    simpa only [pow_mul] using (norm_pow_le (φ q) (d * w.length))
  exact (norm_mul_le _ _).trans
    (mul_le_mul hq he (norm_nonneg _) (pow_nonneg (pow_nonneg (norm_nonneg _) _) _))

end EntrySize

end LocalHirschHyperfinite.TriangularWordBounds

end
-- END COMPLETE MODULE HirschProof.TriangularWordBounds

-- BEGIN COMPLETE MODULE HirschProof.TaggedShortLifts
section
                                      
                                       

set_option autoImplicit false

namespace LocalHirschHyperfinite

variable {G Γ : Type*} [Group G] [Group Γ]

theorem wordBall_mono_alphabet {A B : Finset G} (h : A ⊆ B) (r : ℕ) :
    wordBall A r ⊆ wordBall B r := by
  classical
  induction r with
  | zero => simpa only [wordBall] using Finset.Subset.refl ({1} : Finset G)
  | succ r ih =>
      intro w hw
      rcases wordBall_succ_cases hw with hw | ⟨a,ha,b,hb,rfl⟩
      · exact wordBall_mono B (Nat.le_succ _) (ih hw)
      · exact wordBall_append_mem B (ih ha) (h hb)

theorem exists_list_of_mem_wordBall {A : Finset G} {w : G} {r : ℕ}
    (hw : w ∈ wordBall A r) :
    ∃ xs : List G, (∀ a ∈ xs, a ∈ A) ∧ xs.prod = w ∧ xs.length ≤ r := by
  classical
  induction r generalizing w with
  | zero =>
      have h : w = 1 := by simpa [wordBall] using hw
      exact ⟨[],by simp,by simp [h],by simp⟩
  | succ r ih =>
      rcases wordBall_succ_cases hw with hw | ⟨a,ha,b,hb,rfl⟩
      · obtain ⟨xs,hxs,he,hl⟩ := ih hw
        exact ⟨xs,hxs,he,hl.trans (Nat.le_succ _)⟩
      obtain ⟨xs,hxs,he,hl⟩ := ih ha
      exact ⟨xs ++ [b],by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hxs g hg
        · simpa only [List.mem_singleton.mp hg] using hb,
          by simp [he],by simpa using Nat.succ_le_succ hl⟩

theorem exists_element_lift_of_mem_wordBall (q : G →* Γ)
    (A : Finset G) (T : Finset Γ) (hT : ∀ t ∈ T, ∃ a ∈ A, q a = t)
    (r : ℕ) {t : Γ} (ht : t ∈ wordBall T r) : ∃ a ∈ wordBall A r, q a = t := by
  classical
  induction r generalizing t with
  | zero =>
      have he : t = 1 := by simpa [wordBall] using ht
      exact ⟨1,one_mem_wordBall A _,by simp [he]⟩
  | succ r ih =>
      rcases wordBall_succ_cases ht with ht | ⟨u,hu,v,hv,rfl⟩
      · obtain ⟨a,ha,he⟩ := ih ht
        exact ⟨a,wordBall_mono A (Nat.le_succ _) ha,he⟩
      obtain ⟨a,ha,hea⟩ := ih hu
      obtain ⟨b,hb,heb⟩ := hT v hv
      exact ⟨a*b,wordBall_append_mem A ha hb,by simp [hea,heb]⟩

/-- Choose a global section that lifts all tags in finite word balls
by words of at most the same length. -/
theorem exists_short_lift_section (q : G →* Γ) (hsurj : Function.Surjective q)
    (A : Finset G) (T : Finset Γ) (hT : ∀ t ∈ T, ∃ a ∈ A, q a = t) :
    ∃ s : Γ → G, (∀ t, q (s t) = t) ∧
      ∀ t r, t ∈ wordBall T r → s t ∈ wordBall A r := by
  classical
  let good (t : Γ) := ∃ r, t ∈ wordBall T r
  have h (t : Γ) (ht : good t) := exists_element_lift_of_mem_wordBall q A T hT
    (Nat.find ht) (Nat.find_spec ht)
  let s (t : Γ) : G := if ht : good t then (h t ht).choose else (hsurj t).choose
  refine ⟨s,fun t => ?_,fun t r hr => ?_⟩
  · by_cases ht : good t
    · simpa only [s,dif_pos ht] using (h t ht).choose_spec.2
    · simpa only [s,dif_neg ht] using (hsurj t).choose_spec
  · have ht : good t := ⟨r,hr⟩
    simp only [s,dif_pos ht]
    exact wordBall_mono A (Nat.find_min' ht hr) (h t ht).choose_spec.1

/-- Enlarge the fixed alphabet to include lifts of the whole tag alphabet
and close the physical alphabet under inversion. -/
theorem exists_symmetric_lift_alphabet (q : G →* Γ) (hsurj : Function.Surjective q)
    (P : Finset G) (T : Finset Γ) :
    ∃ A : Finset G, P ⊆ A ∧ SymmetricMoves A ∧ ∀ t ∈ T, ∃ a ∈ A, q a = t := by
  classical
  let B : Finset G := P ∪ T.image (fun t => (hsurj t).choose)
  let A := B ∪ B.image Inv.inv
  refine ⟨A,fun _ hg => Finset.mem_union_left _ (Finset.mem_union_left _ hg),?_,?_⟩
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg)
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mem_union_left _ (by simpa using ha)
  · intro t ht
    exact ⟨(hsurj t).choose,Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht)),(hsurj t).choose_spec⟩

namespace TriangularWordBounds

variable {K : Type*} [CommRing K] {n : ℕ}

theorem cleared_wordBall (ρ : G →* (Square K n)ˣ) {O : Subring K} {z : K}
    (hz : z ∈ O) (A : Finset G) (hA : ∀ a ∈ A, Cleared O z 1 (ρ a).val)
    {g : G} {r : ℕ} (hg : g ∈ wordBall A r) : Cleared O z r (ρ g).val := by
  obtain ⟨xs,hxs,he,hl⟩ := exists_list_of_mem_wordBall hg
  let word : List (Square K n) := xs.map (fun a => (ρ a).val)
  have hw : ∀ a ∈ word, Cleared O z 1 a := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hA b (hxs b hb)
  have hEq : word.prod = (ρ g).val := by
    rw [← he]
    let f : G →* Square K n :=
      { toFun := fun x => (ρ x).val
        map_one' := by simp
        map_mul' := by simp }
    exact (map_list_prod f xs).symm
  have hC := cleared_word word hw
  rw [hEq] at hC
  exact hC.mono hz (by simpa [word] using hl)

end TriangularWordBounds
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.TaggedShortLifts

-- BEGIN COMPLETE MODULE HirschProof.TaggedDenominatorTransport
section
                                   

set_option autoImplicit false

open scoped Pointwise

namespace LocalHirschHyperfinite.TaggedSpace

variable {G Γ X : Type*} [Group G] [Group Γ] [MulAction G X]
variable {Z : Set X} {q : G →* Γ}

/-- Calculate a physical label in the coordinates determined by the
two endpoint tags. -/
def normalizedDisplacement (s : Γ → G) (t u : Γ) (g : G) : G := (s u)⁻¹ * g * s t

lemma normalizedDisplacement_mul (s : Γ → G) (t u v : Γ) (g h : G) :
    normalizedDisplacement s u v g * normalizedDisplacement s t u h =
      normalizedDisplacement s t v (g*h) := by
  unfold normalizedDisplacement
  group

lemma normalizedDisplacement_inv (s : Γ → G) (t u : Γ) (g : G) :
    normalizedDisplacement s u t g⁻¹ = (normalizedDisplacement s t u g)⁻¹ := by
  unfold normalizedDisplacement
  group

lemma normalizedDisplacement_proj (s : Γ → G) (hs : ∀ t, q (s t) = t)
    {t u : Γ} {g : G} (he : q g*t=u) :
    q (normalizedDisplacement s t u g) = 1 := by
  rw [normalizedDisplacement,map_mul,map_mul,map_inv,hs,hs,mul_assoc,he,inv_mul_cancel]

lemma residualDisplacement_proj (s : Γ → G) (hs : ∀ t, q (s t) = t)
    {t u v : Γ} {g : G} (he : q g*t*v⁻¹=u) :
    q ((s v)⁻¹ * normalizedDisplacement s t u g) = 1 := by
  have he' : q g * t = u*v := by rw [← he]; group
  simp only [normalizedDisplacement,map_mul,map_inv,hs]
  rw [mul_assoc u⁻¹,he']
  group

/-- A finite list of physical labels suffices for this element, and all used
normalized displacements lie in the prescribed subgroup. -/
def normalizedTransportGroup (s : Γ → G) (K : Subgroup G) :
    Subgroup (taggedExtension Z q) where
  carrier := { a | ∃ A : Finset G, ∀ x : TaggedSpace Z Γ, ∃ g ∈ A,
    (a • x).1.val = g • x.1.val ∧ tag (a • x) = q g * tag x ∧
    normalizedDisplacement s (tag x) (tag (a • x)) g ∈ K }
  one_mem' := by
    classical
    exact ⟨{1},fun x => ⟨1,by simp,by simp,by simp,by simp [normalizedDisplacement]⟩⟩
  mul_mem' := by
    classical
    intro a b ha hb
    obtain ⟨A,hA⟩ := ha
    obtain ⟨B,hB⟩ := hb
    refine ⟨A*B,fun x => ?_⟩
    obtain ⟨g,hg,hga,hgt,hgn⟩ := hA (b • x)
    obtain ⟨h,hh,hha,hht,hhn⟩ := hB x
    refine ⟨g*h,Finset.mul_mem_mul hg hh,?_,?_,?_⟩
    · rw [mul_smul,hga,hha,mul_smul]
    · rw [mul_smul,hgt,hht,map_mul,mul_assoc]
    · rw [mul_smul,← normalizedDisplacement_mul s (tag x) (tag (b • x))]
      exact K.mul_mem hgn hhn
  inv_mem' := by
    classical
    intro a ha
    obtain ⟨A,hA⟩ := ha
    refine ⟨A.image Inv.inv,fun x => ?_⟩
    obtain ⟨g,hg,hga,hgt,hgn⟩ := hA (a⁻¹ • x)
    rw [smul_inv_smul] at hga hgt hgn
    refine ⟨g⁻¹,Finset.mem_image_of_mem _ hg,?_,?_,?_⟩
    · rw [hga,inv_smul_smul]
    · rw [hgt,map_inv,inv_mul_cancel_left]
    · rw [normalizedDisplacement_inv]
      exact K.inv_mem hgn

/-- Normalized kernel branches of the bounded conjugates lie in any subgroup
that contains the short kernel words. -/
theorem conjugateGroup_normalizedTransport_of_short_kernel_words
    (E : Finset G) (hE : SymmetricMoves E)
    (T : Finset Γ) (s : Γ → G) (hs : ∀ t, q (s t) = t)
    (hShort : ∀ t r, t ∈ wordBall T r → s t ∈ wordBall E r)
    (S B : Finset (taggedExtension Z q)) (hS : SymmetricMoves S)
    (hB : ∀ b ∈ B, taggedProjection Z q b = 1)
    (hTracks : ∀ a ∈ S, TracksTags T a)
    (hSupp : ∀ b ∈ B, taggedPerm Z q b ∈ supportedPerm Z (↑(wordBall T 1) : Set Γ))
    (hLabels : ∀ a, a ∈ S ∨ a ∈ B → ∀ x : TaggedSpace Z Γ, ∃ g ∈ E,
      (a • x).1.val = g • x.1.val ∧
      tag (a • x) = q g * tag x * (taggedProjection Z q a)⁻¹)
    (r : ℕ) (K : Subgroup G)
    (hK : ∀ g, g ∈ wordBall E (3*(1+2*r)) → q g = 1 → g ∈ K) :
    conjugateGroup S B r ≤ normalizedTransportGroup (Z := Z) (q := q) s K := by
  classical
  let F := wordBall T (1+2*r)
  let U := S ∪ B
  apply (Subgroup.closure_le _).2
  rintro _ ⟨⟨w,b⟩,rfl⟩
  let a := w.val*b.val*w.val⁻¹
  have ha : a ∈ conjugateGroup S B r :=
    Subgroup.subset_closure ⟨(w,b),rfl⟩
  have hp := conjugateGroup_supported hTracks 1 r hSupp ha
  have hπ : taggedProjection Z q a = 1 := by simp [a,hB _ b.property]
  have hU : S ⊆ U := fun _ h => Finset.mem_union_left _ h
  have hw := wordBall_mono_alphabet hU r w.property
  have hw' := wordBall_mono_alphabet hU r (wordBall_inv_mem S hS w.property)
  have hb : b.val ∈ U := Finset.mem_union_right _ b.property
  have hwa : a ∈ wordBall U (1+2*r) := by
    have hm := wordBall_mul_mem U (wordBall_append_mem U hw hb) hw'
    simpa only [show r+1+r=1+2*r by omega] using hm
  change ∃ P : Finset G, ∀ x : TaggedSpace Z Γ, ∃ g ∈ P,
    (a • x).1.val = g • x.1.val ∧ tag (a • x) = q g * tag x ∧
    normalizedDisplacement s (tag x) (tag (a • x)) g ∈ K
  refine ⟨wordBall E (1+2*r),fun x => ?_⟩
  by_cases hx : tag x ∈ F
  · have hy : tag (a • x) ∈ F :=
      (supportedPerm_preserves hp x).mpr hx
    obtain ⟨g,hg,hp,hgt⟩ := physical_word_transport
      (fun a ha => hLabels a (Finset.mem_union.mp ha)) (1+2*r) hwa x
    have he : tag (a • x) = q g*tag x := by simpa [hπ] using hgt
    refine ⟨g,hg,hp,he,?_⟩
    let d := normalizedDisplacement s (tag x) (tag (a • x)) g
    have hd : d ∈ wordBall E (3*(1+2*r)) := by
      have hd₁ := wordBall_inv_mem E hE (hShort _ _ hy)
      have hd₂ := hShort _ _ hx
      have hd₃ := wordBall_mul_mem E (wordBall_mul_mem E hd₁ hg) hd₂
      simpa only [d,normalizedDisplacement,show (1+2*r)+(1+2*r)+(1+2*r)=3*(1+2*r) by omega]
        using hd₃
    exact hK d hd (normalizedDisplacement_proj s hs he.symm)
  · have he : a • x = x := hp x hx
    refine ⟨1,one_mem_wordBall E _,?_,?_,?_⟩
    · simp [he]
    · simp [he]
    · simp [he,normalizedDisplacement]

/-- Exceptional residuals have a finite list of full physical labels and a
normalized factorization into the two kernel moves, a short middle move,
and the inverse of the projection lift. -/
theorem exists_exceptional_residual_decomposition (L : Subgroup G)
    (E : Finset G) (hE : SymmetricMoves E)
    (T : Finset Γ) (s : Γ → G) (hs : ∀ t, q (s t) = t)
    (hShort : ∀ t r, t ∈ wordBall T r → s t ∈ wordBall E r)
    (S : Finset (taggedExtension Z q)) (r : ℕ)
    (hProj : ∀ a ∈ S, taggedProjection Z q a ∈ T)
    (hMid : ∀ a ∈ S, ∀ x : TaggedSpace Z Γ, ∃ g ∈ E, (a • x).1.val = g • x.1.val ∧
      tag (a • x) = q g * tag x * (taggedProjection Z q a)⁻¹)
    (D : Subgroup (taggedExtension Z q)) [Finite D]
    (hD : D ≤ normalizedTransportGroup s L)
    (hDsup : D ≤ (supportedPerm Z (↑(wordBall T (1+2*r)) : Set Γ)).comap (taggedPerm Z q))
    (hEx : ∀ l ∈ D, ∀ a ∈ S, ∀ d ∈ D, ∀ x : TaggedSpace Z Γ,
      (l*a*d) • x ≠ rightTag Z (taggedProjection Z q a) x →
      tag x ∈ wordBall T (1+2*r+2) ∧ tag ((l*a*d) • x) ∈ wordBall T (1+2*r+2)) :
    ∃ F : Finset G, ∀ l ∈ D, ∀ a ∈ S, ∀ d ∈ D, ∀ x : TaggedSpace Z Γ,
      (l*a*d) • x ≠ rightTag Z (taggedProjection Z q a) x →
      let y := (l*a*d) • x
      tag x ∈ wordBall T (1+2*r+2) ∧ tag y ∈ wordBall T (1+2*r+2) ∧
      ∃ g ∈ F, y.1.val = g • x.1.val ∧
        let δ := (s (taggedProjection Z q a))⁻¹ * normalizedDisplacement s (tag x) (tag y) g
        q δ = 1 ∧
          ∃ dL dM dD : G, dL ∈ L ∧ dD ∈ L ∧
            dM ∈ wordBall E (1+2*(1+2*r+2)) ∧
            (s (taggedProjection Z q a))⁻¹ ∈ wordBall E 1 ∧
            q ((s (taggedProjection Z q a))⁻¹*dM) = 1 ∧
            δ = (s (taggedProjection Z q a))⁻¹*dL*dM*dD := by
  classical
  let k := 1 + 2*r + 2
  let T' := wordBall T k
  letI : Fintype D := Fintype.ofFinite D
  choose A hA using fun d : D => hD d.property
  let P := Finset.univ.biUnion A
  have hP (d : D) : A d ⊆ P := fun _ hg => Finset.mem_biUnion.mpr ⟨d,Finset.mem_univ _,hg⟩
  have hTag (d : D) (x : TaggedSpace Z Γ) : tag (d.val • x) ∈ T' ↔ tag x ∈ T' := by
    have hh := supportedPerm_mono (Z := Z) (A := (wordBall T (1+2*r) : Set Γ))
      (B := (T' : Set Γ)) (wordBall_mono T (by dsimp [k]; omega)) (hDsup d.property)
    exact supportedPerm_preserves hh x
  refine ⟨P*E*P, fun l hl a ha d hd x hne => ?_⟩
  let y₁ := d • x
  let y₂ := a • y₁
  let y₃ := l • y₂
  have heq : (l*a*d) • x = y₃ := by simp [mul_smul,y₃,y₂,y₁]
  obtain ⟨hx,hy⟩ := hEx l hl a ha d hd x hne
  rw [heq] at hy ⊢
  have hy₁ : tag y₁ ∈ T' := (hTag ⟨d,hd⟩ x).mpr hx
  have hy₂ : tag y₂ ∈ T' := (hTag ⟨l,hl⟩ y₂).mp hy
  obtain ⟨gD,hgD,hbD,htD,hnD⟩ := hA ⟨d,hd⟩ x
  obtain ⟨gM,hgM,hbM,htM⟩ := hMid a ha y₁
  obtain ⟨gL,hgL,hbL,htL,hnL⟩ := hA ⟨l,hl⟩ y₂
  let g := gL*gM*gD
  let v := taggedProjection Z q a
  have hBase : y₃.1.val = g • x.1.val := by
    change y₃.1.val = (gL*gM*gD) • x.1.val
    rw [show y₃.1.val = gL • y₂.1.val from hbL,show y₂.1.val = gM • y₁.1.val from hbM,
      show y₁.1.val = gD • x.1.val from hbD]
    simp only [mul_smul]
  have hProjg : q g*tag x*v⁻¹ = tag y₃ := by
    change q (gL*gM*gD)*tag x*v⁻¹ = tag y₃
    rw [show tag y₃ = q gL*tag y₂ from htL,show tag y₂ = q gM*tag y₁*v⁻¹ from htM,
      show tag y₁ = q gD*tag x from htD]
    simp only [map_mul]
    group
  refine ⟨hx,hy,g,Finset.mul_mem_mul (Finset.mul_mem_mul (hP _ hgL) hgM) (hP _ hgD),hBase,
    residualDisplacement_proj s hs hProjg,?_⟩
  let dL := normalizedDisplacement s (tag y₂) (tag y₃) gL
  let dM := normalizedDisplacement s (tag y₁) (tag y₂) gM
  let dD := normalizedDisplacement s (tag x) (tag y₁) gD
  let c := (s v)⁻¹
  let δ := c * normalizedDisplacement s (tag x) (tag y₃) g
  have hc : c ∈ wordBall E 1 := by
    apply wordBall_inv_mem E hE
    apply hShort
    simpa [v] using wordBall_append_mem T (one_mem_wordBall T 0) (hProj a ha)
  have hm : dM ∈ wordBall E (1+2*k) := by
    have hhL := wordBall_inv_mem E hE (hShort _ _ hy₂)
    have hhR := hShort _ _ hy₁
    have hhM := wordBall_append_mem E (one_mem_wordBall E 0) hgM
    simpa only [dM,normalizedDisplacement,one_mul,show k+(0+1)+k=1+2*k by omega] using
        wordBall_mul_mem E (wordBall_mul_mem E hhL hhM) hhR
  have hδ : δ = c * dL * dM * dD := by
    dsimp [δ,dL,dM,dD,g,normalizedDisplacement]
    group
  have hMiddle : q (c*dM) = 1 := residualDisplacement_proj s hs htM.symm
  exact ⟨dL,dM,dD,hnL,hnD,hm,hc,hMiddle,hδ⟩

section Matrices

open TriangularWordBounds

variable {K : Type*} [CommRing K] {n : ℕ}

/-- Normalized kernel branches of the bounded conjugates retain one
unitriangular denominator bound under arbitrary multiplication. -/
theorem conjugateGroup_normalizedTransport (ρ : G →* (Square K n)ˣ)
    (O : Subring K) (z : K) (hz : z ∈ O)
    (E : Finset G) (hE : SymmetricMoves E)
    (hClear : ∀ g ∈ E, Cleared O z 1 (ρ g).val)
    (T : Finset Γ) (s : Γ → G) (hs : ∀ t, q (s t) = t)
    (hShort : ∀ t r, t ∈ wordBall T r → s t ∈ wordBall E r)
    (hTri : ∀ g : G, q g = 1 →
      (∀ i j : Fin n, j < i → (ρ g).val i j = 0) ∧
      (∀ i : Fin n, (ρ g).val i i = 1))
    (S B : Finset (taggedExtension Z q)) (hS : SymmetricMoves S)
    (hB : ∀ b ∈ B, taggedProjection Z q b = 1)
    (hTracks : ∀ a ∈ S, TracksTags T a)
    (hSupp : ∀ b ∈ B, taggedPerm Z q b ∈ supportedPerm Z (↑(wordBall T 1) : Set Γ))
    (hLabels : ∀ a, a ∈ S ∨ a ∈ B → ∀ x : TaggedSpace Z Γ, ∃ g ∈ E,
      (a • x).1.val = g • x.1.val ∧
      tag (a • x) = q g * tag x * (taggedProjection Z q a)⁻¹)
    (r : ℕ) :
    conjugateGroup S B r ≤ normalizedTransportGroup s
      ((triangularDenominatorSubgroup O z (3*(1+2*r)) n).comap ρ) := by
  refine conjugateGroup_normalizedTransport_of_short_kernel_words E hE T s hs hShort
    S B hS hB hTracks hSupp hLabels r _ (fun g hg hq => ?_)
  have ht := hTri g hq
  exact TriangularCleared.of_cleared hz ht.1 ht.2 (cleared_wordBall ρ hz E hClear hg)

/-- One exponent for both unbounded kernel moves, the short middle move,
and the fixed correction. -/
abbrev mixedDenominatorExponent (n r : ℕ) :=
  1 + (3*(1+2*r))*n + (1+2*(1+2*r+2)) + (3*(1+2*r))*n

/-- Take the common unitriangular denominator bound for the normalized
exceptional factors. -/
theorem exists_exceptional_residuals_with_clearance (ρ : G →* (Square K n)ˣ)
    (O : Subring K) (z : K) (hz : z ∈ O)
    (E : Finset G) (hE : SymmetricMoves E)
    (hClear : ∀ g ∈ E, Cleared O z 1 (ρ g).val)
    (T : Finset Γ) (s : Γ → G) (hs : ∀ t, q (s t) = t)
    (hShort : ∀ t r, t ∈ wordBall T r → s t ∈ wordBall E r)
    (hTri : ∀ g : G, q g = 1 →
      (∀ i j : Fin n, j < i → (ρ g).val i j = 0) ∧
      (∀ i : Fin n, (ρ g).val i i = 1))
    (S : Finset (taggedExtension Z q)) (r : ℕ)
    (hProj : ∀ a ∈ S, taggedProjection Z q a ∈ T)
    (hMid : ∀ a ∈ S, ∀ x : TaggedSpace Z Γ, ∃ g ∈ E, (a • x).1.val = g • x.1.val ∧
      tag (a • x) = q g * tag x * (taggedProjection Z q a)⁻¹)
    (D : Subgroup (taggedExtension Z q)) [Finite D]
    (hD : D ≤ normalizedTransportGroup s
      ((triangularDenominatorSubgroup O z (3*(1+2*r)) n).comap ρ))
    (hDsup : D ≤ (supportedPerm Z (↑(wordBall T (1+2*r)) : Set Γ)).comap (taggedPerm Z q))
    (hEx : ∀ l ∈ D, ∀ a ∈ S, ∀ d ∈ D, ∀ x : TaggedSpace Z Γ,
      (l*a*d) • x ≠ rightTag Z (taggedProjection Z q a) x →
      tag x ∈ wordBall T (1+2*r+2) ∧ tag ((l*a*d) • x) ∈ wordBall T (1+2*r+2)) :
    ∃ F : Finset G, ∀ l ∈ D, ∀ a ∈ S, ∀ d ∈ D, ∀ x : TaggedSpace Z Γ,
      (l*a*d) • x ≠ rightTag Z (taggedProjection Z q a) x →
      let y := (l*a*d) • x
      tag x ∈ wordBall T (1+2*r+2) ∧ tag y ∈ wordBall T (1+2*r+2) ∧
      ∃ g ∈ F, y.1.val = g • x.1.val ∧
        let δ := (s (taggedProjection Z q a))⁻¹ * normalizedDisplacement s (tag x) (tag y) g
        q δ = 1 ∧ TriangularCleared O z (mixedDenominatorExponent n r) (ρ δ).val := by
  obtain ⟨F,hF⟩ := exists_exceptional_residual_decomposition _ E hE T s hs hShort
    S r hProj hMid D hD hDsup hEx
  refine ⟨F,fun l hl a ha d hd x hne => ?_⟩
  obtain ⟨hx,hy,g,hg,hphys,hq,dL,dM,dD,hL,hD',hm,hc,_,hδ⟩ := hF l hl a ha d hd x hne
  refine ⟨hx,hy,g,hg,hphys,hq,?_⟩
  have hCl := cleared_residual hz
    (show TriangularCleared O z (3*(1+2*r)) (ρ dL).val from hL)
    (cleared_wordBall ρ hz E hClear hm)
    (show TriangularCleared O z (3*(1+2*r)) (ρ dD).val from hD')
    (cleared_wordBall ρ hz E hClear hc)
  let δ := (s (taggedProjection Z q a))⁻¹ *
    normalizedDisplacement s (tag x) (tag ((l*a*d) • x)) g
  have he : Cleared O z (mixedDenominatorExponent n r) (ρ δ).val := by
    rw [show δ = (s (taggedProjection Z q a))⁻¹*dL*dM*dD from hδ]
    simpa only [map_mul,Units.val_mul,mixedDenominatorExponent] using hCl
  have ht := hTri δ hq
  exact TriangularCleared.of_cleared hz ht.1 ht.2 he

end Matrices
end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.TaggedDenominatorTransport

-- BEGIN COMPLETE MODULE HirschProof.TaggedShortKernelPalettes
section
                                       
                                             

set_option autoImplicit false

namespace LocalHirschHyperfinite.TaggedSpace

variable {G Γ X Q : Type*} [Group G] [Group Γ] [Group Q] [MulAction G X]
variable {Z : Set X} {q : G →* Γ}

/-- Uniform relative index bounds for a subgroup containing the projected
short words in the quotient kernel. -/
def HasShortKernelIndexBounds (π : G →* Q) (q : G →* Γ) (I : Subgroup Q)
    (H : G → Subgroup I) : Prop :=
  ∀ E : Finset G, ∃ (P : ℕ → Subgroup I) (C : ℕ),
    (∀ r (g : G), g ∈ wordBall E (8*(r+1)) → q g = 1 → ∃ b : P r, b.val.val = π g) ∧
    (∀ r (g : G), g ∈ wordBall E (1+2*r+2) →
      (H g).IsFiniteRelIndex (P r) ∧ (H g).relIndex (P r) ≤ 2^(2^(C*(r+1))))

private lemma palette_count_growth (A C d : ℕ) :
    ∃ b : ℕ, ∀ R : ℕ, (2*(A^(R+1)*2^(2^(2*C*(R+1))))+1)*(d+1) ≤ 2^(2^(b*(R+1))) := by
  let U := A+d+4
  refine ⟨U + 2*C + 1, fun R => ?_⟩
  let k := R+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hA : A^k ≤ 2^(A*k) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := A))) _
  have hd : d+1 ≤ 2^(d+1) := Nat.le_of_lt (Nat.lt_two_pow_self (n := d+1))
  let M := 2^(2*C*k)
  have Mpos : 1 ≤ (2 : ℕ)^(A*k+M) := Nat.succ_le_of_lt (Nat.pow_pos (by decide))
  have hSmall : 2+A*k+(d+1) ≤ U*k := by
    have hdk := Nat.mul_le_mul_left (d+4) hk
    rw [Nat.mul_one] at hdk
    calc
      2+A*k+(d+1) = A*k+(d+3) := by omega
      _ ≤ A*k+(d+4)*k := Nat.add_le_add_left ((show d+3 ≤ d+4 by omega).trans hdk) _
      _ = U*k := by dsimp [U]; ring
  have hOne : U*k ≤ 2^((U+2*C)*k) := by
    apply (Nat.le_of_lt (Nat.lt_two_pow_self (n := U*k))).trans
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right k (by omega))
  have hTwo : M ≤ 2^((U+2*C)*k) := by
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right k (by omega))
  have hExp : 2+A*k+M+(d+1) ≤ 2^((U+2*C+1)*k) := by
    calc
      _ ≤ U*k+M := by omega
      _ ≤ 2^((U+2*C)*k)+2^((U+2*C)*k) := Nat.add_le_add hOne hTwo
      _ = 2^((U+2*C)*k+1) := by rw [pow_succ]; ring
      _ ≤ 2^((U+2*C+1)*k) := by
        apply Nat.pow_le_pow_right (by decide)
        exact (Nat.add_le_add_left hk ((U+2*C)*k)).trans_eq (by ring)
  change (2*(A^k*2^M)+1)*(d+1) ≤ 2^(2^((U+2*C+1)*k))
  have hp : A^k * 2^M ≤ 2^(A*k+M) := by
    exact (Nat.mul_le_mul_right (2^M) hA).trans_eq (pow_add 2 (A*k) M).symm
  calc
    _ ≤ (2*2^(A*k+M)+1)*2^(d+1) :=
      Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 1) hd
    _ ≤ (2^2*2^(A*k+M))*2^(d+1) := Nat.mul_le_mul_right _ (by omega)
    _ = 2^(2+A*k+M+(d+1)) := by
      rw [show 2+A*k+M+(d+1)=2+(A*k+M)+(d+1) by omega]
      simp only [← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hExp

variable [Countable G] [Countable Γ] [MeasurableSpace X] [StandardBorelSpace X]
variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [StandardBorelSpace (TaggedSpace Z Γ)]

/-- Abstract replacement for the matrix denominator estimate. The small
subgroup contains the projected short kernel words, and the stabilizer
witnesses have uniformly controlled index in it. -/
theorem kernelPalettes_of_short_kernel_index (π : G →* Q)
    (hq : Function.Surjective q) (I : Subgroup Q)
    (hLift : ∀ b : I, ∃ g : G, π g = b.val ∧ q g = 1)
    (H : G → Subgroup I)
    (hfix : ∀ g : G, ∀ a ∈ H g, ∃ d : G, π d = a.val ∧
      ∀ x : Z, d • (g⁻¹ • x.val) = g⁻¹ • x.val)
    (hpal : HasRelativePalettes q.ker π.ker X)
    (hZ : MeasurableSet Z) (hX : BorelAction G X)
    (horbits : ChartModel.FiniteKernelOrbitBounds (taggedProjection Z q)
      (fun _ : TaggedSpace Z Γ => ()))
    (hIndex : HasShortKernelIndexBounds π q I H) :
    ChartModel.HasKernelPalettes (taggedProjection Z q) (TaggedSpace Z Γ) := by
  classical
  apply kernelPalettes_of_exceptionalLabels π.ker hpal hZ hX horbits
  intro S hS hOff B hB
  obtain ⟨F,T,hFT,_,hProjInv,hTracks,hSupp,hPure⟩ := exists_finite_tagSupport_alphabet S B hB
  obtain ⟨E,hFE,hE,hTE⟩ := exists_symmetric_lift_alphabet q hq F T
  obtain ⟨s,hs,hShort⟩ := exists_short_lift_section q hq E T hTE
  obtain ⟨P,C,hP,hC⟩ := hIndex E
  let A : ℕ := (T.card+1)^5 * (S.card+1)
  obtain ⟨b,hb⟩ := palette_count_growth A C S.card
  refine ⟨s,fun R => A^(R+1)*2^(2^(2*C*(R+1))),b,hb,fun R => ?_⟩
  let r := R+1
  let D := conjugateGroup S B r
  let U := wordBall T (1+2*r+2)
  let K := Subgroup.closure {g : G | g ∈ wordBall E (3*(1+2*r)) ∧ q g = 1}
  let J := ((P r).map I.subtype).comap π
  have hJ (g : G) (hg : g ∈ wordBall E (8*(r+1))) (hqg : q g = 1) : g ∈ J := by
    obtain ⟨a,ha⟩ := hP r g hg hqg
    exact ⟨a.val,a.property,ha⟩
  have hKJ : K ≤ J := (Subgroup.closure_le _).mpr (by
    intro g hg
    exact hJ _ (wordBall_mono E (by omega) hg.1) hg.2)
  have hKConj (v : Γ) (hsv : (s v)⁻¹ ∈ wordBall E 1) (g : G) (hg : g ∈ K) :
      (s v)⁻¹*g*s v ∈ J := by
    let σ := (MulAut.conj (s v)⁻¹).toMonoidHom
    have hσ : K ≤ J.comap σ := (Subgroup.closure_le _).mpr (by
      rintro w ⟨hw,hkw⟩
      change σ w ∈ J
      apply hJ
      · have hsv' := wordBall_inv_mem E hE hsv
        have hr := wordBall_mul_mem E (wordBall_mul_mem E hsv hw) hsv'
        apply wordBall_mono E (show 1+3*(1+2*r)+1 ≤ 8*(r+1) by omega)
        simpa [σ,MulAut.conj_apply] using hr
      · simp [σ,map_mul,map_inv,hkw])
    simpa [σ,MulAut.conj_apply] using (show σ g ∈ J from hσ hg)
  have hLab : ∀ a, a ∈ S ∨ a ∈ B → ∀ x : TaggedSpace Z Γ, ∃ g ∈ E,
      (a • x).1.val = g • x.1.val ∧
      tag (a • x) = q g * tag x * (taggedProjection Z q a)⁻¹ := by
    intro a ha x
    obtain ⟨g,hg,he,ht⟩ := hFT a ha x
    exact ⟨g,hFE hg,he,ht⟩
  have hProj : ∀ a ∈ S, taggedProjection Z q a ∈ T := by
    intro a ha
    simpa using hProjInv a⁻¹ (hS ha)
  have hTD := conjugateGroup_normalizedTransport_of_short_kernel_words E hE T s hs hShort
    S B hS hB hTracks hSupp hLab r K (fun g hg hqg => Subgroup.subset_closure ⟨hg,hqg⟩)
  have hSD := conjugateGroup_supported hTracks 1 r hSupp
  have hDproj : D ≤ (taggedProjection Z q).ker :=
    conjugateGroup_le S B r (taggedProjection Z q).ker hB
  letI : Finite D := finite_kernel_subgroup_of_orbitBounds horbits D
    (conjugateGroup_fg S B r) hDproj
  obtain ⟨W,hW⟩ := exists_exceptional_residual_decomposition K E hE T s hs hShort
    S r hProj (fun a ha => hLab a (Or.inl ha)) D hTD hSD
      (fun l hl a ha d hd => double_move_support hS hTracks 1 r hSupp hPure ha hl hd)
  have hIdx (t : Γ) (ht : t ∈ U) := hC r (s t) (hShort _ _ ht)
  obtain ⟨c,l,hcard,hoff,hl,hbranches⟩ := exceptionalLabels_of_residual_cosets
    (Z := Z) (q := q) π s s hs I (P r) (H ∘ s) U W S D (2^(2^(C*(r+1)))) hOff
    (fun t ht => (hIdx t ht).1) (fun t ht => (hIdx t ht).2)
    (fun b => hLift b.val) (fun t _ => hfix (s t))
    (fun l hl c hc d hd x hne => by
      obtain ⟨ht,hu,g,hg,hphys,hker,dL,dM,dD,hL,hD,hm,hv,hmKer,hEq⟩ :=
        hW l hl c hc d hd x hne
      refine ⟨ht,hu,g,hg,hphys,?_⟩
      let v := taggedProjection Z q c
      let δ := (s v)⁻¹*normalizedDisplacement s (tag x) (tag ((l*c*d) • x)) g
      have hM : (s v)⁻¹*dM ∈ J := by
        apply hJ _ _ hmKer
        exact wordBall_mono E (by omega) (wordBall_mul_mem E hv hm)
      have hδ : δ ∈ J := by
        rw [show δ = (s v)⁻¹*dL*dM*dD from hEq,
          show (s v)⁻¹*dL*dM*dD = (((s v)⁻¹*dL*s v) * ((s v)⁻¹*dM)) * dD by group]
        exact J.mul_mem (J.mul_mem (hKConj v hv dL hL) hM) (hKJ hD)
      obtain ⟨a,ha,he⟩ := hδ
      exact ⟨⟨a,ha⟩,by simpa [δ,normalizedDisplacement,mul_assoc] using he.symm⟩)
  have hTags : U.card ≤ ((T.card+1)^5)^r := by
    rw [← pow_mul]
    exact (card_wordBall_le T _).trans (Nat.pow_le_pow_right (by omega) (by dsimp [r]; omega))
  have hS' : S.card ≤ (S.card+1)^r := by
    have he := Nat.pow_le_pow_right (by omega : 1 ≤ S.card+1) (show 1 ≤ r by dsimp [r]; omega)
    exact (Nat.le_succ _).trans (by simpa using he)
  have hCap : 2^(2^(C*(r+1))) ≤ 2^(2^(2*C*r)) := by
    apply Nat.pow_le_pow_right (by decide)
    apply Nat.pow_le_pow_right (by decide)
    rw [mul_comm 2 C,mul_assoc]
    exact Nat.mul_le_mul_left C (by dsimp [r]; omega)
  have hBound : U.card * 2^(2^(C*(r+1))) * S.card ≤ A^r * 2^(2^(2*C*r)) := by
    calc
      _ ≤ ((T.card+1)^5)^r * 2^(2^(2*C*r)) * (S.card+1)^r :=
        Nat.mul_le_mul (Nat.mul_le_mul hTags hCap) hS'
      _ = A^r * 2^(2^(2*C*r)) := by rw [show A = _ from rfl,mul_pow]; ac_rfl
  exact ⟨c,l,hcard.trans hBound,hoff,hl,hbranches⟩

end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.TaggedShortKernelPalettes

-- BEGIN COMPLETE MODULE HirschProof.ChartTransfer
section
                                 

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite
open ChartModel

variable {H Γ X T : Type*} [Group H] [Group Γ] [Countable H] [Countable Γ]
  [MulAction H X] [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace T]

set_option maxHeartbeats 1500000 in
/-- Finite clopen observations of a compact free quotient action give Borel
colorings on the original action, with component bounds uniform on parameter fibers. -/
theorem chart_transfer (π : H →* Γ) (hπ : Function.Surjective π)
    (hact : BorelAction H X) (_hstab : ∀ g : H, ∀ x : X, g • x = x → π g = 1)
    (p : X → T) (_hp : Measurable p) (hinv : ∀ g : H, ∀ x, p (g • x) = p x)
    (hfin : FiniteKernelOrbitBounds π p) (hpal : HasKernelPalettes π X)
    (d : ℕ) (hDAD : CompactClopenDADLE Γ d)
    (P : Finset H) (hP₁ : (1 : H) ∈ P) :
    ∃ χ : X → Fin (d+1), Measurable χ ∧
      ∀ t : T, ∃ N : ℕ, ∀ i x, p x = t → ∃ F : Finset X, F.card ≤ N ∧
        ∀ y, TestComponent P (χ ⁻¹' {i}) x y → y ∈ F := by
  classical
  choose s hs using hπ
  have sep (j : Layer Γ) (c : H) (hc : c ∈ j.val.image s) : π c ≠ 1 := by
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hc
    rw [hs]
    exact fun h => j.prop (h ▸ hg)
  choose cap hcap using fun j : Layer Γ => hpal (j.val.image s) (sep j)
  have hpal' (j : Layer Γ) (B : Subgroup H) (hB : B.FG) (hBk : B ≤ π.ker) :
      ∃ q : X → Fin (cap j), Measurable q ∧
        ∀ c ∈ j.val, ∀ b ∈ B, ∀ x, q x ≠ q ((s c*b) • x) := by
    obtain ⟨q,hq,hqsep⟩ := hcap j B hB hBk
    exact ⟨q,hq,fun c hc => hqsep (s c) (Finset.mem_image_of_mem s hc)⟩
  let F := P.image π
  let K := (F ×ˢ F).image fun ab : Γ × Γ => ab.1*ab.2⁻¹
  have hF₁ : (1 : Γ) ∈ F := by
    have h := Finset.mem_image_of_mem π hP₁
    simpa only [map_one] using h
  have hKf (g : H) (hg : g ∈ P) : π g ∈ K :=
    Finset.mem_image.mpr ⟨(π g,1),Finset.mem_product.mpr ⟨Finset.mem_image_of_mem π hg,hF₁⟩,by simp⟩
  have hK₁ : (1 : Γ) ∈ K := by simpa only [map_one] using hKf 1 hP₁
  have hKsym : SymmetricMoves K := by
    intro q hq
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    exact Finset.mem_image.mpr ⟨(b,a),Finset.mem_product.mpr ⟨hb,ha⟩,by simp⟩
  obtain ⟨R⟩ := exists_rules cap K hKsym hK₁ d hDAD
  obtain ⟨C⟩ := exists_observed_chart π s hs P hP₁ R.W hact p hfin cap hpal'
  let χ (x : X) := R.color (C.z x)
  have hMeas : Measurable χ := observed_color_measurable C R.color (fun z w h => (R.read z w h).1)
  let m (x : X) := R.normalizer (C.z x)
  have hmem (x : X) : m x ∈ R.V := R.normalizer_mem _
  let norm (x : X) := s (m x) • x
  let E₀ := ((R.V ×ˢ P) ×ˢ R.V).image
    fun a : (Γ × H) × Γ => s a.1.1 * a.1.2 * (s a.2)⁻¹
  let E₁ := E₀.filter (fun g => π g = 1)
  let E := Subgroup.closure (E₁ : Set H)
  have hE : E.FG := ⟨E₁,rfl⟩
  have hEker : E ≤ π.ker := (Subgroup.closure_le _).mpr fun _ hg => (Finset.mem_filter.mp hg).2
  have hstep (i : Fin (d+1)) {x y : X} (hxy : TestEdge P (χ ⁻¹' {i}) x y) :
      orbitRel E (norm x) (norm y) := by
    obtain ⟨hx,hy,g,hg,rfl⟩ := hxy
    have heq : χ x = χ (g • x) := hx.trans hy.symm
    have hshift := R.read (C.z (g • x)) (π g • C.z x)
      (fun a ha => C.shift_agree a ha g hg x)
    have hnorm := R.equivariant (C.z x) (π g) (hKf g hg) (heq.trans hshift.1)
    have he : m (g • x) * π g = m x := by
      change R.normalizer (C.z (g • x)) * π g = R.normalizer (C.z x)
      rw [hshift.2]
      exact hnorm
    let a := s (m (g • x)) * g * (s (m x))⁻¹
    have ha : a ∈ E₁ := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨((m (g • x),g), m x), Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hmem _,hg⟩,hmem _⟩,rfl⟩, ?_⟩
      change π (s (m (g • x)) * g * (s (m x))⁻¹) = 1
      simp only [map_mul,map_inv,hs,he,mul_inv_cancel]
    refine ⟨⟨a,Subgroup.subset_closure ha⟩,?_⟩
    change (s (m (g • x))*g*(s (m x))⁻¹) • (s (m x) • x) = s (m (g • x)) • (g • x)
    simp only [mul_smul,inv_smul_smul]
  have hreach (i : Fin (d+1)) {x y : X}
      (p : Relation.ReflTransGen (TestEdge P (χ ⁻¹' {i})) x y) : orbitRel E (norm x) (norm y) := by
    induction p with
    | refl => exact ⟨1,one_smul _ _⟩
    | tail _ e ih =>
      obtain ⟨a,ha⟩ := ih
      obtain ⟨b,hb⟩ := hstep i e
      exact ⟨b*a,by rw [mul_smul,ha,hb]⟩
  refine ⟨χ,hMeas,fun t => ?_⟩
  obtain ⟨N,hN⟩ := hfin E hE hEker t
  refine ⟨R.V.card*N, fun i x hx => ?_⟩
  have hnx : p (norm x) = t := (hinv _ x).trans hx
  obtain ⟨L,hL,hnorm⟩ := hN (norm x) hnx
  let W := (R.V ×ˢ L).image fun a : Γ × X => (s a.1)⁻¹ • a.2
  have hWL : W.card ≤ R.V.card*N := by
    calc W.card ≤ (R.V ×ˢ L).card := Finset.card_image_le
      _ = R.V.card*L.card := Finset.card_product _ _
      _ ≤ R.V.card*N := Nat.mul_le_mul_left _ hL
  refine ⟨W,hWL,fun y hy => ?_⟩
  obtain ⟨e,he⟩ := hreach i hy.2
  have hNy : norm y ∈ L := by
    rw [← he]
    exact hnorm e.val e.prop
  refine Finset.mem_image.mpr ⟨(m y,norm y),Finset.mem_product.mpr ⟨hmem _,hNy⟩,?_⟩
  exact inv_smul_smul _ _

/-- With one parameter value, chart transfer supplies a Borel dimension bound. -/
theorem asdim_of_chart_transfer_constant (π : H →* Γ) (hπ : Function.Surjective π)
    (hact : BorelAction H X) (hstab : ∀ g : H, ∀ x : X, g • x = x → π g = 1)
    (hfin : FiniteKernelOrbitBounds π (fun _ : X => ()))
    (hpal : HasKernelPalettes π X) (d : ℕ) (hDAD : CompactClopenDADLE Γ d)
    (A : Finset H) (hA : SymmetricMoves A) :
    BorelAsdimLE (wordNear A hA hact) d univ := by
  classical
  intro r
  let P := wordBall A r
  let D : BorelNear X := wordNear A hA hact
  obtain ⟨q,hq,hN⟩ := chart_transfer π hπ hact hstab (fun _ : X => ())
    measurable_const (fun _ _ => rfl) hfin hpal d hDAD P (one_mem_wordBall A r)
  obtain ⟨N,hN⟩ := hN ()
  let U (i : Fin (d+1)) := q ⁻¹' {i}
  have hsmall (i : Fin (d+1)) (x : X) : ∃ F : Finset X, F.card ≤ N ∧
      ∀ y, D.comp r (U i) x y → y ∈ F := by
    obtain ⟨F,hF,hU⟩ := hN i x rfl
    refine ⟨F,hF,fun y hy => hU y ⟨hy.1,?_⟩⟩
    apply Relation.ReflTransGen.mono _ hy.2
    intro a b ⟨ha,hb,hNear⟩
    obtain ⟨n,hn,hw⟩ := hNear
    obtain ⟨g,hg,he⟩ := hw.exists_wordBall A (fun he => ⟨by have := he.1; omega,he.2⟩)
    exact ⟨ha,hb,g,wordBall_mono A hn hg,he⟩
  exact ⟨U,r*N,fun _ => subset_univ _,fun i => hq (measurableSet_singleton i),
    fun x _ => ⟨q x,rfl⟩,fun i => D.boundComp_of_small (hsmall i)⟩

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.ChartTransfer

-- BEGIN COMPLETE MODULE HirschProof.TaggedPhysicalTransfer
section
                                
                                  
                                     
                                        

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite

variable {G Γ X : Type*} [Group G] [Group Γ] [Countable G] [Countable Γ]
  [MulAction G X] [MeasurableSpace X] [StandardBorelSpace X]

/-- Chart transfer for the orbit metric given by an arbitrary proper group length. -/
theorem asdim_of_proper_chart_transfer (π : G →* Γ) (hπ : Function.Surjective π)
    (hact : BorelAction G X) (hstab : ∀ g : G, ∀ x : X, g • x = x → π g = 1)
    (hfin : ChartModel.FiniteKernelOrbitBounds π (fun _ : X => ()))
    (hpal : ChartModel.HasKernelPalettes π X) (d : ℕ) (hDAD : CompactClopenDADLE Γ d)
    (B : ProperGroupBalls G) : BorelAsdimLE (B.toBorelNear hact) d univ := by
  classical
  intro r
  let D := B.toBorelNear hact
  obtain ⟨c,hc,hN⟩ := chart_transfer π hπ hact hstab (fun _ : X => ()) measurable_const
    (fun _ _ => rfl) hfin hpal d hDAD (B.ball r) (B.one_mem r)
  obtain ⟨N,hN⟩ := hN ()
  let U (i : Fin (d+1)) := c ⁻¹' {i}
  have hsmall (i : Fin (d+1)) (x : X) : ∃ F : Finset X, F.card ≤ N ∧
      ∀ y, D.comp r (U i) x y → y ∈ F := by
    obtain ⟨F,hF,hTest⟩ := hN i x rfl
    refine ⟨F,hF,fun y hy => hTest y ⟨hy.1,?_⟩⟩
    exact Relation.ReflTransGen.mono (fun _ _ ⟨ha,hb,hNear⟩ => ⟨ha,hb,hNear⟩) hy.2
  exact ⟨U,r*N,fun _ => subset_univ _,fun i => hc (measurableSet_singleton i),
    fun x _ => ⟨c x,rfl⟩,fun i => D.boundComp_of_small (hsmall i)⟩

namespace TaggedSpace

variable [MeasurableSpace Γ] [StandardBorelSpace Γ]

/-- A bounded chart decomposition of the tagged action transfers to the
restricted physical orbit metric on the chosen section. -/
theorem physical_asdim_of_tagged (Z : Set X) (hZ : MeasurableSet Z) (q : G →* Γ)
    (hact : BorelAction G X) (BG : ProperGroupBalls G) (d : ℕ) (hDAD : CompactClopenDADLE Γ d)
    (hstab : ∀ (g : G) (x : Z), g • x.val = x.val → q g = 1)
    (hfin : ChartModel.FiniteKernelOrbitBounds (taggedProjection Z q) (fun _ : TaggedSpace Z Γ => ()))
    (hpal : ChartModel.HasKernelPalettes (taggedProjection Z q) (TaggedSpace Z Γ)) :
    BorelAsdimLE (BG.toBorelNear hact) d Z := by
  classical
  by_cases hNon : Z.Nonempty
  · letI : StandardBorelSpace Z := hZ.standardBorel
    letI : Countable (taggedExtension Z q) := countable_taggedExtension Z q
    let B := ProperGroupBalls.ofCountable (taggedExtension Z q)
    let hY := borel_taggedAction Z q hZ hact
    have hYstab (g : taggedExtension Z q) (y : TaggedSpace Z Γ) (hg : g • y = y) :
        taggedProjection Z q g = 1 := tagged_stabilizer_in_kernel Z q g (fun z a => hstab a z) hg
    let z : Z := ⟨hNon.some,hNon.some_mem⟩
    obtain ⟨f,hf,hfe⟩ := (MeasurableEmbedding.subtype_coe hZ).exists_measurable_extend
      (measurable_entry (Γ := Γ) Z) (fun _ => ⟨entry Z z⟩)
    have hfe' (x : Z) : f x.val = entry Z x := congrFun hfe x
    have hInj : Set.InjOn f Z := by
      intro x hx y hy hxy
      rw [hfe' ⟨x,hx⟩,hfe' ⟨y,hy⟩] at hxy
      exact congrArg Subtype.val (entry_injective (Γ := Γ) Z hxy)
    refine asdim_pullback_finite_fibers (BG.toBorelNear hact) (B.toBorelNear hY)
      f hf hZ (mapsTo_univ _ _) ?_ ?_ (asdim_of_proper_chart_transfer (taggedProjection Z q)
        (taggedProjection_surjective Z q) hY hYstab hfin hpal d hDAD B)
    · intro r
      obtain ⟨s,hs⟩ := B.finite_subset ((BG.ball r).image (physicalMove Z q))
      refine ⟨s,?_⟩
      rintro x y hx hy ⟨g,hg,hxy⟩
      exact ⟨physicalMove Z q g,hs _ (Finset.mem_image_of_mem _ hg),by
        rw [hfe' ⟨x,hx⟩,hfe' ⟨y,hy⟩]
        exact physicalMove_entry Z q hxy⟩
    · refine ⟨1,fun y => ?_⟩
      by_cases hy : ∃ x ∈ Z, f x = y
      · obtain ⟨x,hx,hxy⟩ := hy
        exact ⟨{x},by simp,fun z hz hzy => Finset.mem_singleton.mpr (hInj hz hx (hzy.trans hxy.symm))⟩
      · exact ⟨∅,by simp,fun x hx hxy => False.elim (hy ⟨x,hx,hxy⟩)⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hNon]
    exact asdim_empty (BG.toBorelNear hact) d

end TaggedSpace
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.TaggedPhysicalTransfer

-- BEGIN COMPLETE MODULE HirschProof.TaggedAbstractCore
section
                                     
                                            
                                         

set_option autoImplicit false

namespace LocalHirschHyperfinite.TaggedSpace

variable {G X Q : Type*} [Group G] [Group Q] [MulAction G X]
variable [Countable G] [MeasurableSpace X] [StandardBorelSpace X] {Z : Set X}

/-- The fixed-core theorem with a group-theoretic short-word relative index
bound in place of triangular coordinates. The proof uses the quotient by
the normal nilpotent isolator. -/
theorem physical_asdim_of_fixed_witness_short_index_quotient (π : G →* Q)
    (hπ : Function.Surjective π)
    (I : Subgroup Q) [I.Normal] [Group.IsNilpotent I]
    (H : Subgroup I) (hH : H.FG) (hroot : nilpotentIsolator H = ⊤)
    (hfix : ∀ a ∈ H, ∃ d : G, π d = a.val ∧ ∀ x : Z, d • x.val = x.val)
    (hL : IsLocallyFiniteGroup π.ker) [IsSolvable π.ker]
    (hZ : MeasurableSet Z) (hX : BorelAction G X)
    (hstab : ∀ g : G, ∀ x : X, g • x = x → π g ∈ I)
    (hIndex : HasShortKernelIndexBounds π ((QuotientGroup.mk' I).comp π) I
      (conjugateStabilizerSubgroup π I H))
    (B : ProperGroupBalls G) (d : ℕ) (hDAD : CompactClopenDADLE (Q ⧸ I) d) :
    BorelAsdimLE (B.toBorelNear hX) d Z := by
  let q := (QuotientGroup.mk' I).comp π
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective I).comp hπ
  letI : Countable (Q ⧸ I) := hq.countable
  letI : MeasurableSpace (Q ⧸ I) := ⊤
  letI : StandardBorelSpace (TaggedSpace Z (Q ⧸ I)) := standardBorel_tagged hZ
  have hI (g : G) : q g = 1 ↔ π g ∈ I := QuotientGroup.eq_one_iff _
  obtain ⟨s,hs⟩ := hq.hasRightInverse
  have hOrbit := finiteKernelOrbitBounds_constant_of_fixed_witness (Z := Z)
    π s hs I H hH hroot hfix (fun g hg => (hI g).mp hg) hL
  have hLK : π.ker ≤ q.ker := by
    intro g hg
    change π g = 1 at hg
    exact (hI g).mpr (hg.symm ▸ I.one_mem)
  have hpal : HasRelativePalettes q.ker π.ker X :=
    relative_palettes_of_locally_finite_solvable q.ker π.ker hLK hL hX
      (fun g x hx => (hI g).mpr (hstab g x hx))
  have hLift (b : I) : ∃ g : G, π g = b.val ∧ q g = 1 := by
    obtain ⟨g,hg⟩ := hπ b.val
    exact ⟨g,hg,(hI g).mpr (hg ▸ b.property)⟩
  have hPal := kernelPalettes_of_short_kernel_index π hq I hLift
    (conjugateStabilizerSubgroup π I H) (conjugateStabilizerSubgroup_fixed_lifts π I H hfix)
    hpal hZ hX hOrbit hIndex
  exact physical_asdim_of_tagged Z hZ q hX B d hDAD
    (fun g x hx => (hI g).mpr (hstab g x.val hx)) hOrbit hPal

end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.TaggedAbstractCore

-- BEGIN COMPLETE MODULE HirschProof.LatticeWordCollection
section
                                  
                                   
                                       
                                   

set_option autoImplicit false

namespace LocalHirschHyperfinite

open Set

variable {G : Type*} [Group G]

private theorem product_perm_mod_conjugates (E U : Finset G)
    (hU : ∀ a ∈ E, ∀ b ∈ E, a*b*(b*a)⁻¹ ∈ U)
    {w w' : List G} (h : w.Perm w') (hE : ∀ a ∈ w, a ∈ E) (R : ℕ)
    (p : G) (n : ℕ) (hp : p ∈ wordBall E n) (hn : n+w.length ≤ R) :
    (p*w.prod)*(p*w'.prod)⁻¹ ∈ conjugateGroup E U R := by
  induction h generalizing p n with
  | nil => simp
  | @cons a w w' h ih =>
    have ha := hE a (by simp)
    have hi := ih (fun b hb => hE b (by simp [hb])) (p*a) (n+1)
      (wordBall_append_mem E hp ha) (by simp at hn; omega)
    simpa only [List.prod_cons,mul_assoc] using hi
  | swap a b t =>
    have ha : a ∈ E := hE a (by simp)
    have hb : b ∈ E := hE b (by simp)
    have hc := conj_mem_conjugateGroup E U R (wordBall_mono E (by omega) hp)
      (Subgroup.subset_closure (hU b hb a ha))
    convert hc using 1
    simp only [List.prod_cons]
    group
  | @trans a b c hab hbc ihab ihbc =>
    have h₁ := ihab hE p n hp hn
    have h₂ := ihbc (fun g hg => hE g (hab.mem_iff.mpr hg)) p n hp (by simpa only [← hab.length_eq] using hn)
    convert (conjugateGroup E U R).mul_mem h₁ h₂ using 1
    group

private theorem perm_fiber_groups {α β : Type*} [DecidableEq β]
    (f : α → β) (keys : List β) (hk : keys.Nodup) (w : List α)
    (hw : ∀ a ∈ w, f a ∈ keys) :
    (keys.flatMap (fun b => w.filter (fun a => decide (f a = b)))).Perm w := by
  induction keys generalizing w with
  | nil =>
    cases w with
    | nil => simp
    | cons a t => exact False.elim (List.not_mem_nil (hw a (by simp)))
  | cons b keys ih =>
    let p (a : α) := decide (f a = b)
    let r := w.filter (fun a => !p a)
    have hn := List.nodup_cons.mp hk
    have hr : ∀ a ∈ r, f a ∈ keys := by
      intro a ha
      obtain ⟨h₁,h₂⟩ := List.mem_filter.mp ha
      rcases List.mem_cons.mp (hw a h₁) with he | he
      · simp [p,he] at h₂
      · exact he
    have h := ih hn.2 r hr
    have hFilter (c : β) (hc : c ∈ keys) :
        r.filter (fun a => decide (f a = c)) = w.filter (fun a => decide (f a = c)) := by
      have hcb : c ≠ b := fun he => hn.1 (he ▸ hc)
      rw [List.filter_filter]
      congr 1
      funext a
      by_cases ha : f a=c
      · have hab : f a ≠ b := fun hh => hcb (ha.symm.trans hh)
        simp [p,ha,hcb]
      · simp [ha]
    have hFlat : keys.flatMap (fun c => r.filter (fun a => decide (f a = c))) =
        keys.flatMap (fun c => w.filter (fun a => decide (f a = c))) :=
      List.flatMap_congr hFilter
    rw [hFlat] at h
    exact (h.append_left (w.filter p)).trans (List.filter_append_perm p w)

private theorem lattice_coordinate_prod {e : ℕ} (f : G →* Multiplicative (Fin e → ℤ))
    (i : Fin e) (l : List G) :
    (f l.prod).toAdd i = (l.map fun g => (f g).toAdd i).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons,map_mul,List.map_cons,List.sum_cons]
    change (f x).toAdd i+(f l.prod).toAdd i = _
    rw [ih]

private theorem lift_power_coordinate {e : ℕ} (f : G →* Multiplicative (Fin e → ℤ))
    (t : Fin e → G) (ht : ∀ j, f (t j) = Multiplicative.ofAdd (Pi.single j (1 : ℤ)))
    (i j : Fin e) (a : ℤ) : (f (t j ^ a)).toAdd i = if j=i then a else 0 := by
  rw [map_zpow,ht]
  change (a • (Pi.single j (1 : ℤ) : Fin e → ℤ)) i = _
  by_cases h : j=i
  · subst j
    simp [Pi.smul_apply]
  · simp [Pi.smul_apply,Pi.single_eq_of_ne (Ne.symm h),h]

private theorem sum_map_filter_eq {A : Type*} (p : A → Bool) (v : A → ℤ) (w : List A)
    (h : ∀ a ∈ w, p a = false → v a = 0) :
    ((w.filter p).map v).sum = (w.map v).sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have h₀ := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    cases ha : p a
    · simpa only [List.filter_cons,ha,cond_false,List.map_cons,List.sum_cons,
        h a (List.mem_cons_self ..) ha,zero_add] using h₀
    · simpa only [List.filter_cons,ha,cond_true,List.map_cons,List.sum_cons] using congrArg (v a + ·) h₀

set_option maxHeartbeats 1200000 in
/-- Words that are trivial in a free abelian quotient are products of bounded
conjugates of a fixed finite family of kernel elements. -/
theorem exists_kernel_word_collection {e : ℕ}
    (f : G →* Multiplicative (Fin e → ℤ)) (hf : Function.Surjective f) (S : Finset G) :
    ∃ (E U : Finset G), (∀ a ∈ U, a ∈ f.ker) ∧
      ∀ R (g : G), g ∈ wordBall S R → f g = 1 → g ∈ conjugateGroup E U ((e+1)*R) := by
  classical
  choose t ht using fun i : Fin e => hf (Multiplicative.ofAdd (Pi.single i (1 : ℤ)))
  let lifts (g : G) : List G := List.ofFn (fun i => t i ^ (f g).toAdd i)
  have hlift (g : G) : f (lifts g).prod = f g := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [lattice_coordinate_prod]
    dsimp only [lifts]
    rw [List.map_ofFn,List.sum_ofFn]
    change ∑ j : Fin e, (f (t j ^ (f g).toAdd j)).toAdd i = (f g).toAdd i
    simp only [lift_power_coordinate f t ht]
    rw [Finset.sum_eq_single i (fun j _ hji => if_neg hji) (by simp)]
    simp
  let correction (g : G) := g * (lifts g).prod⁻¹
  have hc (g : G) : f (correction g) = 1 := by simp [correction,hlift]
  let A := (↑S : Type _) ⊕ ((↑S : Type _) × Fin e)
  let val : A → G := Sum.elim (fun g => correction g.val)
    (fun p => t p.2 ^ (f p.1.val).toAdd p.2)
  let key : A → Option (Fin e) := Sum.elim (fun _ => none) (fun p => some p.2)
  let E : Finset G := Finset.univ.image val
  let U : Finset G := (S.image correction) ∪ (E.product E).image (fun p => p.1*p.2*(p.2*p.1)⁻¹)
  have hMem (a : A) : val a ∈ E := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hComm (a : G) (ha : a ∈ E) (b : G) (hb : b ∈ E) : a*b*(b*a)⁻¹ ∈ U :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩)
  refine ⟨E,U,?_,?_⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
      exact hc b
    · obtain ⟨⟨b,c⟩,_,rfl⟩ := Finset.mem_image.mp ha
      change f (b*c*(c*b)⁻¹) = 1
      simp only [map_mul,map_inv,mul_comm (f c) (f b),mul_inv_cancel]
  intro R g hg hfg
  obtain ⟨l,hl,he,hLen⟩ := exists_list_of_mem_wordBall hg
  let s : List (↑S : Type _) := l.attach.map fun a => ⟨a.val,hl a.val a.property⟩
  have hs : s.map Subtype.val = l := by simp [s,List.map_map,List.attach_map_val]
  let letters (a : ↑S) : List A := Sum.inl a :: List.ofFn (fun i => Sum.inr (a,i))
  let w := s.flatMap letters
  have hlParts (a : ↑S) : ((letters a).map val).prod = a.val := by
    simp only [letters,List.map_cons,List.prod_cons,List.map_ofFn]
    change correction a.val * (lifts a.val).prod = a.val
    exact inv_mul_cancel_right _ _
  have hExpand (s' : List ↑S) : ((s'.flatMap letters).map val).prod = (s'.map Subtype.val).prod := by
    induction s' with
    | nil => simp
    | cons a s' ih => simp only [List.flatMap_cons,List.map_append,List.prod_append,ih,hlParts,List.map_cons,List.prod_cons]
  have hProd : (w.map val).prod = g := (hExpand s).trans (congrArg List.prod hs |>.trans he)
  have hWlen (s' : List ↑S) : (s'.flatMap letters).length = (e+1)*s'.length := by
    induction s' with
    | nil => simp
    | cons a t ih => simp only [List.flatMap_cons,List.length_append,ih,letters,List.length_cons,
        List.length_ofFn,Nat.mul_succ]; omega
  have hSize : (w.map val).length ≤ (e+1)*R := by
    rw [List.length_map,hWlen]
    exact Nat.mul_le_mul_left _ (by simpa [s] using hLen)
  let D := conjugateGroup E U ((e+1)*R)
  let keys := (Finset.univ : Finset (Option (Fin e))).toList
  let block (b : Option (Fin e)) := w.filter (fun a => decide (key a=b))
  have hPerm : (keys.flatMap block).Perm w :=
    perm_fiber_groups key keys (Finset.nodup_toList _) w (fun _ _ => by simp [keys])
  have hDiff : (w.map val).prod * (((keys.flatMap block).map val).prod)⁻¹ ∈ D := by
    simpa only [one_mul] using product_perm_mod_conjugates E U hComm (hPerm.symm.map val)
      (fun _ ha => by obtain ⟨a,_,rfl⟩ := List.mem_map.mp ha; exact hMem a)
      ((e+1)*R) 1 0 (one_mem_wordBall E 0) (by simpa using hSize)
  have hSeed {x : G} (hx : x ∈ U) : x ∈ D := by
    simpa only [one_mul,inv_one,mul_one] using conj_mem_conjugateGroup E U ((e+1)*R)
      (one_mem_wordBall E ((e+1)*R)) (Subgroup.subset_closure hx)
  have hBlock (b : Option (Fin e)) : ((block b).map val).prod ∈ D := by
    cases b with
    | none =>
      apply D.list_prod_mem
      intro x hx
      obtain ⟨a,ha,heq⟩ := List.mem_map.mp hx
      subst x
      have hk := (List.mem_filter.mp (show a ∈ w.filter (fun a => decide (key a=none)) from ha)).2
      cases a with
      | inl g => exact hSeed (Finset.mem_union_left _ (Finset.mem_image_of_mem _ g.property))
      | inr p => simp [key] at hk
    | some i =>
      let tval (a : A) := (f (val a)).toAdd i
      have hZero (a : A) (ha : key a ≠ some i) : tval a = 0 := by
        cases a with
        | inl g => simp [tval,val,hc]
        | inr p =>
          have hne : p.2 ≠ i := fun h => ha (congrArg some h)
          change (f (t p.2 ^ (f p.1.val).toAdd p.2)).toAdd i = 0
          rw [lift_power_coordinate f t ht,if_neg hne]
      have hVal (a : A) (ha : key a = some i) : val a = t i ^ tval a := by
        cases a with
        | inl g => simp [key] at ha
        | inr p =>
          have he : p.2 = i := Option.some.inj ha
          change t p.2 ^ (f p.1.val).toAdd p.2 =
            t i ^ (f (t p.2 ^ (f p.1.val).toAdd p.2)).toAdd i
          rw [lift_power_coordinate f t ht,if_pos he,he]
      have hSum : ((block (some i)).map tval).sum = 0 := by
        have ht := sum_map_filter_eq (fun a => decide (key a = some i)) tval w
          (fun a _ ha => hZero a (by simpa using ha))
        change ((block (some i)).map tval).sum = _ at ht
        have hCoord := lattice_coordinate_prod f i (w.map val)
        rw [hProd,hfg,List.map_map] at hCoord
        exact ht.trans hCoord.symm
      have hPow (l : List A) (hl : ∀ a ∈ l, key a=some i) :
          (l.map val).prod = t i ^ (l.map tval).sum := by
        induction l with
        | nil => simp
        | cons a l ih =>
          rw [List.map_cons,List.prod_cons,List.map_cons,List.sum_cons,hVal a (hl a (by simp)),
            ih (fun b hb => hl b (by simp [hb])),zpow_add]
      rw [hPow _ (fun a ha => of_decide_eq_true (List.mem_filter.mp ha).2),hSum,zpow_zero]
      exact D.one_mem
  have hFlat (ks : List (Option (Fin e))) : ((ks.flatMap block).map val).prod ∈ D := by
    induction ks with
    | nil => simp
    | cons a ks ih =>
      simp only [List.flatMap_cons,List.map_append,List.prod_append]
      exact D.mul_mem (hBlock a) ih
  have hEnd := D.mul_mem hDiff (hFlat keys)
  simpa only [inv_mul_cancel_right,hProd] using hEnd

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.LatticeWordCollection

-- BEGIN COMPLETE MODULE HirschProof.CommensurateConjugates
section
                            
                                  
                                      
                                              

set_option autoImplicit false

open Set

namespace LocalHirschHyperfinite

variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]

/-- Bounded conjugates of a finite generating list in a normal subgroup. -/
def normalConjugates (E : Finset G) (V : Finset N) (r : ℕ) : Set N :=
  range (fun a : (↑(wordBall E r) : Type _) × (↑V : Type _) => MulAut.conjNormal a.1.val a.2.val)

noncomputable def normalConjugateSpan (E : Finset G) (V : Finset N) (r : ℕ) : Subgroup N :=
  Subgroup.closure (normalConjugates N E V r)

theorem normalConjugates_finite (E : Finset G) (V : Finset N) (r : ℕ) :
    (normalConjugates N E V r).Finite := Set.finite_range _

theorem normalConjugates_ncard_le (E : Finset G) (V : Finset N) (r : ℕ) :
    (normalConjugates N E V r).ncard ≤ V.card*(E.card+1)^r := by
  classical
  rw [normalConjugates,← Set.image_univ]
  refine le_trans Set.ncard_image_le ?_
  rw [Set.ncard_univ,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe,Fintype.card_coe]
  rw [mul_comm (wordBall E r).card]
  exact Nat.mul_le_mul_left _ (card_wordBall_le E r)

theorem map_le_normalConjugateSpan_of_le_closure (E : Finset G) (V : Finset N) (r : ℕ)
    {w : G} (hw : w ∈ wordBall E r) {K : Subgroup N} (hK : K ≤ Subgroup.closure (V : Set N)) :
    K.map (MulAut.conjNormal w).toMonoidHom ≤ normalConjugateSpan N E V r := by
  let f := (MulAut.conjNormal (H := N) w).toMonoidHom
  apply (Subgroup.map_mono hK).trans
  rw [f.map_closure]
  apply (Subgroup.closure_le _).2
  rintro _ ⟨a,ha,rfl⟩
  exact Subgroup.subset_closure ⟨(⟨w,hw⟩,⟨a,ha⟩),rfl⟩

theorem conjugateGroup_le_map_normalConjugateSpan (E U : Finset G) (V : Finset N) (r : ℕ)
    (hU : ∀ x ∈ U, ∃ y : N, y ∈ Subgroup.closure (V : Set N) ∧ y.val=x) :
    conjugateGroup E U r ≤ (normalConjugateSpan N E V r).map N.subtype := by
  apply (Subgroup.closure_le _).2
  rintro _ ⟨a,rfl⟩
  obtain ⟨y,hy,hey⟩ := hU a.2.val a.2.property
  let f := (MulAut.conjNormal (H := N) a.1.val).toMonoidHom
  have hy' : f y ∈ normalConjugateSpan N E V r :=
    (map_le_normalConjugateSpan_of_le_closure N E V r a.1.property le_rfl) ⟨y,hy,rfl⟩
  refine ⟨f y,hy',?_⟩
  change (MulAut.conjNormal a.1.val y).val = a.1.val*a.2.val*a.1.val⁻¹
  rw [MulAut.conjNormal_apply,hey]

set_option maxHeartbeats 850000 in
/-- Each alphabet letter conjugates a common positive power of every member
of a finitely generated full-isolator subgroup back into that subgroup.
Iterating gives an exponential common exponent for short words. -/
theorem exists_uniform_conjugate_powers [Group.IsNilpotent N]
    (K : Subgroup N) (hK : K.FG) (hRoot : nilpotentIsolator K = ⊤) (E : Finset G) :
    ∃ e : ℕ, 0 < e ∧ ∀ r (w : G), w ∈ wordBall E r → ∀ a ∈ K,
      (MulAut.conjNormal w a)^(e^r) ∈ K := by
  classical
  let M (s : ↑E) := ((K.map (MulAut.conjNormal (H := N) s.val).symm.toMonoidHom).subgroupOf K).normalCore
  have hM (s : ↑E) : (M s).FiniteIndex := by
    let a : MulAut N := (MulAut.conjNormal s.val).symm
    have hRoot' : nilpotentIsolator (K.map a.toMonoidHom) = ⊤ := by
      rw [← nilpotentIsolator_map_equiv,hRoot]
      exact Subgroup.map_top_of_surjective _ a.surjective
    letI := finiteIndex_of_fg_le_nilpotentIsolator (K.map a.toMonoidHom) K hK
      (hRoot'.symm ▸ le_top)
    change ((K.map a.toMonoidHom).subgroupOf K).normalCore.FiniteIndex
    infer_instance
  let e := ∏ s : ↑E, (M s).index
  have he : 0 < e := Finset.prod_pos (fun s _ => (hM s).index_ne_zero.bot_lt)
  have hOne (s : G) (hs : s ∈ E) (a : N) (ha : a ∈ K) : (MulAut.conjNormal s a)^e ∈ K := by
    let s' : ↑E := ⟨s,hs⟩
    let a' : K := ⟨a,ha⟩
    have hd : (M s').index ∣ e := Finset.dvd_prod_of_mem (fun s => (M s).index) (Finset.mem_univ s')
    obtain ⟨d,hd⟩ := hd
    have hm : a'^e ∈ M s' := by
      rw [hd,pow_mul]
      exact (M s').pow_mem ((M s').pow_index_mem a') d
    have hC : (a'^e).val ∈ K.map (MulAut.conjNormal (H := N) s).symm.toMonoidHom :=
      ((K.map _).subgroupOf K).normalCore_le hm
    obtain ⟨b,hb,hEq⟩ := hC
    have h' : (MulAut.conjNormal s).symm b = a^e := hEq
    rw [← map_pow,← h']
    simpa only [MulEquiv.apply_symm_apply] using hb
  refine ⟨e,he,fun r => ?_⟩
  induction r with
  | zero =>
    intro w hw a ha
    have hw' : w=1 := Finset.mem_singleton.mp hw
    subst w
    simpa only [pow_zero,pow_one,map_one,MulAut.one_apply] using ha
  | succ r ih =>
    intro w hw a ha
    rcases wordBall_succ_cases hw with hw | ⟨u,hu,s,hs,rfl⟩
    · rw [pow_succ,pow_mul]
      exact K.pow_mem (ih w hw a ha) e
    · have hh := ih u hu ((MulAut.conjNormal s a)^e) (hOne s hs a ha)
      have hPow : e^(r+1) = e*e^r := by rw [pow_succ,mul_comm]
      rw [map_mul,hPow,pow_mul]
      change (MulAut.conjNormal u (MulAut.conjNormal s a)^e)^(e^r) ∈ K
      rw [← map_pow]
      exact hh

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.CommensurateConjugates

-- BEGIN COMPLETE MODULE HirschProof.NilpotentPowerIndex
section
                            
                                  

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem leadingWords_ncard_le {S : Set G} (hS : S.Finite) (j : ℕ) :
    (leadingWords S j).ncard ≤ S.ncard^(j+1) := by
  induction j with
  | zero => simp [leadingWords]
  | succ j ih =>
    let I := leadingWords S j
    let J := leadingWords S (j+1)
    letI : Finite I := (finite_leadingWords hS j).to_subtype
    letI : Finite S := hS.to_subtype
    letI : Finite J := (finite_leadingWords hS (j+1)).to_subtype
    let f (p : I × S) : J := ⟨⁅p.1.val,p.2.val⁆,⟨p.1.val,p.1.property,p.2.val,p.2.property,rfl⟩⟩
    have hs : Function.Surjective f := by
      rintro ⟨g,hg⟩
      obtain ⟨a,ha,b,hb,rfl⟩ := hg
      exact ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl⟩
    calc
      J.ncard ≤ I.ncard*S.ncard := by
        simpa only [Nat.card_prod,Nat.card_coe_set_eq] using Nat.card_le_card_of_surjective f hs
      _ ≤ S.ncard^(j+1)*S.ncard := Nat.mul_le_mul_right _ ih
      _ = S.ncard^(j+1+1) := (pow_succ _ _).symm

private theorem terminalLayer_index_le {S : Set G} (hSf : S.Finite) (hSg : closure S = ⊤)
    (H : Subgroup G) {m d : ℕ} (hm : 0 < m) (hd : S.ncard ≤ d)
    (hSp : ∀ x ∈ S, x^m ∈ H) (j : ℕ) (hj : Subgroup.lowerCentralSeries G (j+1) = ⊥) :
    H.relIndex (Subgroup.lowerCentralSeries G j) ≤ m^((j+1)*d^(j+1)) := by
  let C := Subgroup.lowerCentralSeries G j
  let D := H.subgroupOf C
  let T := leadingWords S j
  have hT : T ⊆ C := leadingWords_subset_lowerCentral S j
  have hTg : closure T = C := by
    have h := leadingWords_sup_next_lowerCentral S hSg j
    rw [hj,sup_bot_eq] at h
    exact h
  letI : CommGroup C := { (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp
      (last_lowerCentral_le_center j hj b.property) a.val) }
  haveI : D.FiniteIndex := terminalLayer_finiteIndex hSf hSg H hm hSp j hj
  let q := QuotientGroup.mk' D
  let w (t : T) : C := ⟨t.val,hT t.property⟩
  let u (t : T) : C ⧸ D := q (w t)
  have hw : closure (range w) = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    have he : C.subtype '' range w = T := by
      ext x
      exact ⟨by rintro ⟨_,⟨t,rfl⟩,rfl⟩; exact t.property,
        fun hx => ⟨w ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩,rfl⟩⟩
    rw [C.subtype.map_closure,he,hTg,← MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hu : closure (range u) = ⊤ := by
    have he : range u = q '' range w := Set.range_comp q w
    rw [he,← q.map_closure,hw,Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective D)]
  have hpow (t : T) : u t ^ (m^(j+1)) = 1 := by
    change q (w t) ^ (m^(j+1)) = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (terminalLayer_power_mem H hSp j hj t.val t.property)
  letI : Fintype T := (finite_leadingWords hSf j).fintype
  have hCard : Fintype.card T ≤ d^(j+1) := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    exact (leadingWords_ncard_le hSf j).trans (Nat.pow_le_pow_left hd _)
  calc
    H.relIndex C = Nat.card (C ⧸ D) := rfl
    _ ≤ (m^(j+1))^(Fintype.card T) :=
      card_abelian_of_exponent_generators u hu _ (pow_ne_zero _ hm.ne') hpow
    _ ≤ (m^(j+1))^(d^(j+1)) :=
      Nat.pow_le_pow_right (Nat.one_le_pow _ _ hm) hCard
    _ = m^((j+1)*d^(j+1)) := (pow_mul _ _ _).symm

/-- The exponent in the nilpotent power-index estimate. The (j)-th
lower central layer contributes (j,d^j). -/
def powerGeneratorExponent (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => (j+1)*d^(j+1) + powerGeneratorExponent d j

theorem powerGeneratorExponent_eq_sum (d c : ℕ) :
    powerGeneratorExponent d c = ∑ j ∈ Finset.range c, (j+1)*d^(j+1) := by
  induction c with
  | zero => simp [powerGeneratorExponent]
  | succ c ih => rw [powerGeneratorExponent,Finset.sum_range_succ,ih,Nat.add_comm]

theorem powerGeneratorExponent_le (d c : ℕ) :
    powerGeneratorExponent d c ≤ c * (d+1)^c := by
  have geom (k : ℕ) : (∑ j ∈ Finset.range (k+1), d^j) ≤ (d+1)^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ',pow_zero]
      simp_rw [pow_succ' d]
      rw [← Finset.mul_sum]
      have h1 : 1 ≤ (d+1)^k := Nat.one_le_pow _ _ (by omega)
      calc
        d*(∑ j ∈ Finset.range (k+1),d^j)+1 ≤ d*(d+1)^k+(d+1)^k :=
          Nat.add_le_add (Nat.mul_le_mul_left _ ih) h1
        _ = (d+1)^(k+1) := by rw [pow_succ']; ring
  have hgeom : (∑ j ∈ Finset.range c, d^(j+1)) ≤ (d+1)^c := by
    have h := geom c
    rw [Finset.sum_range_succ',pow_zero] at h
    exact (Nat.le_add_right _ _).trans h
  rw [powerGeneratorExponent_eq_sum]
  calc
    (∑ j ∈ Finset.range c, (j+1)*d^(j+1)) ≤ ∑ j ∈ Finset.range c, c*d^(j+1) :=
      Finset.sum_le_sum (fun j hj => Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))
    _ ≤ c*(d+1)^c := by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ hgeom

/-- In a nilpotent group of class at most (c) generated by at most (d)
letters, if a subgroup contains the (m)-th power of each letter, its
index is at most (m^{sum_{j=1}^{c} j d^j}). -/
theorem index_le_of_common_power_generators {S : Set G} (hSf : S.Finite) (hSg : closure S = ⊤)
    (H : Subgroup G) {m d c : ℕ} (hm : 0 < m) (hd : S.ncard ≤ d)
    (hSp : ∀ x ∈ S, x^m ∈ H) (hc : Subgroup.lowerCentralSeries G c = ⊥) :
    H.index ≤ m^(powerGeneratorExponent d c) := by
  have gen (c : ℕ) : ∀ (J : Type _) [Group J], Subgroup.lowerCentralSeries J c = ⊥ →
      ∀ (T : Set J), T.Finite → closure T = ⊤ → T.ncard ≤ d →
      ∀ K : Subgroup J, (∀ x ∈ T, x^m ∈ K) → K.index ≤ m^(powerGeneratorExponent d c) := by
    induction c with
    | zero =>
      intro J _ hc T hT hTg hTd K hK
      have htop : (⊤ : Subgroup J) = ⊥ := hc
      have hK' : K = ⊤ := le_antisymm le_top (htop.symm ▸ bot_le)
      rw [hK',Subgroup.index_top,powerGeneratorExponent,pow_zero]
    | succ c ih =>
      intro J _ hc T hT hTg hTd K hK
      let C := Subgroup.lowerCentralSeries J c
      let q : J →* J ⧸ C := QuotientGroup.mk' C
      have hs : Function.Surjective q := QuotientGroup.mk'_surjective C
      have hq : Subgroup.lowerCentralSeries (J ⧸ C) c = ⊥ := by
        rw [← map_lowerCentralSeries_surjective q hs]
        exact (Subgroup.map_eq_bot_iff C).mpr (by simp [q])
      have hTq : closure (q '' T) = ⊤ := by
        rw [← q.map_closure,hTg,Subgroup.map_top_of_surjective q hs]
      have hD : (q '' T).ncard ≤ d := (ncard_image_le hT).trans hTd
      have hqi : (K.map q).index ≤ m^(powerGeneratorExponent d c) :=
        ih _ hq _ (hT.image _) hTq hD _ (by
          rintro _ ⟨x,hx,rfl⟩
          rw [← q.map_pow]
          exact ⟨x^m,hK x hx,rfl⟩)
      rw [index_eq_mul_of_central_extension K C (last_lowerCentral_le_center c hc)]
      exact (Nat.mul_le_mul (terminalLayer_index_le hT hTg K hm hTd hK c hc) hqi).trans_eq
        (pow_add _ _ _).symm
  exact gen c G hc S hSf hSg hd H hSp

/-- The relative index estimate for a subgroup generated by finitely
many letters. The nilpotency bound concerns the ambient group. -/
theorem relIndex_bounds_of_common_power_generators (H B : Subgroup G) {S : Set G}
    (hSf : S.Finite) (hSg : closure S = B) {m d c : ℕ} (hm : 0 < m) (hd : S.ncard ≤ d)
    (hSp : ∀ x ∈ S, x^m ∈ H) (hc : Subgroup.lowerCentralSeries G c = ⊥) :
    H.IsFiniteRelIndex B ∧ H.relIndex B ≤ m^(powerGeneratorExponent d c) := by
  let T : Set B := Subtype.val ⁻¹' S
  have hT : T.Finite := hSf.preimage Subtype.val_injective.injOn
  have hB : B.subtype '' T = S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hSg ▸ Subgroup.subset_closure hx⟩,hx,rfl⟩
  have hTd : T.ncard ≤ d := by
    rw [← ncard_image_of_injective T B.subtype_injective,hB]
    exact hd
  have hTg : closure T = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    rw [B.subtype.map_closure,hB,hSg,← MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hBc : Subgroup.lowerCentralSeries B c = ⊥ := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_bot]
    exact bot_unique (hc ▸ Subgroup.lowerCentralSeries_map_subtype_le B c)
  letI : Group.IsNilpotent B := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨c,hBc⟩
  have hp : ∀ x ∈ T, x^m ∈ H.subgroupOf B := fun x hx => hSp x.val hx
  exact ⟨Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr
      (finiteIndex_of_common_power_generators hT hTg (H.subgroupOf B) hm hp),
    index_le_of_common_power_generators hT hTg (H.subgroupOf B) hm hTd hp hBc⟩

theorem relIndex_le_of_common_power_generators (H B : Subgroup G) {S : Set G}
    (hSf : S.Finite) (hSg : closure S = B) {m d c : ℕ} (hm : 0 < m) (hd : S.ncard ≤ d)
    (hSp : ∀ x ∈ S, x^m ∈ H) (hc : Subgroup.lowerCentralSeries G c = ⊥) :
    H.relIndex B ≤ m^(powerGeneratorExponent d c) :=
  (relIndex_bounds_of_common_power_generators H B hSf hSg hm hd hSp hc).2

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.NilpotentPowerIndex

-- BEGIN COMPLETE MODULE HirschProof.NilpotentSubgroupFiniteness
section
                                    
                                          

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set Subgroup

variable {G Q : Type*} [Group G] [Group Q]

/-- Finitely generated kernels and images give finitely generated groups. -/
theorem groupFG_of_ker_range (f : G →* Q) [Group.FG f.ker] [Group.FG f.range] :
    Group.FG G := by
  let q := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have htop : (⊤ : Subgroup f.range) ≤ (⊤ : Subgroup G).map q := by
    rw [Subgroup.map_top_of_surjective q hq]
  obtain ⟨J,_,hJ,hJq⟩ := exists_fg_subgroup_map_eq q ⊤ ⊤ htop Group.FG.out
  have hgen : J ⊔ f.ker = ⊤ := by
    apply top_unique
    intro x _
    have hx : q x ∈ J.map q := hJq.symm ▸ Subgroup.mem_top (q x)
    obtain ⟨y,hy,he⟩ := hx
    have hfe : f y = f x := congrArg Subtype.val he
    have hz : y⁻¹*x ∈ f.ker := by
      change f (y⁻¹*x) = 1
      rw [map_mul,map_inv,hfe,inv_mul_cancel]
    have hL : J ≤ J ⊔ f.ker := le_sup_left
    have hR : f.ker ≤ J ⊔ f.ker := le_sup_right
    have hc := (J ⊔ f.ker).mul_mem (hL hy) (hR hz)
    simpa using hc
  have hf : f.ker.FG := (Group.fg_iff_subgroup_fg _).mp inferInstance
  exact ⟨hgen ▸ hJ.sup hf⟩

/-- Every subgroup of a finitely generated abelian group is finitely generated. -/
theorem fg_subgroup_of_fg_comm {A : Type*} [CommGroup A] [Group.FG A] (H : Subgroup A) :
    H.FG := by
  letI : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let S := H.toAddSubgroup.toIntSubmodule
  have hS : S.FG := IsNoetherian.noetherian S
  exact (Subgroup.fg_iff_add_fg H).mpr ((Submodule.fg_iff_addSubgroup_fg S).mp hS)

/-- Every subgroup of a finitely generated nilpotent group is finitely generated. -/
theorem fg_subgroup_of_fg_nilpotent [Group.FG G] [Group.IsNilpotent G] (H : Subgroup G) :
    H.FG := by
  have main (n : ℕ) : ∀ (J : Type _) [Group J] [Group.FG J],
      Subgroup.lowerCentralSeries J n = ⊥ → ∀ L : Subgroup J, L.FG := by
    induction n with
    | zero =>
      intro J _ _ hn L
      have htop : (⊤ : Subgroup J) = ⊥ := hn
      have hL : L = ⊥ := bot_unique (htop ▸ le_top)
      exact (Subgroup.fg_iff L).mpr ⟨∅,by rw [Subgroup.closure_empty,hL],finite_empty⟩
    | succ n ih =>
      intro J _ _ hn L
      let C := Subgroup.lowerCentralSeries J n
      let q := QuotientGroup.mk' C
      letI : Group.FG (J ⧸ C) := Group.fg_of_surjective (QuotientGroup.mk'_surjective C)
      have hq : Subgroup.lowerCentralSeries (J ⧸ C) n = ⊥ := by
        rw [← map_lowerCentralSeries_surjective q (QuotientGroup.mk'_surjective C)]
        exact (Subgroup.map_eq_bot_iff C).mpr (by simp [q])
      letI : CommGroup C := { (inferInstance : Group C) with
        mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp
          (last_lowerCentral_le_center n hn b.property) a.val) }
      obtain ⟨S,hSg⟩ := (Group.FG.out : (⊤ : Subgroup J).FG)
      let T := leadingWords (S : Set J) n
      have hT : closure T = C := by
        have he := leadingWords_sup_next_lowerCentral (S : Set J) hSg n
        rw [hn,sup_bot_eq] at he
        exact he
      letI : Group.FG C := (Group.fg_iff_subgroup_fg C).mpr
        ((Subgroup.fg_iff C).mpr ⟨T,hT,finite_leadingWords S.finite_toSet n⟩)
      let F := q.comp L.subtype
      have he : F.range = L.map q := by
        change (q.comp L.subtype).range = L.map q
        rw [MonoidHom.range_comp,Subgroup.range_subtype]
      letI : Group.FG F.range := (Group.fg_iff_subgroup_fg _).mpr (he.symm ▸ ih _ hq (L.map q))
      let D := L.subgroupOf C
      letI : Group.FG D := (Group.fg_iff_subgroup_fg D).mpr (fg_subgroup_of_fg_comm D)
      let p : D →* F.ker := {
        toFun := fun x => ⟨⟨x.val.val,x.property⟩,
          (QuotientGroup.eq_one_iff _).mpr x.val.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
      have hp : Function.Surjective p := by
        intro y
        let z : D := ⟨⟨y.val.val,(QuotientGroup.eq_one_iff _).mp y.property⟩,y.val.property⟩
        exact ⟨z,Subtype.ext (Subtype.ext rfl)⟩
      letI : Group.FG F.ker := Group.fg_of_surjective hp
      exact (Group.fg_iff_subgroup_fg L).mp (groupFG_of_ker_range F)
  obtain ⟨n,hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent G)
  exact main n G hn H

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.NilpotentSubgroupFiniteness

-- BEGIN COMPLETE MODULE HirschProof.ConjugateIsolatorIndex
section
                                      
                                              
                                         

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set Subgroup

variable {G : Type*} [Group G]

private theorem fg_inf_of_fg_nilpotent [Group.IsNilpotent G]
    (K I : Subgroup G) (hK : K.FG) : (K ⊓ I).FG := by
  letI : Group.FG K := (Group.fg_iff_subgroup_fg _).mpr hK
  let D := I.subgroupOf K
  have hD : D.FG := fg_subgroup_of_fg_nilpotent D
  have he : D.map K.subtype = K ⊓ I := by
    change (I.comap K.subtype).map K.subtype = K ⊓ I
    rw [Subgroup.map_comap_eq,Subgroup.range_subtype,inf_comm]
  exact he ▸ IsLocallyFiniteGroup.fg_map _ _ hD

/-- Quantitative index comparison on an isolator for a subgroup generated
by bounded conjugates. The fixed factor is the index inside the original
finitely generated subgroup. -/
theorem conjugate_isolator_relIndex_bounds (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (K H : Subgroup N) (hHK : H ≤ K) (V : Finset N) (hV : closure (V : Set N) = K)
    (E : Finset G) {e : ℕ} (he : 0 < e)
    (hpow : ∀ r w, w ∈ wordBall E r → ∀ a ∈ K, (MulAut.conjNormal w a)^(e^r) ∈ K)
    {c : ℕ} (hc : Subgroup.lowerCentralSeries N c = ⊥) :
    ∀ r w, w ∈ wordBall E r → w⁻¹ ∈ wordBall E r →
    let I := nilpotentIsolator H
    let a := (MulAut.conjNormal (H := N) w).toMonoidHom
    let B := normalConjugateSpan N E V r
    I.map a = I →
    H.map a ≤ B ⊓ I ∧ (H.map a).IsFiniteRelIndex (B ⊓ I) ∧
      (H.map a).relIndex (B ⊓ I) ≤ H.relIndex (K ⊓ I) *
        (e^(r+r))^(powerGeneratorExponent (V.card*(E.card+1)^r) c) := by
  classical
  intro r w hw hwi I a B hI
  let α : G →* MulAut N := MulAut.conjNormal
  let Kw := K.map a
  let Hw := H.map a
  let T := normalConjugates N E V r
  have hgen : closure T = B := rfl
  have hKwB : Kw ≤ B := map_le_normalConjugateSpan_of_le_closure N E V r hw hV.ge
  have hBH : Hw ≤ Kw ⊓ I := le_inf (Subgroup.map_mono hHK)
    (hI ▸ Subgroup.map_mono (f := a) (le_nilpotentIsolator H))
  have hT : T.Finite := normalConjugates_finite N E V r
  have hCard : T.ncard ≤ V.card*(E.card+1)^r := normalConjugates_ncard_le N E V r
  have hTp : ∀ x ∈ T, x^(e^(r+r)) ∈ Kw := by
    rintro x ⟨⟨g,v⟩,rfl⟩
    have hg : w⁻¹*g.val ∈ wordBall E (r+r) := wordBall_mul_mem E hwi g.property
    have hv : v.val ∈ K := hV ▸ Subgroup.subset_closure v.property
    have hp := hpow (r+r) _ hg v.val hv
    have hcomp : a (α (w⁻¹*g.val) v.val) = α g.val v.val := by
      change (α w * α (w⁻¹*g.val)) v.val = α g.val v.val
      rw [← map_mul,mul_inv_cancel_left]
    exact ⟨(α (w⁻¹*g.val) v.val)^(e^(r+r)),hp,by rw [map_pow,hcomp]⟩
  obtain ⟨hF,hN⟩ := relIndex_bounds_of_common_power_generators Kw B hT hgen
    (pow_pos he _) hCard hTp hc
  let F := K ⊓ I
  have hKF : K.FG := (Subgroup.fg_iff K).mpr ⟨V,hV,V.finite_toSet⟩
  have hFf : F.FG := fg_inf_of_fg_nilpotent K I hKF
  have hFin : (H.subgroupOf F).FiniteIndex :=
    finiteIndex_of_fg_le_nilpotentIsolator H F hFf inf_le_right
  have hMap : F.map a = Kw ⊓ I := by
    change (K ⊓ I).map a = K.map a ⊓ I
    have ha : Function.Injective a := (α w).injective
    rw [Subgroup.map_inf K I a ha,hI]
  have hL : Hw.relIndex (Kw ⊓ I) = H.relIndex F := by
    rw [← hMap]
    exact Subgroup.relIndex_map_map_of_injective H F (α w).injective
  have hL' : Hw.relIndex (Kw ⊓ I) ≠ 0 := hL.symm ▸ hFin.index_ne_zero
  have hF' : Kw.relIndex B ≠ 0 := Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp hF
  have hF'₂ : (Kw ⊓ I).relIndex (B ⊓ I) ≠ 0 := Subgroup.relIndex_inter_ne_zero hF' I
  have hN' : (Kw ⊓ I).relIndex (B ⊓ I) ≤ Kw.relIndex B := by
    have he : Kw ⊓ (B ⊓ I) = Kw ⊓ I := by rw [← inf_assoc,inf_eq_left.mpr hKwB]
    rw [← he,Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_le_of_le_right inf_le_left hF'
  have hB' : Kw ⊓ I ≤ B ⊓ I := inf_le_inf_right I hKwB
  refine ⟨hBH.trans hB',Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr
    (Subgroup.relIndex_ne_zero_trans hL' hF'₂),?_⟩
  rw [← Subgroup.relIndex_mul_relIndex Hw (Kw ⊓ I) (B ⊓ I) hBH hB',hL]
  exact Nat.mul_le_mul_left _ (hN'.trans hN)

private theorem le_pow_two (k : ℕ) : k ≤ 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hn : 0 < 2^k := by positivity
    omega

/-- The index expression above is bounded by a uniform double exponential
in the conjugating word radius. -/
theorem conjugate_index_growth_double_exponential (L e c v s : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ,
      L*(e^(r+r))^(powerGeneratorExponent (v*(s+1)^r) c) ≤ 2^(2^(C*(r+1))) := by
  let a := v+1
  let b := s+1
  let p := c+(a+b)*c
  let k := e+2+p
  refine ⟨k+L+1,by omega,fun r => ?_⟩
  have hd : v*b^r+1 ≤ 2^(a+b*r) := calc
    _ ≤ a*b^r := by
      change v*b^r+1 ≤ (v+1)*b^r
      rw [Nat.add_mul,one_mul]
      exact Nat.add_le_add_left (Nat.one_le_pow _ _ (by dsimp [b]; omega)) _
    _ ≤ 2^a*(2^b)^r :=
      Nat.mul_le_mul (le_pow_two a) (Nat.pow_le_pow_left (le_pow_two b) r)
    _ = _ := by rw [← pow_mul,← pow_add]
  have hab : a+b*r ≤ (a+b)*(r+1) := by
    calc
      a+b*r ≤ a*(r+1)+b*(r+1) :=
        Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
          (Nat.mul_le_mul_left _ (Nat.le_succ _))
      _ = _ := by ring
  let P := powerGeneratorExponent (v*b^r) c
  have hP : P ≤ 2^(p*(r+1)) := calc
    P ≤ c*(v*b^r+1)^c := powerGeneratorExponent_le _ _
    _ ≤ 2^c*(2^(a+b*r))^c :=
      Nat.mul_le_mul (le_pow_two c) (Nat.pow_le_pow_left hd _)
    _ = 2^(c+(a+b*r)*c) := by rw [← pow_mul,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (calc
        c+(a+b*r)*c ≤ c*(r+1)+((a+b)*(r+1))*c :=
          Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) (Nat.mul_le_mul_right _ hab)
        _ = _ := by dsimp [p]; ring)
  have hr : r+r ≤ 2^(r+1) := by
    rw [pow_succ]
    have h := le_pow_two r
    omega
  have he : e*(r+r) ≤ 2^((e+2)*(r+1)) := calc
    _ ≤ 2^e*2^(r+1) := Nat.mul_le_mul (le_pow_two e) hr
    _ = 2^(e+(r+1)) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (calc
        e+(r+1) ≤ e*(r+1)+2*(r+1) :=
          Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) (by omega)
        _ = _ := by ring)
  have hPow : (e^(r+r))^P ≤ 2^(2^(k*(r+1))) := calc
    _ ≤ ((2^e)^(r+r))^P :=
      Nat.pow_le_pow_left (Nat.pow_le_pow_left (le_pow_two e) _) _
    _ = 2^((e*(r+r))*P) := by rw [← pow_mul,← pow_mul,Nat.mul_assoc]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (calc
        (e*(r+r))*P ≤ 2^((e+2)*(r+1))*2^(p*(r+1)) := Nat.mul_le_mul he hP
        _ = _ := by rw [← pow_add]; congr 1; dsimp [k]; ring)
  calc
    L*(e^(r+r))^P ≤ 2^L*2^(2^(k*(r+1))) := Nat.mul_le_mul (le_pow_two L) hPow
    _ = 2^(L+2^(k*(r+1))) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (calc
        L+2^(k*(r+1)) ≤ (L+1)*2^(k*(r+1)) := by
          simp only [Nat.add_mul,Nat.one_mul]
          exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (by positivity)) _
        _ ≤ 2^(L+1)*2^(k*(r+1)) := Nat.mul_le_mul_right _ (le_pow_two _)
        _ = 2^(L+1+k*(r+1)) := (pow_add _ _ _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (calc
            L+1+k*(r+1) ≤ (L+1)*(r+1)+k*(r+1) :=
              Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) _
            _ = _ := by ring))

/-- A fixed coefficient gives a double exponential bound for all the
conjugates that preserve the isolator, whenever the initial subgroup has
full isolator in the normal nilpotent group. -/
theorem exists_conjugate_isolator_relIndex_double_exp (N : Subgroup G)
    [N.Normal] [Group.IsNilpotent N] (K H : Subgroup N) (hHK : H ≤ K)
    (V : Finset N) (hV : closure (V : Set N) = K) (hRoot : nilpotentIsolator K = ⊤)
    (E : Finset G) : ∃ C : ℕ, 0 < C ∧ ∀ r w,
    w ∈ wordBall E r → w⁻¹ ∈ wordBall E r →
    let I := nilpotentIsolator H
    let a := (MulAut.conjNormal (H := N) w).toMonoidHom
    let B := normalConjugateSpan N E V r
    I.map a = I →
    H.map a ≤ B ⊓ I ∧ (H.map a).IsFiniteRelIndex (B ⊓ I) ∧
      (H.map a).relIndex (B ⊓ I) ≤ 2^(2^(C*(r+1))) := by
  have hK : K.FG := (Subgroup.fg_iff K).mpr ⟨V,hV,V.finite_toSet⟩
  obtain ⟨e,he,hpow⟩ := exists_uniform_conjugate_powers N K hK hRoot E
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp (show Group.IsNilpotent N from inferInstance)
  obtain ⟨C,hC,hgrowth⟩ := conjugate_index_growth_double_exponential
    (H.relIndex (K ⊓ nilpotentIsolator H)) e c V.card E.card
  refine ⟨C,hC,?_⟩
  intro r w hw hwi I a B hI
  obtain ⟨hLe,hFin,hIdx⟩ := conjugate_isolator_relIndex_bounds N K H hHK V hV E he hpow hc
    r w hw hwi hI
  exact ⟨hLe,hFin,hIdx.trans (hgrowth r)⟩

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.ConjugateIsolatorIndex

-- BEGIN COMPLETE MODULE HirschProof.AmbientShortKernelIndex
section
                                        
                                         
                                         
                                     
                                            

set_option autoImplicit false

namespace LocalHirschHyperfinite.TaggedSpace

open Set

variable {G Q A : Type*} [Group G] [Group Q] [Group A]

private theorem map_mem_wordBall (i : G →* A) (E : Finset G) (F : Finset A)
    (hi : ∀ g ∈ E, i g ∈ F) {r : ℕ} {g : G} (hg : g ∈ wordBall E r) :
    i g ∈ wordBall F r := by
  classical
  induction r generalizing g with
  | zero =>
      have h : g = 1 := by simpa [wordBall] using hg
      simpa [h] using one_mem_wordBall F 0
  | succ r ih =>
      rcases wordBall_succ_cases hg with hg | ⟨u,hu,v,hv,rfl⟩
      · exact wordBall_mono F (Nat.le_succ _) (ih hg)
      · rw [map_mul]
        exact wordBall_append_mem F (ih hu) (hi v hv)

private theorem conjugateGroup_mono_alphabet {E F U : Finset A} (hEF : E ⊆ F) (r : ℕ) :
    conjugateGroup E U r ≤ conjugateGroup F U r := by
  apply (Subgroup.closure_le _).2
  rintro _ ⟨⟨w,u⟩,rfl⟩
  exact Subgroup.subset_closure ⟨(⟨w.val,wordBall_mono_alphabet hEF r w.property⟩,u),rfl⟩

set_option maxHeartbeats 1000000 in
/-- A normal nilpotent kernel of a free abelian ambient quotient gives the
short-word relative index bounds required on a fixed witness subgroup. The
image of the local isolator can sit inside a larger ambient isolator. -/
theorem shortKernelIndexBounds_of_ambient_lattice
    (p : G →* Q) (i : Q →* A) (hi : Function.Injective i)
    {e : ℕ} (projection : A →* Multiplicative (Fin e → ℤ))
    (hprojection : Function.Surjective projection)
    [Group.IsNilpotent projection.ker] (hN : HasFiniteIsolatorWitness projection.ker)
    (I : Subgroup Q) [I.Normal] [Group.IsNilpotent I] (hI : ∀ x ∈ I, i x ∈ projection.ker)
    (H : Subgroup I) (hH : H.FG) (hRoot : nilpotentIsolator H = ⊤) :
    HasShortKernelIndexBounds p ((QuotientGroup.mk' I).comp p) I
      (conjugateStabilizerSubgroup p I H) := by
  classical
  intro E
  let N := projection.ker
  let f := i.comp p
  let j : I →* N :=
    { toFun := fun x => ⟨i x.val,hI x.val x.property⟩
      map_one' := Subtype.ext (map_one i)
      map_mul' := fun x y => Subtype.ext (map_mul i x.val y.val) }
  have hj : Function.Injective j := by
    intro a b h
    exact Subtype.ext (hi (congrArg (fun y : N => y.val) h))
  let H' := H.map j
  let I' := j.range
  let J := nilpotentIsolator H'
  have hH'I' : H' ≤ I' := Subgroup.map_le_range _ _
  have hI'J : I' ≤ J := by
    rintro y ⟨x,rfl⟩
    have hx : x ∈ nilpotentIsolator H := hRoot.symm ▸ Subgroup.mem_top x
    obtain ⟨m,hm,hmx⟩ := (mem_nilpotentIsolator H x).mp hx
    apply (mem_nilpotentIsolator H' (j x)).mpr
    exact ⟨m,hm,⟨x^m,hmx,map_pow j x m⟩⟩
  have hIso : nilpotentIsolator I' = J := le_antisymm
    ((nilpotentIsolator_mono hI'J).trans_eq (nilpotentIsolator_idempotent H'))
    (nilpotentIsolator_mono hH'I')
  let S := E.image f
  obtain ⟨C,U,hU,hCollection⟩ := exists_kernel_word_collection projection hprojection S
  let U' := U.attach.image (fun x => (⟨x.val,hU x.val x.property⟩ : N))
  obtain ⟨K₀,_,hK₀,hK₀root⟩ := hN ⊤
  have hK₀root' : nilpotentIsolator K₀ = ⊤ := by
    rw [hK₀root]
    exact top_unique (le_nilpotentIsolator ⊤)
  let K := (K₀ ⊔ H') ⊔ Subgroup.closure (U' : Set N)
  have hH'K : H' ≤ K := le_sup_right.trans le_sup_left
  have hKFG : K.FG := (hK₀.sup (IsLocallyFiniteGroup.fg_map j H hH)).sup ⟨U',rfl⟩
  have hKroot : nilpotentIsolator K = ⊤ :=
    top_unique (hK₀root' ▸ nilpotentIsolator_mono (le_sup_left.trans le_sup_left))
  obtain ⟨V,hV⟩ := hKFG
  have hUV : ∀ u ∈ U, ∃ y : N, y ∈ Subgroup.closure (V : Set N) ∧ y.val = u := by
    intro u hu
    let y : N := ⟨u,hU u hu⟩
    have hy : y ∈ U' := Finset.mem_image.mpr ⟨⟨u,hu⟩,Finset.mem_attach _ _,rfl⟩
    have hU' : Subgroup.closure (U' : Set N) ≤ K := le_sup_right
    exact ⟨y,hV.symm ▸ hU' (Subgroup.subset_closure hy),rfl⟩
  let E₀ := S ∪ C
  let E' := E₀ ∪ E₀.image Inv.inv
  have hS : S ⊆ E' := fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hC : C ⊆ E' := fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)
  have hES : SymmetricMoves E' := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_union_left _ (by simpa using hv)
  let B := normalConjugateSpan N E' V
  obtain ⟨D,_,hIndex⟩ := exists_conjugate_isolator_relIndex_double_exp N K H' hH'K V hV hKroot E'
  let R (r : ℕ) := (e+1)*(8*(r+1))
  let P (r : ℕ) := (B (R r)).comap j
  refine ⟨P,D*((e+1)*8+1),?_,?_⟩
  · intro r g hg hq
    have hgI : p g ∈ I := (QuotientGroup.eq_one_iff _).mp hq
    let x : I := ⟨p g,hgI⟩
    have hgS : f g ∈ wordBall S (8*(r+1)) :=
      map_mem_wordBall f E S (fun _ => Finset.mem_image_of_mem _) hg
    have hgK : projection (f g) = 1 := hI (p g) hgI
    have hColl := hCollection (8*(r+1)) (f g) hgS hgK
    have hCG := conjugateGroup_mono_alphabet (U := U) hC (R r) hColl
    have hf : f g ∈ (B (R r)).map N.subtype :=
      conjugateGroup_le_map_normalConjugateSpan N E' U V (R r) hUV hCG
    obtain ⟨y,hy,he⟩ := hf
    have hyx : j x = y := Subtype.ext he.symm
    exact ⟨⟨x,show j x ∈ B (R r) from hyx.symm ▸ hy⟩,rfl⟩
  · intro r g hg
    let w := (f g)⁻¹
    let a := (MulAut.conjNormal (H := N) w).toMonoidHom
    let b := (MulAut.conjNormal (H := I) (p g)).symm
    let H₁ := conjugateStabilizerSubgroup p I H g
    have hComm : j.comp b.toMonoidHom = a.comp j := by
      ext x
      simp [j,a,b,w,f,MulAut.conjNormal_symm_apply,MulAut.conjNormal_apply,map_mul,map_inv]
    have hH₁ : H₁.map j = H'.map a := by
      change (H.map b.toMonoidHom).map j = (H.map j).map a
      rw [Subgroup.map_map,Subgroup.map_map,hComm]
    have hI' : I'.map a = I' := by
      change j.range.map a = j.range
      rw [MonoidHom.map_range,← hComm]
      ext y
      constructor
      · rintro ⟨x,rfl⟩
        exact ⟨b x,rfl⟩
      · rintro ⟨x,rfl⟩
        exact ⟨b.symm x,by simp⟩
    have hJ : J.map a = J := by
      rw [← hIso]
      change (nilpotentIsolator I').map (MulAut.conjNormal (H := N) w).toMonoidHom = _
      rw [nilpotentIsolator_map_equiv]
      exact congrArg nilpotentIsolator hI'
    have hf : f g ∈ wordBall E' (R r) := by
      have hgS : f g ∈ wordBall S (1+2*r+2) :=
        map_mem_wordBall f E S (fun _ => Finset.mem_image_of_mem _) hg
      have hRadius : 1+2*r+2 ≤ R r := (by omega : 1+2*r+2 ≤ 8*(r+1)).trans
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos e))
      exact wordBall_mono E' hRadius (wordBall_mono_alphabet hS _ hgS)
    have hw : w ∈ wordBall E' (R r) := wordBall_inv_mem E' hES hf
    have hwi : w⁻¹ ∈ wordBall E' (R r) := by simpa [w] using hf
    obtain ⟨_,hLarge,hBound⟩ := hIndex (R r) w hw hwi hJ
    have hPS : (P r).map j = B (R r) ⊓ I' := by
      simpa only [inf_comm] using Subgroup.map_comap_eq j (B (R r))
    have hRel : H₁.relIndex (P r) = (H'.map a).relIndex (B (R r) ⊓ I') := by
      rw [← Subgroup.relIndex_map_map_of_injective (f := j) H₁ (P r) hj,hH₁,hPS]
    have hSmall : (H'.map a).relIndex (B (R r) ⊓ I') ≠ 0 := by
      intro hz
      exact hLarge.relIndex_ne_zero (Subgroup.relIndex_eq_zero_of_le_right (inf_le_inf_left _ hI'J) hz)
    refine ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr (hRel.symm ▸ hSmall),?_⟩
    rw [hRel]
    calc
      _ ≤ (H'.map a).relIndex (B (R r) ⊓ J) :=
        Subgroup.relIndex_le_of_le_right (inf_le_inf_left _ hI'J) hLarge.relIndex_ne_zero
      _ ≤ 2^(2^(D*(R r+1))) := hBound
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        apply Nat.pow_le_pow_right (by decide)
        rw [mul_assoc]
        apply Nat.mul_le_mul_left
        calc
          R r+1 ≤ ((e+1)*8)*(r+1)+(r+1) := by
            dsimp [R]
            rw [mul_assoc]
            omega
          _ = ((e+1)*8+1)*(r+1) := by ring

end LocalHirschHyperfinite.TaggedSpace

end
-- END COMPLETE MODULE HirschProof.AmbientShortKernelIndex

-- BEGIN COMPLETE MODULE HirschProof.NilpotentLatticeCores
section
                                      
                                             
                                       
                                        
                                     
                                          

set_option autoImplicit false

namespace LocalHirschHyperfinite

open TaggedSpace
universe u v

/-- The short-word index estimate for actions whose projected groups embed in
one ambient group with a distinguished nilpotent kernel. -/
def AmbientHasShortKernelIndexBounds (A : Type u) [Group A] (N : Subgroup A) : Prop :=
  ∀ (J Q : Type u) [Group J] [Group Q], ∀ (p : J →* Q) (i : Q →* A), Function.Injective i →
    ∀ (I : Subgroup Q) [I.Normal] [Group.IsNilpotent I], (∀ a ∈ I, i a ∈ N) →
      ∀ (H : Subgroup I), H.FG → nilpotentIsolator H = ⊤ →
        HasShortKernelIndexBounds p ((QuotientGroup.mk' I).comp p) I (conjugateStabilizerSubgroup p I H)

variable {G Q A : Type u} {X : Type v} [Group G] [Group Q] [Group A]
  [Countable G] [Countable Q] [MulAction G X] [MeasurableSpace X] [StandardBorelSpace X]
  [IsSolvable G]

set_option maxHeartbeats 1600000 in
/-- Controlled cores after restricting to actions with stabilizers in the
nilpotent kernel. Short-word cosets are counted in the ambient group. -/
theorem coreExhaustionLE_of_nilpotent_stabilizers (p : G →* Q) (hp : Function.Surjective p)
    (i : Q →* A) (hi : Function.Injective i) (N : Subgroup Q) [N.Normal] [Group.IsNilpotent N]
    (A₀ : Subgroup A) (hN : ∀ a ∈ N, i a ∈ A₀) (hShort : AmbientHasShortKernelIndexBounds A A₀)
    (hQ : IsSolvableFiniteHirsch Q) (hL : IsLocallyFiniteGroup p.ker)
    (hStab : ∀ g : G, ∀ x : X, g • x = x → p g ∈ N)
    (B : ProperGroupBalls G) (hact : BorelAction G X) (d : ℕ) (hDAD : SubquotientDADLE A d) :
    HasCoreExhaustionLE (B.toBorelNear hact) d := by
  have hRoot : HasFiniteIsolatorWitness N := finiteIsolatorWitness_of_nilpotent_finiteHirsch (hQ.subgroup N)
  apply coreExhaustionLE_of_isolator_strata p N hRoot B hact d
  intro I
  apply coreExhaustionLE_of_normalizer_fixed_witnesses p N I hRoot hStab hact d
  let Y := isolatorFiber (X := X) p N I
  let G' := physicalNormalizer p N I
  let Q' := matrixNormalizer N I
  let J := normalizerIsolator N I
  letI : MulAction G' Y := isolatorFiberAction (X := X) p N I
  letI : StandardBorelSpace Y := (measurableSet_physicalIsolator p N hact I).standardBorel
  let p' := normalizerProjection p N I
  let j := i.comp Q'.subtype
  have hj : Function.Injective j := hi.comp Q'.subtype_injective
  have hJD : CompactClopenDADLE (Q' ⧸ J) d := hDAD Q' _ j hj
    (QuotientGroup.mk' J) (QuotientGroup.mk'_surjective J)
  have hI : ∀ a ∈ J, j a ∈ A₀ := by
    intro a ha
    obtain ⟨b,_,hb⟩ := ha
    exact hN a.val ((show b.val=a.val from hb) ▸ b.property)
  intro Z hZ H hH hIso hFix
  have hIdx := hShort G' Q' p' j hj J hI H hH hIso
  exact physical_asdim_of_fixed_witness_short_index_quotient p' (normalizerProjection_surjective p N I hp)
    J H hH hIso hFix (normalizerProjection_locallyFinite p N I hL) hZ
    (borelAction_isolatorFiber p N I hact) (normalizerProjection_stabilizers_in_isolator p N I hStab)
    hIdx _ d hJD

section Lattice

variable {e : ℕ} (π : G →* A) (hπ : Function.Surjective π)
variable (diag : A →* Multiplicative (Fin e → ℤ)) [Group.IsNilpotent diag.ker]

include hπ

private theorem coreExhaustionLE_of_lattice_complement
    (P P' : Subgroup (Multiplicative (Fin e → ℤ)))
    (hP : ∀ x : X, projectedStabilizer (diag.comp π) x = P) (hd : Disjoint P P')
    (hA : IsSolvableFiniteHirsch A) (hL : IsLocallyFiniteGroup π.ker)
    (hShort : AmbientHasShortKernelIndexBounds A diag.ker)
    (B : ProperGroupBalls (projectedComplement (diag.comp π) P'))
    (hact : BorelAction G X) (d : ℕ) (hDAD : SubquotientDADLE A d) :
    HasCoreExhaustionLE (B.toBorelNear (fun g => hact g.val)) d := by
  let G' := projectedComplement (diag.comp π) P'
  let A' := P'.comap diag
  let π' : G' →* A' := subgroupPreimageProjection π A'
  have hπ' : Function.Surjective π' := subgroupPreimageProjection_surjective π A' hπ
  letI : Countable A' := hπ'.countable
  let diag' := diag.comp A'.subtype
  letI : Group.IsNilpotent diag'.ker := nilpotent_kernel_of_embedding diag A'.subtype A'.subtype_injective
  have hStab (g : G') (x : X) (hg : g • x = x) : π' g ∈ diag'.ker := by
    have hPg : (diag.comp π) g.val ∈ P := by
      rw [← hP x]
      exact ⟨g.val,hg,rfl⟩
    have hh : (diag.comp π) g.val ∈ P ⊓ P' := ⟨hPg,g.property⟩
    change (diag.comp π) g.val = 1
    exact Subgroup.mem_bot.mp (hd.eq_bot ▸ hh)
  have hL' : IsLocallyFiniteGroup π'.ker := locallyFinite_kernel_of_restriction π π'
    G'.subtype G'.subtype_injective A'.subtype (fun _ => rfl) hL
  exact coreExhaustionLE_of_nilpotent_stabilizers π' hπ' A'.subtype A'.subtype_injective
    diag'.ker diag.ker (fun _ ha => ha) hShort (hA.subgroup A') hL' hStab B
    (fun g => hact g.val) d hDAD

/-- The fixed-stage core theorem for a solvable action with locally finite
kernel and a quotient that is nilpotent-by-free-abelian. -/
theorem coreExhaustionLE_of_nilpotent_lattice_quotient (hDiag : Function.Surjective diag)
    (hA : IsSolvableFiniteHirsch A) (hL : IsLocallyFiniteGroup π.ker)
    (B : ProperGroupBalls G) (hact : BorelAction G X) (d : ℕ) (hDAD : SubquotientDADLE A d) :
    HasCoreExhaustionLE (B.toBorelNear hact) d := by
  have hN : HasFiniteIsolatorWitness diag.ker :=
    finiteIsolatorWitness_of_nilpotent_finiteHirsch (hA.subgroup diag.ker)
  have hShort : AmbientHasShortKernelIndexBounds A diag.ker := by
    intro J Q _ _ p i hi I _ _ hI H hH hIso
    exact shortKernelIndexBounds_of_ambient_lattice p i hi diag hDiag hN I hI H hH hIso
  letI : Countable (Multiplicative (Fin e → ℤ)) := by
    change Countable (Fin e → ℤ)
    infer_instance
  apply coreExhaustionLE_of_integer_lattice_complements e (diag.comp π) (hDiag.comp hπ) B hact d
  intro P P' hd _ B'
  let Y := projectedStabilizerSlice (X := X) (diag.comp π) P
  letI : MulAction G Y := projectedSliceAction (X := X) (diag.comp π) P
  letI : StandardBorelSpace Y := (measurableSet_projectedStabilizer_eq (diag.comp π) hact P).standardBorel
  exact coreExhaustionLE_of_lattice_complement π hπ diag P P'
    (projectedStabilizer_on_slice (diag.comp π) P) hd hA hL hShort B'
    (borelAction_projectedSlice (diag.comp π) P hact) d hDAD

end Lattice
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.NilpotentLatticeCores

-- BEGIN COMPLETE MODULE HirschProof.NilpotentLatticeAssembly
section
                                
                                        

set_option autoImplicit false

namespace LocalHirschHyperfinite

universe u v

/-- A finite-index subgroup with nilpotent kernel and free abelian quotient. -/
def HasVirtuallyFreeAbelianQuotientWithNilpotentKernel (Q : Type*) [Group Q] : Prop :=
  ∃ J : Subgroup Q, J.FiniteIndex ∧ ∃ e : ℕ,
    ∃ p : J →* Multiplicative (Fin e → ℤ), Function.Surjective p ∧ Group.IsNilpotent p.ker

set_option maxHeartbeats 1200000 in
/-- The finitely generated stage reduction from the nilpotent-by-free-abelian
structure of its locally finite radical quotient. -/
theorem coreExhaustion_of_nilpotent_lattice_radical_quotient {G : Type u} {X : Type v}
    [Group G] [Countable G] [MulAction G X] [MeasurableSpace X] [StandardBorelSpace X]
    (hG : IsSolvableFiniteHirsch G)
    (hStructure : HasVirtuallyFreeAbelianQuotientWithNilpotentKernel (G ⧸ locallyFiniteRadical G))
    (hRank : ∃ r, GeneratorRankLE (G ⧸ locallyFiniteRadical G) r)
    (B : ProperGroupBalls G) (hact : BorelAction G X) : HasCoreExhaustion (B.toBorelNear hact) := by
  let L := locallyFiniteRadical G
  let Q := G ⧸ L
  let p := QuotientGroup.mk' L
  have hp : Function.Surjective p := QuotientGroup.mk'_surjective L
  have hQ := hG.of_surjective p hp
  letI : IsSolvable G := hG.1
  letI : Countable Q := hp.countable
  obtain ⟨J,hJIndex,e,diag,hDiag,hNil⟩ := hStructure
  obtain ⟨r,hR⟩ := hRank
  letI : J.FiniteIndex := hJIndex
  letI : Group.IsNilpotent diag.ker := hNil
  let G' := J.comap p
  let p' := subgroupPreimageProjection p J
  have hp' := subgroupPreimageProjection_surjective p J hp
  letI : G'.FiniteIndex := ⟨by
    change (J.comap p).index ≠ 0
    rw [Subgroup.index_comap_of_surjective _ hp]
    exact hJIndex.index_ne_zero⟩
  have hL : IsLocallyFiniteGroup p.ker := by
    rw [QuotientGroup.ker_mk']
    exact locallyFiniteRadical_locallyFinite G
  have hL' : IsLocallyFiniteGroup p'.ker := locallyFinite_kernel_of_restriction p p'
    G'.subtype G'.subtype_injective J.subtype (fun _ => rfl) hL
  have hJ := hQ.subgroup J
  obtain ⟨d,hDAD⟩ := exists_subquotientDADLE_of_solvableFiniteHirsch_generatorRank hJ (hR.subgroup J)
  let B' := ProperGroupBalls.ofCountable G'
  have hact' : BorelAction G' X := fun g => hact g.val
  have h := coreExhaustionLE_of_nilpotent_lattice_quotient p' hp' diag hDiag hJ hL' B' hact' d hDAD
  exact coreExhaustion_finiteIndex_action G' B B' hact (coreExhaustion_of_le _ d h)

/-- Assemble the countable orbit theorem from the group-only structural facts. -/
theorem hyperfinite_of_nilpotent_lattice_radical_quotients (G : Type u) (X : Type v)
    [Group G] [Countable G] [MulAction G X] [MeasurableSpace X] [StandardBorelSpace X]
    (hG : IsLocallyVirtuallySolvableFiniteHirsch G) (hact : BorelAction G X)
    (hStructure : ∀ (J : Type u) [Group J] [Group.FG J], IsSolvableFiniteHirsch J →
      HasVirtuallyFreeAbelianQuotientWithNilpotentKernel (J ⧸ locallyFiniteRadical J))
    (hRank : ∀ (J : Type u) [Group J] [Group.FG J], IsSolvableFiniteHirsch J →
      ∃ r, GeneratorRankLE (J ⧸ locallyFiniteRadical J) r) : IsHyperfinite (orbitRel G (X := X)) := by
  apply hyperfinite_of_solvable_stage_cores hG hact
  intro J _ _ _ _ B hJact hJ
  exact coreExhaustion_of_nilpotent_lattice_radical_quotient hJ (hStructure J hJ) (hRank J hJ) B hJact

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.NilpotentLatticeAssembly

-- BEGIN COMPLETE MODULE HirschProof.PolynomialTopology
section
                                                 
                                          
                                       
                                       

set_option autoImplicit false

noncomputable section

namespace LocalHirschHyperfinite
open Set Topology TopologicalSpace

variable {K : Type*} [Field K] {ι κ X Y : Type*}

/-- The prime ideal of polynomials vanishing at a point. -/
def polynomialPoint (a : ι → K) : PrimeSpectrum (MvPolynomial ι K) where
  asIdeal := RingHom.ker (MvPolynomial.eval a)
  isPrime := RingHom.ker_isPrime (MvPolynomial.eval a)

/-- The Zariski topology induced by the given system of coordinates. -/
@[implicit_reducible]
def polynomialTopology (v : X → ι → K) : TopologicalSpace X :=
  TopologicalSpace.induced (polynomialPoint ∘ v) inferInstance

/-- Scalar-valued functions given by a polynomial in the coordinates. -/
def PolynomialAlong (v : X → ι → K) (f : X → K) : Prop :=
  ∃ p : MvPolynomial ι K, ∀ x, MvPolynomial.eval (v x) p = f x

namespace PolynomialAlong

variable {v : X → ι → K} {f g : X → K}

theorem coord (i : ι) : PolynomialAlong v (fun x => v x i) := ⟨MvPolynomial.X i,by simp⟩

theorem constant (a : K) : PolynomialAlong v (fun _ => a) := ⟨MvPolynomial.C a,by simp⟩

theorem add (hf : PolynomialAlong v f) (hg : PolynomialAlong v g) :
    PolynomialAlong v (fun x => f x + g x) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun x => by rw [map_add,hp,hq]⟩

theorem neg (hf : PolynomialAlong v f) : PolynomialAlong v (fun x => -f x) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨-p,fun x => by rw [map_neg,hp]⟩

theorem sub (hf : PolynomialAlong v f) (hg : PolynomialAlong v g) :
    PolynomialAlong v (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : PolynomialAlong v f) (hg : PolynomialAlong v g) :
    PolynomialAlong v (fun x => f x * g x) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,fun x => by rw [map_mul,hp,hq]⟩

theorem sum {I : Type*} (s : Finset I) (f : I → X → K)
    (h : ∀ i ∈ s, PolynomialAlong v (f i)) :
    PolynomialAlong v (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using constant (v := v) (0 : K)
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem isClosed_zero (hf : PolynomialAlong v f) :
    @IsClosed X (polynomialTopology v) {x | f x = 0} := by
  letI := polynomialTopology v
  obtain ⟨p,hp⟩ := hf
  let s := PrimeSpectrum.zeroLocus ({p} : Set (MvPolynomial ι K))
  have he : {x | f x = 0} = (polynomialPoint ∘ v) ⁻¹' s := by
    ext x
    change f x = 0 ↔ ({p} : Set (MvPolynomial ι K)) ⊆ (polynomialPoint (v x)).asIdeal
    rw [Set.singleton_subset_iff]
    exact (congrArg (· = 0) (hp x)).symm.to_iff
  rw [he]
  exact (PrimeSpectrum.isClosed_zeroLocus _).preimage continuous_induced_dom

theorem isClosed_eq (hf : PolynomialAlong v f) (hg : PolynomialAlong v g) :
    @IsClosed X (polynomialTopology v) {x | f x = g x} := by
  simpa only [sub_eq_zero] using (hf.sub hg).isClosed_zero

end PolynomialAlong

theorem polynomialTopology_continuous {v : X → ι → K} {u : Y → κ → K} {f : X → Y}
    (h : ∀ j, PolynomialAlong v (fun x => u (f x) j)) :
    @Continuous X Y (polynomialTopology v) (polynomialTopology u) f := by
  letI := polynomialTopology v
  letI := polynomialTopology u
  choose p hp using h
  let σ := MvPolynomial.eval₂Hom MvPolynomial.C p
  have he (x : X) : polynomialPoint (u (f x)) = PrimeSpectrum.comap σ (polynomialPoint (v x)) := by
    have hEval : MvPolynomial.eval (u (f x)) = (MvPolynomial.eval (v x)).comp σ := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [σ]
      · intro j
        simp [σ,hp j x]
    apply PrimeSpectrum.ext
    change RingHom.ker (MvPolynomial.eval (u (f x))) =
      (RingHom.ker (MvPolynomial.eval (v x))).comap σ
    rw [hEval]
    rfl
  apply continuous_induced_rng.mpr
  have hfun : (polynomialPoint ∘ u) ∘ f = PrimeSpectrum.comap σ ∘ (polynomialPoint ∘ v) :=
    funext he
  rw [hfun]
  exact (PrimeSpectrum.continuous_comap σ).comp continuous_induced_dom

/-- A finite system of coordinates induces a Noetherian topology. -/
theorem polynomialTopology_noetherian [Finite ι] (v : X → ι → K) :
    @NoetherianSpace X (polynomialTopology v) := by
  letI := polynomialTopology v
  let P := MvPolynomial ι K
  haveI : NoetherianSpace (PrimeSpectrum P) :=
    ((noetherianSpace_TFAE (PrimeSpectrum P)).out 0 1).mpr (PrimeSpectrum.closedsEmbedding P).dual.wellFoundedLT
  have hi : IsInducing (polynomialPoint ∘ v) := ⟨rfl⟩
  exact hi.noetherianSpace

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.PolynomialTopology

-- BEGIN COMPLETE MODULE HirschProof.TriangularStructure
section
                                       
                                         
                                 

set_option autoImplicit false

namespace LocalHirschHyperfinite
open scoped commutatorElement

local notation "Square" => fun K n => Matrix (Fin n) (Fin n) K

/-- A homomorphism from a finitely generated group to an abelian group
has, on a finite-index subgroup, an image free abelian of finite rank. -/
theorem exists_finiteIndex_freeAbelianImage {G A : Type*} [Group G] [Group.FG G]
    [CommGroup A] (f : G →* A) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∃ d : ℕ, ∃ p : H →* (Fin d → Multiplicative ℤ),
      Function.Surjective p ∧ p.ker = f.ker.subgroupOf H := by
  classical
  letI : Group.FG f.range := Group.fg_of_surjective f.rangeRestrict_surjective
  obtain ⟨I,J,hI,hJ,a,ha,b,⟨e⟩⟩ := CommGroup.equiv_free_prod_prod_multiplicative_zmod f.range
  let B := (∀ i : I, Multiplicative (ZMod (a i ^ b i)))
  haveI (i : I) : NeZero (a i ^ b i) := ⟨pow_ne_zero _ (ha i).ne_zero⟩
  letI : Finite B := inferInstance
  let v := e.toMonoidHom.comp f.rangeRestrict
  let q := (MonoidHom.snd (J → Multiplicative ℤ) B).comp v
  let H := q.ker
  let τ := Fintype.equivFin J
  let P : (J → Multiplicative ℤ) →* (Fin (Fintype.card J) → Multiplicative ℤ) := {
    toFun := fun x i => x (τ.symm i)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let p := P.comp ((MonoidHom.fst (J → Multiplicative ℤ) B).comp (v.comp H.subtype))
  have hvs : Function.Surjective v := e.surjective.comp f.rangeRestrict_surjective
  have hpi : Function.Injective P := by
    intro x y h
    funext i
    simpa [P] using congrFun h (τ i)
  refine ⟨H,Subgroup.finiteIndex_ker q,Fintype.card J,p,?_,?_⟩
  · intro z
    obtain ⟨g,hg⟩ := hvs ((fun j => z (τ j)),1)
    have hgH : g ∈ H := by change (v g).2 = 1; rw [hg]
    refine ⟨⟨g,hgH⟩,?_⟩
    ext i
    change (v g).1 (τ.symm i) = z i
    rw [hg]
    simp
  · ext g
    change P (v g.val).1 = 1 ↔ f g.val = 1
    have hg : (v g.val).2 = 1 := g.property
    constructor
    · intro h
      have h' : (v g.val).1 = 1 := hpi (h.trans P.map_one.symm)
      have hv : v g.val = 1 := Prod.ext h' hg
      exact congrArg Subtype.val (e.injective (hv.trans e.map_one.symm))
    · intro h
      have hv : f.rangeRestrict g.val = 1 := Subtype.ext h
      change P (e (f.rangeRestrict g.val)).1 = 1
      rw [hv,map_one]
      exact P.map_one

section Diagonal

variable {G K : Type*} [Group G] [CommRing K] {n : ℕ}

theorem diagonal_mul_of_upper {A B : Square K n}
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  classical
  rw [Matrix.mul_apply,Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hj|hj
    · rw [hA i j hj,zero_mul]
    · rw [hB j i hj,mul_zero]
  · simp

/-- The diagonal of an upper triangular representation is a group
homomorphism to the tuple of scalar units. -/
def diagonalRepresentation (ρ : G →* (Square K n)ˣ)
    (hρ : ∀ g : G, ∀ i j, j < i → (ρ g : Square K n) i j = 0) :
    G →* (Fin n → Kˣ) where
  toFun g i := {
    val := (ρ g : Square K n) i i
    inv := (ρ g⁻¹ : Square K n) i i
    val_inv := by
      rw [← diagonal_mul_of_upper (hρ g) (hρ g⁻¹),← Units.val_mul,← map_mul,mul_inv_cancel,map_one]
      exact Matrix.one_apply_eq i
    inv_val := by
      rw [← diagonal_mul_of_upper (hρ g⁻¹) (hρ g),← Units.val_mul,← map_mul,inv_mul_cancel,map_one]
      exact Matrix.one_apply_eq i }
  map_one' := by
    ext i
    simp
  map_mul' g h := by
    ext i
    change (ρ (g*h) : Square K n) i i = (ρ g : Square K n) i i * (ρ h : Square K n) i i
    rw [map_mul,Units.val_mul,diagonal_mul_of_upper (hρ g) (hρ h)]

/-- After passing to finite index, the diagonal quotient of an upper
triangular finitely generated group is free abelian of finite rank. -/
theorem exists_finiteIndex_diagonal_quotient [Group.FG G] (ρ : G →* (Square K n)ˣ)
    (hρ : ∀ g : G, ∀ i j, j < i → (ρ g : Square K n) i j = 0) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∃ d : ℕ, ∃ p : H →* (Fin d → Multiplicative ℤ),
      Function.Surjective p ∧ ∀ g : H, (p g = 1 ↔ ∀ i, (ρ g.val : Square K n) i i = 1) := by
  let d := diagonalRepresentation ρ hρ
  obtain ⟨H,hH,r,p,hp,he⟩ := exists_finiteIndex_freeAbelianImage d
  refine ⟨H,hH,r,p,hp,fun g => ?_⟩
  change g ∈ p.ker ↔ _
  rw [he]
  change d g.val = 1 ↔ _
  constructor
  · intro h i
    exact congrArg (fun f : Fin n → Kˣ => (f i : K)) h
  · intro h
    exact funext (fun i => Units.ext (h i))

end Diagonal

section Unitriangular

variable {G K : Type*} [Group G] [CommRing K] {n : ℕ}

/-- The entries of a matrix below the given superdiagonal vanish. -/
def VanishesBefore (k : ℕ) (A : Square K n) : Prop :=
  ∀ i j, j.val < i.val + k → A i j = 0

theorem VanishesBefore.zero (k : ℕ) : VanishesBefore k (0 : Square K n) :=
  fun _ _ _ => rfl

theorem VanishesBefore.add {k : ℕ} {A B : Square K n}
    (ha : VanishesBefore k A) (hb : VanishesBefore k B) : VanishesBefore k (A+B) := by
  intro i j hij
  simp [ha i j hij,hb i j hij]

theorem VanishesBefore.neg {k : ℕ} {A : Square K n}
    (ha : VanishesBefore k A) : VanishesBefore k (-A) := by
  intro i j hij
  simp [ha i j hij]

theorem VanishesBefore.mul {k l : ℕ} {A B : Square K n}
    (ha : VanishesBefore k A) (hb : VanishesBefore l B) : VanishesBefore (k+l) (A*B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hm : m.val < i.val + k
  · rw [ha i m hm,zero_mul]
  · rw [hb m j (by omega),mul_zero]

variable (ρ : G →* (Square K n)ˣ)
variable (hu : ∀ g : G, ∀ i j, j < i → (ρ g : Square K n) i j = 0)
include hu

theorem vanishesBefore_repr (g : G) : VanishesBefore 0 (ρ g : Square K n) :=
  fun i j h => hu g i j (by simpa using h)

/-- The subgroup whose deviation from the identity starts at the given
superdiagonal. -/
def unitriangularFiltration (k : ℕ) : Subgroup G where
  carrier := {g | VanishesBefore k ((ρ g : Square K n)-1)}
  one_mem' := by
    change VanishesBefore k ((ρ 1 : Square K n)-1)
    simpa only [map_one,Units.val_one,sub_self] using VanishesBefore.zero (K := K) (n := n) k
  mul_mem' := by
    intro g h hg hh
    change VanishesBefore k ((ρ (g*h) : Square K n)-1)
    change VanishesBefore k ((ρ g : Square K n)-1) at hg
    change VanishesBefore k ((ρ h : Square K n)-1) at hh
    have ht := (hg.mul (vanishesBefore_repr ρ hu h))
    rw [Nat.add_zero] at ht
    rw [map_mul,Units.val_mul,show ((ρ g : Square K n)*(ρ h : Square K n)-1) =
        ((ρ g : Square K n)-1)*(ρ h : Square K n)+((ρ h : Square K n)-1) by noncomm_ring]
    exact ht.add hh
  inv_mem' := by
    intro g hg
    change VanishesBefore k ((ρ g : Square K n)-1) at hg
    change VanishesBefore k ((ρ g⁻¹ : Square K n)-1)
    have ht := ((vanishesBefore_repr ρ hu g⁻¹).mul hg).neg
    rw [Nat.zero_add] at ht
    have he : (ρ g⁻¹ : Square K n)*(ρ g : Square K n) = 1 := by
      rw [← Units.val_mul,← map_mul,inv_mul_cancel,map_one,Units.val_one]
    rwa [mul_sub,he,mul_one,neg_sub] at ht

theorem commutator_le_unitriangularFiltration (k l : ℕ) :
    ⁅unitriangularFiltration ρ hu k,unitriangularFiltration ρ hu l⁆ ≤
      unitriangularFiltration ρ hu (k+l) := by
  apply Subgroup.commutator_le.mpr
  intro g hg h hh
  change VanishesBefore k ((ρ g : Square K n)-1) at hg
  change VanishesBefore l ((ρ h : Square K n)-1) at hh
  change VanishesBefore (k+l) ((ρ ⁅g,h⁆ : Square K n)-1)
  let A : Square K n := ρ g
  let B : Square K n := ρ h
  let C : Square K n := ρ g⁻¹
  let D : Square K n := ρ h⁻¹
  have hBA : A*C=1 := by
    change (ρ g : Square K n)*(ρ g⁻¹ : Square K n) = 1
    rw [← Units.val_mul,← map_mul,mul_inv_cancel,map_one,Units.val_one]
  have hBD : B*D=1 := by
    change (ρ h : Square K n)*(ρ h⁻¹ : Square K n) = 1
    rw [← Units.val_mul,← map_mul,mul_inv_cancel,map_one,Units.val_one]
  have hdiff : VanishesBefore (k+l) (A*B-B*A) := by
    have hAB : A*B-B*A = (A-1)*(B-1)+(-((B-1)*(A-1))) := by noncomm_ring
    rw [hAB]
    exact (hg.mul hh).add (by simpa only [Nat.add_comm l k] using (hh.mul hg).neg)
  have hCD := (vanishesBefore_repr ρ hu g⁻¹).mul (vanishesBefore_repr ρ hu h⁻¹)
  have hfinal := hdiff.mul hCD
  rw [Nat.add_zero] at hfinal
  have he : (A*B-B*A)*(C*D) = A*B*C*D-1 := by
    rw [sub_mul,show B*A*(C*D) = B*(A*C)*D by noncomm_ring,hBA,mul_one,hBD,mul_assoc (A*B)]
  rw [he] at hfinal
  simpa only [commutatorElement_def,map_mul,Units.val_mul] using hfinal

/-- Any group with a faithful upper unitriangular representation is
nilpotent. The central filtration is given by vanishing superdiagonals. -/
theorem isNilpotent_of_faithful_unitriangular (hi : Function.Injective ρ)
    (hd : ∀ g i, (ρ g : Square K n) i i = 1) : Group.IsNilpotent G := by
  have hfirst : unitriangularFiltration ρ hu 1 = ⊤ := by
    apply top_unique
    intro g _ i j hij
    have hle : j ≤ i := Fin.le_iff_val_le_val.mpr (by omega)
    rcases lt_or_eq_of_le hle with hj|rfl
    · simp [hu g i j hj,ne_of_gt hj]
    · simp [hd]
  have hseries (k : ℕ) : Subgroup.lowerCentralSeries G k ≤ unitriangularFiltration ρ hu (k+1) := by
    induction k with
    | zero => simpa only [Nat.zero_add,hfirst] using le_top
    | succ k hk =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact (Subgroup.commutator_mono hk hfirst.ge).trans
        (commutator_le_unitriangularFiltration ρ hu (k+1) 1)
  have hl : unitriangularFiltration ρ hu (n+1) ≤ ⊥ := by
    intro g hg
    apply Subgroup.mem_bot.mpr
    apply hi
    apply Units.ext
    ext i j
    have hlt : j.val < i.val+(n+1) := by omega
    have hz := hg i j hlt
    exact (sub_eq_zero.mp hz).trans (by simp)
  exact Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨n,bot_unique ((hseries n).trans hl)⟩

/-- The nilpotent kernel and free abelian quotient associated to a faithful
upper triangular representation can be chosen on the same finite-index subgroup. -/
theorem exists_finiteIndex_nilpotent_freeAbelian_extension [Group.FG G]
    (hi : Function.Injective ρ) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∃ d : ℕ, ∃ p : H →* (Fin d → Multiplicative ℤ),
      Function.Surjective p ∧ Group.IsNilpotent p.ker ∧
        ∀ g : H, (p g = 1 ↔ ∀ i, (ρ g.val : Square K n) i i = 1) := by
  obtain ⟨H,hH,d,p,hp,hd⟩ := exists_finiteIndex_diagonal_quotient ρ hu
  let σ := ρ.comp (H.subtype.comp p.ker.subtype)
  have hs : Function.Injective σ := hi.comp (H.subtype_injective.comp p.ker.subtype_injective)
  have hσ : ∀ g : p.ker, ∀ i j, j < i → (σ g : Square K n) i j = 0 :=
    fun g => hu g.val.val
  have hsd : ∀ g i, (σ g : Square K n) i i = 1 := fun g => (hd g.val).mp g.property
  exact ⟨H,hH,d,p,hp,isNilpotent_of_faithful_unitriangular σ hσ hs hsd,hd⟩

end Unitriangular

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.TriangularStructure

-- BEGIN COMPLETE MODULE HirschProof.LinearZariskiComponent
section
                                     
                                      

set_option autoImplicit false

noncomputable section

namespace LocalHirschHyperfinite
open Set Topology TopologicalSpace

section Components

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The identity component is a subgroup when translations and inversion
are continuous. Joint continuity for multiplication is unnecessary. -/
def identityComponent (hL : ∀ a : G, Continuous (fun x : G => a*x))
    (hI : Continuous (fun x : G => x⁻¹)) : Subgroup G where
  carrier := connectedComponent 1
  one_mem' := mem_connectedComponent
  mul_mem' := by
    intro x y hx hy
    have hz := (hL x).mapsTo_connectedComponent 1 hy
    rw [mul_one,← connectedComponent_eq hx] at hz
    exact hz
  inv_mem' := by
    intro x hx
    have hz := hI.mapsTo_connectedComponent 1 hx
    simpa only [inv_one] using hz

theorem identityComponent_normal (hL : ∀ a : G, Continuous (fun x : G => a*x))
    (hR : ∀ a : G, Continuous (fun x : G => x*a)) (hI : Continuous (fun x : G => x⁻¹)) :
    (identityComponent hL hI).Normal := by
  constructor
  intro x hx g
  have hg : Continuous (fun x : G => g*x*g⁻¹) := (hR g⁻¹).comp (hL g)
  have hz := hg.mapsTo_connectedComponent 1 hx
  simpa only [mul_one,mul_inv_cancel] using hz

/-- A Noetherian space with continuous left translations and inversion has
only finitely many cosets of the identity component. -/
theorem identityComponent_finiteIndex [NoetherianSpace G]
    (hL : ∀ a : G, Continuous (fun x : G => a*x)) (hI : Continuous (fun x : G => x⁻¹)) :
    (identityComponent hL hI).FiniteIndex := by
  classical
  let H := identityComponent hL hI
  let I := irreducibleComponents G
  letI : Finite I := (NoetherianSpace.finite_irreducibleComponents (α := G)).to_subtype
  let p (s : I) : G := Classical.choose s.property.1.1
  have hp (s : I) : p s ∈ s.val := Classical.choose_spec s.property.1.1
  let f (s : I) : G ⧸ H := QuotientGroup.mk (p s)
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g ∈ ⋃₀ I := by simp [I,sUnion_irreducibleComponents]
    obtain ⟨s,hs,hgs⟩ := mem_sUnion.mp hg
    let b : I := ⟨s,hs⟩
    refine ⟨b,?_⟩
    have hConn : s ⊆ connectedComponent g := hs.1.isConnected.subset_connectedComponent hgs
    have hz := (hL g⁻¹).mapsTo_connectedComponent g (hConn (hp b))
    rw [inv_mul_cancel] at hz
    change (QuotientGroup.mk (p b) : G ⧸ H) = QuotientGroup.mk g
    exact (QuotientGroup.eq.mpr hz).symm
  exact Subgroup.finiteIndex_iff_finite_quotient.mpr (Finite.of_surjective f hfs)

end Components

section Matrices

variable {G K : Type*} [Group G] [Field K] {n : ℕ}
local notation "Square" => fun K n => Matrix (Fin n) (Fin n) K

/-- The matrix and inverse matrix entries give polynomial coordinates in
which the translations and group inversion are polynomial substitutions. -/
def matrixCoordinates (ρ : G →* (Square K n)ˣ) (g : G) (c : Bool × Fin n × Fin n) : K :=
  ((if c.1 then ρ g⁻¹ else ρ g) : Square K n) c.2.1 c.2.2

/-- The Zariski topology associated to a matrix representation. -/
@[implicit_reducible]
def matrixZariskiTopology (ρ : G →* (Square K n)ˣ) : TopologicalSpace G :=
  polynomialTopology (matrixCoordinates ρ)

variable (ρ : G →* (Square K n)ˣ)

theorem matrixZariski_left_poly (a : G) (c : Bool × Fin n × Fin n) :
    PolynomialAlong (matrixCoordinates ρ) (fun x : G => matrixCoordinates ρ (a*x) c) := by
  obtain ⟨b,i,j⟩ := c
  cases b
  · have he (x : G) : matrixCoordinates ρ (a*x) (false,i,j) =
        ∑ k : Fin n, (ρ a : Square K n) i k * matrixCoordinates ρ x (false,k,j) := by
      simp [matrixCoordinates,map_mul,Matrix.mul_apply]
    simp_rw [he]
    exact PolynomialAlong.sum _ _ (fun k _ => (PolynomialAlong.constant _).mul (PolynomialAlong.coord _))
  · have he (x : G) : matrixCoordinates ρ (a*x) (true,i,j) =
        ∑ k : Fin n, matrixCoordinates ρ x (true,i,k) * (ρ a⁻¹ : Square K n) k j := by
      simp [matrixCoordinates,mul_inv_rev,map_mul,Matrix.mul_apply]
    simp_rw [he]
    exact PolynomialAlong.sum _ _ (fun k _ => (PolynomialAlong.coord _).mul (PolynomialAlong.constant _))

theorem matrixZariski_right_poly (a : G) (c : Bool × Fin n × Fin n) :
    PolynomialAlong (matrixCoordinates ρ) (fun x : G => matrixCoordinates ρ (x*a) c) := by
  obtain ⟨b,i,j⟩ := c
  cases b
  · have he (x : G) : matrixCoordinates ρ (x*a) (false,i,j) =
        ∑ k : Fin n, matrixCoordinates ρ x (false,i,k) * (ρ a : Square K n) k j := by
      simp [matrixCoordinates,map_mul,Matrix.mul_apply]
    simp_rw [he]
    exact PolynomialAlong.sum _ _ (fun k _ => (PolynomialAlong.coord _).mul (PolynomialAlong.constant _))
  · have he (x : G) : matrixCoordinates ρ (x*a) (true,i,j) =
        ∑ k : Fin n, (ρ a⁻¹ : Square K n) i k * matrixCoordinates ρ x (true,k,j) := by
      simp [matrixCoordinates,mul_inv_rev,map_mul,Matrix.mul_apply]
    simp_rw [he]
    exact PolynomialAlong.sum _ _ (fun k _ => (PolynomialAlong.constant _).mul (PolynomialAlong.coord _))

theorem matrixZariski_left (a : G) :
    @Continuous G G (matrixZariskiTopology ρ) (matrixZariskiTopology ρ) (fun x : G => a*x) :=
  polynomialTopology_continuous (matrixZariski_left_poly ρ a)

theorem matrixZariski_right (a : G) :
    @Continuous G G (matrixZariskiTopology ρ) (matrixZariskiTopology ρ) (fun x : G => x*a) :=
  polynomialTopology_continuous (matrixZariski_right_poly ρ a)

theorem matrixZariski_inv :
    @Continuous G G (matrixZariskiTopology ρ) (matrixZariskiTopology ρ) (fun x : G => x⁻¹) := by
  apply polynomialTopology_continuous
  rintro ⟨b,i,j⟩
  cases b
  · exact PolynomialAlong.coord (true,i,j)
  · change PolynomialAlong (matrixCoordinates ρ) (fun x => (ρ (x⁻¹)⁻¹ : Square K n) i j)
    simp_rw [inv_inv]
    exact PolynomialAlong.coord (false,i,j)

/-- Every represented group has a normal finite-index Zariski-connected
component, with the topology induced by its matrix entries. -/
theorem exists_finiteIndex_zariskiConnected :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      @IsConnected G (matrixZariskiTopology ρ) (H : Set G) := by
  letI := matrixZariskiTopology ρ
  letI : NoetherianSpace G := polynomialTopology_noetherian (matrixCoordinates ρ)
  exact ⟨identityComponent (matrixZariski_left ρ) (matrixZariski_inv ρ),
    identityComponent_normal (matrixZariski_left ρ) (matrixZariski_right ρ) (matrixZariski_inv ρ),
    identityComponent_finiteIndex (matrixZariski_left ρ) (matrixZariski_inv ρ),
    isConnected_connectedComponent⟩

end Matrices

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.LinearZariskiComponent

-- BEGIN COMPLETE MODULE HirschProof.ConnectedDerivedSubgroups
section
                                         
                                               

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set Topology TopologicalSpace
open scoped Pointwise commutatorElement

section GroupTopology

variable {G : Type*} [Group G] [TopologicalSpace G]

private theorem preconnected_pointwise_mul {S T : Set G} (hS : IsPreconnected S)
    (hT : IsPreconnected T) (hL : ∀ a : G, Continuous (fun x : G => a*x))
    (hR : ∀ a : G, Continuous (fun x : G => x*a)) : IsPreconnected (S*T) := by
  rcases T.eq_empty_or_nonempty with rfl|⟨t,ht⟩
  · simp [isPreconnected_empty]
  apply isPreconnected_of_forall_pair
  rintro _ ⟨a,ha,b,hb,rfl⟩ _ ⟨c,hc,d,hd,rfl⟩
  let A := (fun x => a*x) '' T
  let B := (fun x => x*t) '' S
  let C := (fun x => c*x) '' T
  have hA : IsPreconnected A := hT.image _ (hL a).continuousOn
  have hB : IsPreconnected B := hS.image _ (hR t).continuousOn
  have hC : IsPreconnected C := hT.image _ (hL c).continuousOn
  have htA : a*t ∈ A := ⟨t,ht,rfl⟩
  have htB : a*t ∈ B := ⟨a,ha,rfl⟩
  have htC : c*t ∈ C := ⟨t,ht,rfl⟩
  have htB' : c*t ∈ B := ⟨c,hc,rfl⟩
  have hAB : IsPreconnected (A∪B) := hA.union _ htA htB hB
  have hABC : IsPreconnected ((A∪B)∪C) := hAB.union _ (Or.inr htB') htC hC
  refine ⟨(A∪B)∪C,?_,Or.inl (Or.inl ⟨b,hb,rfl⟩),Or.inr ⟨d,hd,rfl⟩,hABC⟩
  apply union_subset (union_subset ?_ ?_) ?_
  · rintro _ ⟨z,hz,rfl⟩
    exact Set.mul_mem_mul ha hz
  · rintro _ ⟨z,hz,rfl⟩
    exact Set.mul_mem_mul hz ht
  · rintro _ ⟨z,hz,rfl⟩
    exact Set.mul_mem_mul hc hz

/-- With separately continuous multiplication and continuous inversion,
the subgroup generated by a preconnected set containing the identity is
preconnected. -/
theorem preconnected_subgroupClosure {S : Set G} (hS : IsPreconnected S) (h1 : (1 : G) ∈ S)
    (hL : ∀ a : G, Continuous (fun x : G => a*x))
    (hR : ∀ a : G, Continuous (fun x : G => x*a))
    (hI : Continuous (fun x : G => x⁻¹)) : IsPreconnected (Subgroup.closure S : Set G) := by
  apply isPreconnected_of_forall (1 : G)
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    exact ⟨S,Subgroup.subset_closure,h1,hx,hS⟩
  | one =>
    exact ⟨{1},singleton_subset_iff.mpr (Subgroup.one_mem _),rfl,rfl,isPreconnected_singleton⟩
  | mul x y hx hy hx' hy' =>
    obtain ⟨A,hA,h1A,hxA,hpA⟩ := hx'
    obtain ⟨B,hB,h1B,hyB,hpB⟩ := hy'
    refine ⟨A*B,?_,?_,Set.mul_mem_mul hxA hyB,preconnected_pointwise_mul hpA hpB hL hR⟩
    · rintro _ ⟨a,ha,b,hb,rfl⟩
      exact Subgroup.mul_mem _ (hA ha) (hB hb)
    · simpa only [one_mul] using Set.mul_mem_mul h1A h1B
  | inv x hx hx' =>
    obtain ⟨A,hA,h1A,hxA,hpA⟩ := hx'
    refine ⟨(fun y : G => y⁻¹) '' A,?_,⟨1,h1A,inv_one⟩,⟨x,hxA,rfl⟩,hpA.image _ hI.continuousOn⟩
    rintro _ ⟨a,ha,rfl⟩
    exact Subgroup.inv_mem _ (hA ha)

/-- For a preconnected group with continuous one-variable commutator maps,
its derived subgroup is connected in the induced topology. -/
theorem connected_commutator_of_preconnected [PreconnectedSpace G]
    (hL : ∀ a : G, Continuous (fun x : G => a*x))
    (hR : ∀ a : G, Continuous (fun x : G => x*a))
    (hI : Continuous (fun x : G => x⁻¹))
    (hC : ∀ a : G, Continuous (fun x : G => ⁅x,a⁆)) : IsConnected (commutator G : Set G) := by
  have hpre : IsPreconnected (commutatorSet G) := by
    apply isPreconnected_of_forall (1 : G)
    intro x hx
    obtain ⟨g,a,rfl⟩ := mem_commutatorSet_iff.mp hx
    let W := (fun z : G => ⁅z,a⁆) '' univ
    refine ⟨W,?_,⟨1,mem_univ _,by simp⟩,⟨g,mem_univ _,rfl⟩,
      isPreconnected_univ.image _ (hC a).continuousOn⟩
    rintro _ ⟨v,_,rfl⟩
    exact commutator_mem_commutatorSet (g₁ := v) (g₂ := a)
  refine ⟨⟨1,Subgroup.one_mem _⟩,?_⟩
  rw [commutator_eq_closure]
  exact preconnected_subgroupClosure hpre (one_mem_commutatorSet G) hL hR hI

end GroupTopology

section MatrixTopology

variable {G K : Type*} [Group G] [Field K] {n : ℕ}
local notation "Square" => fun K n => Matrix (Fin n) (Fin n) K

variable {ρ : G →* (Square K n)ˣ}

/-- Maps of a group into itself that are polynomial in the matrix and
inverse matrix entries of a representation. -/
def MatrixPolynomialMap (ρ : G →* (Square K n)ˣ) (f : G → G) : Prop :=
  ∀ c, PolynomialAlong (matrixCoordinates ρ) (fun x => matrixCoordinates ρ (f x) c)

theorem MatrixPolynomialMap.id : MatrixPolynomialMap ρ id := fun c => PolynomialAlong.coord c

theorem MatrixPolynomialMap.constant (a : G) : MatrixPolynomialMap ρ (fun _ => a) :=
  fun c => PolynomialAlong.constant (matrixCoordinates ρ a c)

theorem MatrixPolynomialMap.mul {f g : G → G}
    (hf : MatrixPolynomialMap ρ f) (hg : MatrixPolynomialMap ρ g) :
    MatrixPolynomialMap ρ (fun x => f x*g x) := by
  rintro ⟨b,i,j⟩
  cases b
  · have he (x : G) : matrixCoordinates ρ (f x*g x) (false,i,j) =
        ∑ k : Fin n, matrixCoordinates ρ (f x) (false,i,k) * matrixCoordinates ρ (g x) (false,k,j) := by
      simp [matrixCoordinates,map_mul,Matrix.mul_apply]
    simp_rw [he]
    exact PolynomialAlong.sum _ _ (fun k _ => (hf (false,i,k)).mul (hg (false,k,j)))
  · have he (x : G) : matrixCoordinates ρ (f x*g x) (true,i,j) =
        ∑ k : Fin n, matrixCoordinates ρ (g x) (true,i,k) * matrixCoordinates ρ (f x) (true,k,j) := by
      simp [matrixCoordinates,mul_inv_rev,map_mul,Matrix.mul_apply]
    simp_rw [he]
    exact PolynomialAlong.sum _ _ (fun k _ => (hg (true,i,k)).mul (hf (true,k,j)))

theorem MatrixPolynomialMap.inv {f : G → G} (hf : MatrixPolynomialMap ρ f) :
    MatrixPolynomialMap ρ (fun x => (f x)⁻¹) := by
  rintro ⟨b,i,j⟩
  cases b
  · exact hf (true,i,j)
  · change PolynomialAlong (matrixCoordinates ρ) (fun x => (ρ ((f x)⁻¹)⁻¹ : Square K n) i j)
    simp_rw [inv_inv]
    exact hf (false,i,j)

theorem matrixZariski_commutator (a : G) :
    @Continuous G G (matrixZariskiTopology ρ) (matrixZariskiTopology ρ) (fun x : G => ⁅x,a⁆) := by
  have h := ((MatrixPolynomialMap.id.mul (MatrixPolynomialMap.constant (ρ := ρ) a)).mul
    MatrixPolynomialMap.id.inv).mul (MatrixPolynomialMap.constant a⁻¹)
  exact polynomialTopology_continuous h

/-- The derived subgroup of a Zariski-connected represented group is
Zariski-connected as well. -/
theorem matrixZariski_connected_commutator (h : @PreconnectedSpace G (matrixZariskiTopology ρ)) :
    @IsConnected G (matrixZariskiTopology ρ) (commutator G : Set G) := by
  letI := matrixZariskiTopology ρ
  letI := h
  exact connected_commutator_of_preconnected (matrixZariski_left ρ) (matrixZariski_right ρ)
    (matrixZariski_inv ρ) matrixZariski_commutator

end MatrixTopology

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.ConnectedDerivedSubgroups

-- BEGIN COMPLETE MODULE HirschProof.SimultaneousEigenvectors
section
                                                        
                                             

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The simultaneous eigenspace of a family of endomorphisms at the given
family of eigenvalues. -/
def jointEigenspace (f : ι → Module.End K V) (χ : ι → K) : Submodule K V :=
  ⨅ i, (f i).eigenspace (χ i)

theorem mem_jointEigenspace {f : ι → Module.End K V} {χ : ι → K} {v : V} :
    v ∈ jointEigenspace f χ ↔ ∀ i, f i v = χ i • v := by
  simp [jointEigenspace]

/-- The nonzero simultaneous eigenspaces of any family form a finite
family in finite dimension. No commutation assumption is needed here. -/
theorem finite_jointEigenspaces [FiniteDimensional K V] (f : ι → Module.End K V) :
    {χ | jointEigenspace f χ ≠ ⊥}.Finite := by
  have h : iSupIndep (jointEigenspace f) :=
    iSupIndep.iInf (fun i => (f i).eigenspace) (fun i => (f i).eigenspaces_iSupIndep)
  exact WellFoundedGT.finite_ne_bot_of_iSupIndep h

/-- Commuting endomorphisms over an algebraically closed field admit a
nonzero common eigenvector. A least-dimensional nonzero invariant space
must consist of eigenvectors for each member of the family. -/
theorem exists_jointEigenvector_of_commute [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V]
    (f : ι → Module.End K V) (hcomm : ∀ i j : ι, Commute (f i) (f j)) :
    ∃ v : V, v ≠ 0 ∧ ∃ χ : ι → K, v ∈ jointEigenspace f χ := by
  classical
  let P (n : ℕ) := ∃ W : Submodule K V, W ≠ ⊥ ∧
    (∀ i, MapsTo (f i) (W : Set V) W) ∧ Module.finrank K W = n
  have hP : ∃ n, P n := ⟨_,⊤,top_ne_bot,fun _ _ _ => Submodule.mem_top,rfl⟩
  obtain ⟨W,hW,hInv,hdim⟩ := Nat.find_spec hP
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let F (i : ι) : Module.End K W := (f i).restrict (hInv i)
  have hFC (i j : ι) : Commute (F i) (F j) := by
    change F i * F j = F j * F i
    ext w
    exact congrArg (fun T : Module.End K V => T w.val) (hcomm i j).eq
  have hscalar (i : ι) : ∃ a : K, ∀ w : W, F i w = a • w := by
    obtain ⟨a,ha⟩ := (F i).exists_eigenvalue
    let E := (F i).eigenspace a
    have hE : E ≠ ⊥ := ha
    have hEI (j : ι) : MapsTo (F j) (E : Set W) E := by
      intro w hw
      have heq : F i w = a • w := (Module.End.mem_eigenspace_iff.mp hw)
      apply Module.End.mem_eigenspace_iff.mpr
      have h := congrArg (fun T : Module.End K W => T w) (hFC i j).eq
      change F i (F j w) = F j (F i w) at h
      exact h.trans (by rw [heq,map_smul])
    have hTop : E = ⊤ := by
      by_contra hproper
      let M := E.map W.subtype
      have hM : M ≠ ⊥ := by
        intro hz
        exact hE (Submodule.map_injective_of_injective W.subtype_injective
          (hz.trans (Submodule.map_bot _).symm))
      have hMI (j : ι) : MapsTo (f j) (M : Set V) M := by
        rintro _ ⟨w,hw,rfl⟩
        exact ⟨F j w,hEI j hw,rfl⟩
      have hdim' : Module.finrank K M = Module.finrank K E :=
        (Submodule.equivMapOfInjective W.subtype W.subtype_injective E).finrank_eq.symm
      have hlt : Module.finrank K E < Module.finrank K W :=
        Submodule.finrank_lt hproper
      have hmin := Nat.find_min' hP (m := Module.finrank K M) ⟨M,hM,hMI,rfl⟩
      omega
    refine ⟨a,fun w => Module.End.mem_eigenspace_iff.mp ?_⟩
    change w ∈ E
    rw [hTop]
    exact Submodule.mem_top
  choose χ hχ using hscalar
  obtain ⟨w,hw⟩ := exists_ne (0 : W)
  refine ⟨w.val,fun hz => hw (Subtype.ext hz),χ,mem_jointEigenspace.mpr ?_⟩
  intro i
  exact congrArg (fun z : W => z.val) (hχ i w)

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.SimultaneousEigenvectors

-- BEGIN COMPLETE MODULE HirschProof.InvariantWeightSpaces
section
                                            
                                           
                                        
                                        

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set Topology TopologicalSpace

variable {K V G ι : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- The scalar matrix coefficients of a linear action are polynomial in
the chosen coordinates on the group. -/
def PolynomialLinearCoefficients (v : G → ι → K) (a : G →* (V ≃ₗ[K] V)) : Prop :=
  ∀ (w : V) (ℓ : V →ₗ[K] K), PolynomialAlong v (fun g => ℓ (a g w))

/-- Use the topology induced from the original representation on every
subgroup used in a derived-length induction. -/
theorem matrixZariskiTopology_subgroup {n : ℕ} (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ)
    (H : Subgroup G) : matrixZariskiTopology (ρ.comp H.subtype) =
      TopologicalSpace.induced (fun x : H => x.val) (matrixZariskiTopology ρ) := by
  unfold matrixZariskiTopology polynomialTopology
  rw [induced_compose]
  rfl

variable {v : G → ι → K} {a : G →* (V ≃ₗ[K] V)}

theorem PolynomialLinearCoefficients.subgroup (h : PolynomialLinearCoefficients v a) (H : Subgroup G) :
    PolynomialLinearCoefficients (v ∘ H.subtype) (a.comp H.subtype) := by
  intro w ℓ
  obtain ⟨p,hp⟩ := h w ℓ
  exact ⟨p,fun g => hp g.val⟩

private theorem isClosed_vector_eq_of_scalar_eq [FiniteDimensional K V] {F L : G → V}
    (h : ∀ ℓ : V →ₗ[K] K, @IsClosed G (polynomialTopology v) {g | ℓ (F g) = ℓ (L g)}) :
    @IsClosed G (polynomialTopology v) {g | F g = L g} := by
  letI := polynomialTopology v
  have he : {g | F g = L g} = ⋂ ℓ : V →ₗ[K] K, {g | ℓ (F g) = ℓ (L g)} := by
    ext g
    simp only [mem_setOf_eq,mem_iInter]
    refine ⟨fun hg _ => congrArg _ hg,fun hg => Module.eval_apply_injective K ?_⟩
    ext ℓ
    exact hg ℓ
  rw [he]
  exact isClosed_iInter h

/-- A connected represented group preserves each nonzero weight space
of a normal subgroup. Its translates lie in a finite set of weight spaces,
and each possible destination has a closed preimage. -/
theorem invariant_jointEigenspace_of_preconnected [FiniteDimensional K V]
    (hcoord : PolynomialLinearCoefficients v a) (hconn : @PreconnectedSpace G (polynomialTopology v))
    (N : Subgroup G) [N.Normal] (χ : N → K)
    (hχ : jointEigenspace (fun n : N => (a n.val : Module.End K V)) χ ≠ ⊥) :
    ∀ g : G, MapsTo (a g) (jointEigenspace (fun n : N => (a n.val : Module.End K V)) χ : Set V)
      (jointEigenspace (fun n : N => (a n.val : Module.End K V)) χ : Set V) := by
  classical
  letI := polynomialTopology v
  letI := hconn
  let f (n : N) : Module.End K V := a n.val
  let W := jointEigenspace f χ
  let I := {ψ | jointEigenspace f ψ ≠ ⊥}
  have hI : I.Finite := finite_jointEigenspaces f
  let D (ψ : N → K) : Set G := {g | MapsTo (a g) (W : Set V) (jointEigenspace f ψ : Set V)}
  have hclosed (ψ : N → K) : IsClosed (D ψ) := by
    have hd : D ψ = ⋂ w : W, ⋂ n : N, {g | f n (a g w.val) = ψ n • a g w.val} := by
      ext g
      simp only [D,mem_setOf_eq,mem_iInter]
      refine ⟨fun h w => mem_jointEigenspace.mp (h w.property),fun h w hw => ?_⟩
      exact mem_jointEigenspace.mpr (h ⟨w,hw⟩)
    rw [hd]
    apply isClosed_iInter
    intro w
    apply isClosed_iInter
    intro n
    apply isClosed_vector_eq_of_scalar_eq (v := v)
    intro ℓ
    have hF := hcoord w.val (ℓ.comp (f n))
    have hL := (PolynomialAlong.constant (v := v) (ψ n)).mul (hcoord w.val ℓ)
    simpa only [LinearMap.comp_apply,map_smul,smul_eq_mul] using hF.isClosed_eq hL
  obtain ⟨w₀,hw₀,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hcover (g : G) : ∃ ψ ∈ I, g ∈ D ψ := by
    let c (n : N) : N := ⟨g⁻¹*n.val*g,by
      simpa only [inv_inv] using ‹N.Normal›.conj_mem n.val n.property g⁻¹⟩
    let ψ (n : N) := χ (c n)
    have hg : g ∈ D ψ := by
      intro x hx
      apply mem_jointEigenspace.mpr
      intro n
      have he : n.val*g = g*(c n).val := by change n.val*g = g*(g⁻¹*n.val*g); group
      have hχ' := mem_jointEigenspace.mp hx (c n)
      calc
        f n (a g x) = a (n.val*g) x := by rw [map_mul]; rfl
        _ = a (g*(c n).val) x := by rw [he]
        _ = a g (f (c n) x) := by rw [map_mul]; rfl
        _ = ψ n • a g x := by rw [hχ',map_smul]
    refine ⟨ψ,?_,hg⟩
    intro hbot
    have he : a g w₀ ∈ jointEigenspace f ψ := hg hw₀
    rw [hbot,Submodule.mem_bot] at he
    exact hne ((a g).injective (by simpa only [map_zero] using he))
  have hunique {g : G} {ψ θ : N → K} (hp : g ∈ D ψ) (ht : g ∈ D θ) : ψ = θ := by
    funext n
    have he := (mem_jointEigenspace.mp (hp hw₀) n).symm.trans (mem_jointEigenspace.mp (ht hw₀) n)
    have hgn : a g w₀ ≠ 0 := fun h => hne ((a g).injective (by simpa only [map_zero] using h))
    exact smul_left_injective K hgn he
  have he : (D χ)ᶜ = ⋃ ψ ∈ I \ {χ}, D ψ := by
    ext g
    simp only [mem_compl_iff,mem_iUnion,mem_diff,mem_singleton_iff,exists_prop]
    constructor
    · intro hg
      obtain ⟨ψ,hψ,hgψ⟩ := hcover g
      refine ⟨ψ,⟨hψ,fun h => hg (h ▸ hgψ)⟩,hgψ⟩
    · rintro ⟨ψ,⟨_,hn⟩,hp⟩ ht
      exact hn (hunique hp ht)
  have hOpen : IsOpen (D χ) := by
    apply isClosed_compl_iff.mp
    rw [he]
    exact hI.diff.isClosed_biUnion (fun ψ _ => hclosed ψ)
  have h1 : (1 : G) ∈ D χ := by
    intro w hw
    simpa using hw
  have hAll : D χ = univ := IsClopen.eq_univ ⟨hclosed χ,hOpen⟩ ⟨1,h1⟩
  intro g
  have hmem : g ∈ D χ := hAll.symm ▸ mem_univ g
  exact hmem

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.InvariantWeightSpaces

-- BEGIN COMPLETE MODULE HirschProof.SolvableEigenline
section
                                        
                                        
                                       

set_option autoImplicit false

noncomputable section

namespace LocalHirschHyperfinite
open Set Topology TopologicalSpace
open scoped Polynomial commutatorElement

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

/-- The action induced on an invariant subspace. -/
def restrictedLinearAction (a : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (h : ∀ g, MapsTo (a g) (W : Set V) W) : G →* (W ≃ₗ[K] W) where
  toFun g := {
    toLinearMap := (a g : Module.End K V).restrict (h g)
    invFun := fun w => ⟨a g⁻¹ w.val,h g⁻¹ w.property⟩
    left_inv := by
      intro w
      apply Subtype.ext
      change a g⁻¹ (a g w.val) = w.val
      rw [← LinearEquiv.mul_apply,← map_mul,inv_mul_cancel,map_one]
      rfl
    right_inv := by
      intro w
      apply Subtype.ext
      change a g (a g⁻¹ w.val) = w.val
      rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
      rfl }
  map_one' := by ext w; simp
  map_mul' g h := by ext w; exact congrArg (fun f : V ≃ₗ[K] V => f w.val) (map_mul a g h)

private theorem finite_pow_eq_one {m : ℕ} (hm : 0 < m) :
    {x : K | x^m=1}.Finite := by
  let p : K[X] := Polynomial.X^m-1
  have hp : p ≠ 0 := by
    intro h
    have h' := congrArg (fun f : K[X] => f.coeff m) h
    simp [p,Polynomial.coeff_X_pow,Polynomial.coeff_one,ne_of_gt hm] at h'
  have hF := Polynomial.finite_setOf_isRoot hp
  simpa [p,Polynomial.IsRoot,sub_eq_zero] using hF

private theorem coeff_eq_one_on_derived [FiniteDimensional K V] {n : ℕ}
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ) (a : G →* (V ≃ₗ[K] V))
    (hcoord : PolynomialLinearCoefficients (matrixCoordinates ρ) a)
    (hconn : @PreconnectedSpace G (matrixZariskiTopology ρ))
    (χ : commutator G → K)
    (hχ : jointEigenspace (fun h : commutator G => (a h.val : Module.End K V)) χ ≠ ⊥) :
    ∀ h, χ h = 1 := by
  classical
  let N := commutator G
  let W := jointEigenspace (fun h : N => (a h.val : Module.End K V)) χ
  have hW := invariant_jointEigenspace_of_preconnected hcoord hconn N χ hχ
  let b := restrictedLinearAction a W hW
  let δ := (LinearEquiv.det (R := K) (M := W)).comp b
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hχ
  let m := Module.finrank K W
  have hm : 0 < m := Module.finrank_pos
  have hpower (h : N) : (χ h)^m = 1 := by
    have hd : δ h.val = 1 := Abelianization.commutator_subset_ker δ h.property
    have hscalar : (b h.val : Module.End K W) = χ h • 1 := by
      ext w
      change a h.val w.val = χ h • w.val
      exact mem_jointEigenspace.mp w.property h
    have hval : LinearMap.det (b h.val : Module.End K W) = 1 := by
      have he := congrArg (fun t : Kˣ => (t : K)) hd
      simpa only [δ,MonoidHom.comp_apply,LinearEquiv.coe_det,Units.val_one] using he
    rwa [hscalar,LinearMap.det_smul,map_one,mul_one] at hval
  letI := matrixZariskiTopology ρ
  have hnconn := matrixZariski_connected_commutator hconn
  letI := matrixZariskiTopology (ρ.comp N.subtype)
  haveI : PreconnectedSpace N := by
    change @PreconnectedSpace N (matrixZariskiTopology (ρ.comp N.subtype))
    rw [matrixZariskiTopology_subgroup]
    exact isPreconnected_iff_preconnectedSpace.mp hnconn.isPreconnected
  obtain ⟨w,hw,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_eq_one K hne
  have heqn (s : N) : ℓ (a s.val w) = χ s := by
    have he : a s.val w = χ s • w := mem_jointEigenspace.mp hw s
    rw [he,map_smul,hℓ,smul_eq_mul,mul_one]
  have hp : PolynomialAlong (matrixCoordinates (ρ.comp N.subtype)) χ := by
    obtain ⟨p,hp⟩ := hcoord w ℓ
    exact ⟨p,fun s => (hp s.val).trans (heqn s)⟩
  let D : Set N := {s | χ s = 1}
  have hy (r : K) : IsClosed {s : N | χ s = r} := hp.isClosed_eq (PolynomialAlong.constant r)
  have hc : Dᶜ = ⋃ r ∈ {x : K | x^m=1} \ {1}, {s : N | χ s = r} := by
    ext s
    simp only [D,mem_compl_iff,mem_iUnion,mem_diff,mem_setOf_eq,mem_singleton_iff,exists_prop]
    exact ⟨fun hn => ⟨χ s,⟨hpower s,hn⟩,rfl⟩,fun ⟨_,⟨_,hn⟩,he⟩ => he.symm ▸ hn⟩
  have hO : IsOpen D := by
    apply isClosed_compl_iff.mp
    rw [hc]
    exact (finite_pow_eq_one (K := K) hm).diff.isClosed_biUnion (fun r _ => hy r)
  have h₁ : (1 : N) ∈ D := by
    change χ 1 = 1
    rw [← heqn 1]
    simpa using hℓ
  have hU : D = univ := IsClopen.eq_univ ⟨hy 1,hO⟩ ⟨1,h₁⟩
  intro s
  have hs : s ∈ D := hU.symm ▸ mem_univ s
  exact hs

private theorem eigenvector_of_derived_weight [IsAlgClosed K] [FiniteDimensional K V] {n : ℕ}
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ) (a : G →* (V ≃ₗ[K] V))
    (hcoord : PolynomialLinearCoefficients (matrixCoordinates ρ) a)
    (hconn : @PreconnectedSpace G (matrixZariskiTopology ρ))
    (χ : commutator G → K)
    (hχ : jointEigenspace (fun h : commutator G => (a h.val : Module.End K V)) χ ≠ ⊥) :
    ∃ x : V, x ≠ 0 ∧ ∀ g : G, ∃ t : K, a g x = t • x := by
  let N := commutator G
  let W := jointEigenspace (fun h : N => (a h.val : Module.End K V)) χ
  let b := restrictedLinearAction a W
    (invariant_jointEigenspace_of_preconnected hcoord hconn N χ hχ)
  have htriv : N ≤ b.ker := by
    intro g hg
    change b g = 1
    ext w
    change a g w.val = w.val
    let u : N := ⟨g,hg⟩
    have he := mem_jointEigenspace.mp w.property u
    simpa only [coeff_eq_one_on_derived ρ a hcoord hconn χ hχ u,one_smul] using he
  have hcomm (g h : G) : Commute (b g : Module.End K W) (b h : Module.End K W) := by
    have hc : b ⁅g,h⁆ = 1 := htriv (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hc
    change (b g : Module.End K W) * (b h : Module.End K W) = (b h : Module.End K W) * (b g : Module.End K W)
    exact congrArg (fun e : (W ≃ₗ[K] W) => (e : Module.End K W)) hc
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hχ
  obtain ⟨u,hu,ω,hω⟩ := exists_jointEigenvector_of_commute (fun g : G => (b g : Module.End K W)) hcomm
  refine ⟨u.val,fun he => hu (Subtype.ext he),fun g => ⟨ω g,?_⟩⟩
  exact congrArg (fun w : W => w.val) (mem_jointEigenspace.mp hω g)

/-- A solvable action with polynomial matrix coefficients on a
Zariski-connected represented group has a common eigenline. -/
theorem exists_eigenline_of_zariskiConnected_solvable [IsAlgClosed K] [FiniteDimensional K V]
    [Nontrivial V] [IsSolvable G] {n : ℕ}
    (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ) (a : G →* (V ≃ₗ[K] V))
    (hcoord : PolynomialLinearCoefficients (matrixCoordinates ρ) a)
    (hconn : @PreconnectedSpace G (matrixZariskiTopology ρ)) :
    ∃ x : V, x ≠ 0 ∧ ∀ g : G, ∃ t : K, a g x = t • x := by
  have main (k : ℕ) : ∀ (J : Type _) [Group J], derivedSeries J k = ⊥ →
      ∀ (σ : J →* (Matrix (Fin n) (Fin n) K)ˣ) (b : J →* (V ≃ₗ[K] V)),
        PolynomialLinearCoefficients (matrixCoordinates σ) b →
        @PreconnectedSpace J (matrixZariskiTopology σ) →
        ∃ x : V, x ≠ 0 ∧ ∀ g : J, ∃ t : K, b g x = t • x := by
    induction k with
    | zero =>
      intro J _ h σ b hσ hconn
      obtain ⟨x,hx⟩ := exists_ne (0 : V)
      refine ⟨x,hx,fun g => ⟨1,?_⟩⟩
      have heg : g = 1 := Subgroup.mem_bot.mp ((derivedSeries_zero J ▸ h) ▸ Subgroup.mem_top g)
      simp [heg]
    | succ k ih =>
      intro J _ h σ b hσ hconn
      let N := commutator J
      have hn : derivedSeries N k = ⊥ := by
        apply Subgroup.map_subtype_inj.mp
        rw [map_commutator_derivedSeries,Subgroup.map_bot,h]
      have hnc : @PreconnectedSpace N (matrixZariskiTopology (σ.comp N.subtype)) := by
        letI := matrixZariskiTopology σ
        rw [matrixZariskiTopology_subgroup]
        exact isPreconnected_iff_preconnectedSpace.mp (matrixZariski_connected_commutator hconn).isPreconnected
      obtain ⟨w,hne,hweight⟩ := ih N hn (σ.comp N.subtype) (b.comp N.subtype) (hσ.subgroup N) hnc
      choose χ hχ using hweight
      have hχ' : jointEigenspace (fun h : N => (b h.val : Module.End K V)) χ ≠ ⊥ := by
        intro he
        have hv := (mem_jointEigenspace (f := fun h : N => (b h.val : Module.End K V))).mpr hχ
        rw [he,Submodule.mem_bot] at hv
        exact hne hv
      exact eigenvector_of_derived_weight σ b hσ hconn χ hχ'
  obtain ⟨k,hk⟩ := IsSolvable.solvable (G := G)
  exact main k G hk ρ a hcoord hconn

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.SolvableEigenline

-- BEGIN COMPLETE MODULE HirschProof.TriangularLinearAction
section
                                    
                                       
                                       

set_option autoImplicit false

noncomputable section

namespace LocalHirschHyperfinite
open Set

universe uG uK uV

variable {G : Type uG} {K : Type uK} {V : Type uV} [Group G] [Field K] [AddCommGroup V] [Module K V]

/-- The action induced on the quotient by an invariant subspace. -/
def quotientLinearAction (a : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (h : ∀ g, MapsTo (a g) (W : Set V) W) : G →* ((V ⧸ W) ≃ₗ[K] (V ⧸ W)) where
  toFun g := {
    toLinearMap := W.mapQ W (a g : Module.End K V) (h g)
    invFun := W.mapQ W (a g⁻¹ : Module.End K V) (h g⁻¹)
    left_inv := by
      intro q
      obtain ⟨w,rfl⟩ := W.mkQ_surjective q
      change W.mkQ (a g⁻¹ (a g w)) = W.mkQ w
      rw [← LinearEquiv.mul_apply,← map_mul,inv_mul_cancel,map_one]
      rfl
    right_inv := by
      intro q
      obtain ⟨w,rfl⟩ := W.mkQ_surjective q
      change W.mkQ (a g (a g⁻¹ w)) = W.mkQ w
      rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel,map_one]
      rfl }
  map_one' := by
    ext q
    obtain ⟨w,rfl⟩ := W.mkQ_surjective q
    change W.mkQ (a 1 w) = W.mkQ w
    rw [map_one]
    rfl
  map_mul' g u := by
    ext q
    obtain ⟨w,rfl⟩ := W.mkQ_surjective q
    change W.mkQ (a (g*u) w) = W.mkQ (a g (a u w))
    rw [map_mul]
    rfl

theorem quotientLinearAction_mkQ (a : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (h : ∀ g, MapsTo (a g) (W : Set V) W) (g : G) (w : V) :
    quotientLinearAction a W h g (W.mkQ w) = W.mkQ (a g w) := rfl

theorem PolynomialLinearCoefficients.quotient {ι : Type*} {v : G → ι → K}
    {a : G →* (V ≃ₗ[K] V)} (hp : PolynomialLinearCoefficients v a) (W : Submodule K V)
    (h : ∀ g, MapsTo (a g) (W : Set V) W) :
    PolynomialLinearCoefficients v (quotientLinearAction a W h) := by
  intro q ℓ
  obtain ⟨w,rfl⟩ := W.mkQ_surjective q
  exact hp w (ℓ.comp W.mkQ)

private theorem invariant_span_singleton (a : G →* (V ≃ₗ[K] V)) (w : V)
    (h : ∀ g : G, ∃ t : K, a g w = t • w) :
    ∀ g, MapsTo (a g) (Submodule.span K {w} : Set V) (Submodule.span K {w} : Set V) := by
  intro g x hx
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨s,hs⟩ := h g
  rw [map_smul,hs]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem exists_basis_lift_of_line {d : ℕ} [FiniteDimensional K V]
    (W : Submodule K V) (hd : Module.finrank K W = 1) (b : Module.Basis (Fin d) K (V ⧸ W)) :
    ∃ B : Module.Basis (Fin (1+d)) K V,
      (∀ i, W.mkQ (B (Fin.castAdd d i)) = 0) ∧
      (∀ i, W.mkQ (B (Fin.natAdd 1 i)) = b i) ∧
      ∀ i x, B.repr x (Fin.natAdd 1 i) = b.repr (W.mkQ x) i := by
  obtain ⟨U,hU⟩ := W.exists_isCompl
  let e := ((LinearEquiv.refl K W).prodCongr (W.quotientEquivOfIsCompl U hU)).trans
    (W.prodEquivOfIsCompl U hU)
  have he (z : W × (V ⧸ W)) : W.mkQ (e z) = z.2 := by
    change W.mkQ ((z.1 : V) + ((W.quotientEquivOfIsCompl U hU) z.2).val) = z.2
    rw [map_add,show W.mkQ z.1.val = 0 from (Submodule.Quotient.mk_eq_zero W).mpr z.1.property,zero_add]
    exact W.mk_quotientEquivOfIsCompl_apply hU z.2
  let bw : Module.Basis (Fin 1) K W := Module.finBasisOfFinrankEq K W hd
  let bp := bw.prod b
  let B := (bp.map e).reindex finSumFinEquiv
  refine ⟨B,?_,?_,?_⟩
  · intro i
    rw [← finSumFinEquiv_apply_left]
    change W.mkQ (B (finSumFinEquiv (Sum.inl i))) = 0
    rw [Module.Basis.reindex_apply,Equiv.symm_apply_apply,Module.Basis.map_apply,he]
    exact Module.Basis.prod_apply_inl_snd bw b i
  · intro i
    rw [← finSumFinEquiv_apply_right]
    change W.mkQ (B (finSumFinEquiv (Sum.inr i))) = b i
    rw [Module.Basis.reindex_apply,Equiv.symm_apply_apply,Module.Basis.map_apply,he]
    exact Module.Basis.prod_apply_inr_snd bw b i
  · intro i x
    have hx : (e.symm x).2 = W.mkQ x := by simpa only [e.apply_symm_apply] using (he (e.symm x)).symm
    change B.repr x (Fin.natAdd 1 i) = b.repr (W.mkQ x) i
    rw [← finSumFinEquiv_apply_right,Module.Basis.repr_reindex_apply,
      Equiv.symm_apply_apply,Module.Basis.map_repr]
    change (bw.prod b).repr (e.symm x) (Sum.inr i) = b.repr (W.mkQ x) i
    rw [Module.Basis.prod_repr_inr,hx]

/-- A connected solvable group with polynomially parametrized linear
action admits a basis in which every operator is upper triangular. -/
theorem exists_triangular_basis_of_zariskiConnected_solvable [IsAlgClosed K] [IsSolvable G]
    [FiniteDimensional K V] {n : ℕ} (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ)
    (a : G →* (V ≃ₗ[K] V)) (hcoord : PolynomialLinearCoefficients (matrixCoordinates ρ) a)
    (hconn : @PreconnectedSpace G (matrixZariskiTopology ρ)) :
    ∃ d : ℕ, ∃ b : Module.Basis (Fin d) K V,
      ∀ (g : G) (i j : Fin d), j < i → b.repr (a g (b j)) i = 0 := by
  have main (m : ℕ) : ∀ (U : Type uV) [AddCommGroup U] [Module K U] [FiniteDimensional K U],
      Module.finrank K U = m → ∀ (f : G →* (U ≃ₗ[K] U)),
      PolynomialLinearCoefficients (matrixCoordinates ρ) f →
      ∃ d : ℕ, ∃ b : Module.Basis (Fin d) K U,
        ∀ (g : G) (i j : Fin d), j < i → b.repr (f g (b j)) i = 0 := by
    induction m with
    | zero =>
      intro U _ _ _ hu f hf
      exact ⟨0,Module.finBasisOfFinrankEq K U hu,fun _ i => Fin.elim0 i⟩
    | succ m ih =>
      intro U _ _ _ hu f hf
      letI : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hu]; exact Nat.succ_pos _)
      obtain ⟨w,hne,hw⟩ := exists_eigenline_of_zariskiConnected_solvable ρ f hf hconn
      let W := Submodule.span K {w}
      have hd : Module.finrank K W = 1 := finrank_span_singleton hne
      have hq : Module.finrank K (U ⧸ W) = m := by
        have he := W.finrank_quotient_add_finrank
        omega
      let hI := invariant_span_singleton f w hw
      let fq := quotientLinearAction f W hI
      obtain ⟨d,b,hb⟩ := ih (U ⧸ W) hq fq (hf.quotient W hI)
      obtain ⟨B,hLeft,hRight,hRepr⟩ := exists_basis_lift_of_line W hd b
      refine ⟨1+d,B,fun g i j hji => ?_⟩
      obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective i
      obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective j
      rcases t with t|t
      · exfalso
        rw [finSumFinEquiv_apply_left] at hji
        have ht : t.val = 0 := by omega
        change _ < t.val at hji
        omega
      · rw [finSumFinEquiv_apply_right,hRepr,← quotientLinearAction_mkQ f W hI]
        rcases u with u|u
        · rw [finSumFinEquiv_apply_left,hLeft,map_zero,map_zero,Finsupp.zero_apply]
        · rw [finSumFinEquiv_apply_right,hRight]
          apply hb
          rw [finSumFinEquiv_apply_right,finSumFinEquiv_apply_right] at hji
          exact Fin.lt_iff_val_lt_val.mpr (by
            change 1+u.val < 1+t.val at hji
            omega)
  exact main _ V rfl a hcoord

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.TriangularLinearAction

-- BEGIN COMPLETE MODULE HirschProof.VirtualTriangularization
section
                                         

set_option autoImplicit false

noncomputable section

namespace LocalHirschHyperfinite

variable {G K : Type*} [Group G] [Field K] {n : ℕ}
local notation "Square" => fun K n => Matrix (Fin n) (Fin n) K

private def matrixLinearAction (ρ : G →* (Square K n)ˣ) :
    G →* ((Fin n → K) ≃ₗ[K] Fin n → K) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).toMonoidHom.comp
    ((Units.mapEquiv Matrix.toLinAlgEquiv'.toRingEquiv.toMulEquiv).toMonoidHom.comp ρ)

private theorem matrixLinearAction_injective (ρ : G →* (Square K n)ˣ)
    (hi : Function.Injective ρ) : Function.Injective (matrixLinearAction ρ) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).injective.comp
    ((Units.mapEquiv Matrix.toLinAlgEquiv'.toRingEquiv.toMulEquiv).injective.comp hi)

private theorem matrixLinearAction_coefficients (ρ : G →* (Square K n)ˣ) :
    PolynomialLinearCoefficients (matrixCoordinates ρ) (matrixLinearAction ρ) := by
  classical
  intro w ℓ
  let e := Pi.basisFun K (Fin n)
  have he (x : Fin n → K) : ℓ x = ∑ i : Fin n, x i * ℓ (e i) := by
    conv_lhs => rw [← e.sum_repr x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    rfl
  have h (g : G) : ℓ (matrixLinearAction ρ g w) =
      ∑ i : Fin n, (∑ j : Fin n, matrixCoordinates ρ g (false,i,j) * w j) * ℓ (e i) := by
    rw [he]
    rfl
  simp_rw [h]
  exact PolynomialAlong.sum _ _ (fun i _ => (PolynomialAlong.sum _ _ (fun j _ =>
    (PolynomialAlong.coord (false,i,j)).mul (PolynomialAlong.constant (w j)))).mul
    (PolynomialAlong.constant (ℓ (e i))))


/-- Retain the intertwining basis when triangularizing a possibly nonfaithful
matrix action of a solvable group. -/
theorem exists_finiteIndex_triangular_basis_of_matrix [IsAlgClosed K] [IsSolvable G]
    (ρ : G →* (Square K n)ˣ) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∃ d : ℕ, ∃ b : Module.Basis (Fin d) K (Fin n → K),
        ∀ (g : H) (i j : Fin d), j < i →
          b.repr ((ρ g.val).val.mulVec (b j)) i = 0 := by
  obtain ⟨H,hn,hH,hC⟩ := exists_finiteIndex_zariskiConnected ρ
  let ρH := ρ.comp H.subtype
  let a := matrixLinearAction ρH
  have hp := matrixLinearAction_coefficients ρH
  have hc : @PreconnectedSpace H (matrixZariskiTopology ρH) := by
    letI := matrixZariskiTopology ρ
    change @PreconnectedSpace H (matrixZariskiTopology (ρ.comp H.subtype))
    rw [matrixZariskiTopology_subgroup]
    exact isPreconnected_iff_preconnectedSpace.mp hC.isPreconnected
  obtain ⟨d,b,hb⟩ := exists_triangular_basis_of_zariskiConnected_solvable ρH a hp hc
  exact ⟨H,hn,hH,d,b,hb⟩

/-- A solvable linear group over an algebraically closed field has a
finite-index subgroup represented faithfully by upper triangular matrices. -/
theorem exists_finiteIndex_faithful_triangular_of_linear [IsAlgClosed K] [IsSolvable G]
    (ρ : G →* (Square K n)ˣ) (hi : Function.Injective ρ) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧ ∃ d : ℕ, ∃ σ : H →* (Square K d)ˣ,
      Function.Injective σ ∧ ∀ g : H, ∀ i j, j < i → (σ g : Square K d) i j = 0 := by
  obtain ⟨H,hn,hH,hC⟩ := exists_finiteIndex_zariskiConnected ρ
  let ρH := ρ.comp H.subtype
  let a := matrixLinearAction ρH
  have hp := matrixLinearAction_coefficients ρH
  have hc : @PreconnectedSpace H (matrixZariskiTopology ρH) := by
    letI := matrixZariskiTopology ρ
    change @PreconnectedSpace H (matrixZariskiTopology (ρ.comp H.subtype))
    rw [matrixZariskiTopology_subgroup]
    exact isPreconnected_iff_preconnectedSpace.mp hC.isPreconnected
  obtain ⟨d,b,hb⟩ := exists_triangular_basis_of_zariskiConnected_solvable ρH a hp hc
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)).symm
  let u := Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv
  let σ := u.toMonoidHom.comp (e.toMonoidHom.comp a)
  have hAi : Function.Injective a := matrixLinearAction_injective ρH (hi.comp H.subtype_injective)
  refine ⟨H,hn,hH,d,σ,u.injective.comp (e.injective.comp hAi),?_⟩
  intro g i j hij
  change LinearMap.toMatrix b b (a g : Module.End K (Fin n → K)) i j = 0
  rw [LinearMap.toMatrix_apply]
  exact hb g i j hij

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.VirtualTriangularization

-- BEGIN COMPLETE MODULE HirschProof.NumberFieldTriangularization
section
                                           
                                                       
                                                         

set_option autoImplicit false

noncomputable section

namespace LocalHirschHyperfinite
open Set

variable {G : Type*} [Group G] {n : ℕ}
local notation "Square" => fun K n => Matrix (Fin n) (Fin n) K

private theorem matrixUnitsMap_injective {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (hf : Function.Injective f) :
    Function.Injective (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom) := by
  intro x y h
  apply Units.ext
  ext i j
  exact hf (congrArg (fun z : (Square L n)ˣ => (z : Square L n) i j) h)

/-- A matrix representation of a finitely generated group over an
algebraic extension can be defined over a finite subextension. -/
theorem matrix_representation_descends {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [Group.FG G] (ρ : G →* (Square L n)ˣ) :
    ∃ E : IntermediateField K L, Module.Finite K E ∧
      ∃ σ : G →* (Square E n)ˣ, (Units.map E.val.toRingHom.mapMatrix.toMonoidHom).comp σ = ρ := by
  classical
  obtain ⟨S,hS⟩ := (Group.FG.out : (⊤ : Subgroup G).FG)
  let A := range (fun t : (↑S : Type _) × Bool × Fin n × Fin n => matrixCoordinates ρ t.1.val t.2)
  let E := IntermediateField.adjoin K A
  letI : Finite A := (Set.finite_range (fun t : (↑S : Type _) × Bool × Fin n × Fin n =>
    matrixCoordinates ρ t.1.val t.2)).to_subtype
  have hE : Module.Finite K E := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral)
  let p : (Square E n) →+* Square L n := E.val.toRingHom.mapMatrix
  have hp : Function.Injective p := by
    intro U V h
    apply Matrix.ext
    intro i j
    exact Subtype.ext (congrArg (fun M : Square L n => M i j) h)
  let q : (Square E n)ˣ →* (Square L n)ˣ := Units.map p.toMonoidHom
  have hq : Function.Injective q := matrixUnitsMap_injective E.val.toRingHom Subtype.val_injective
  have hR : ∀ g : G, ρ g ∈ q.range := by
    intro g
    have ht : (⊤ : Subgroup G) ≤ q.range.comap ρ := by
      rw [← hS]
      apply (Subgroup.closure_le _).mpr
      intro x hx
      change ρ x ∈ q.range
      let c (b : Bool) (i j : Fin n) : E := ⟨matrixCoordinates ρ x (b,i,j),
        IntermediateField.subset_adjoin K A ⟨(⟨x,hx⟩,b,i,j),rfl⟩⟩
      let U : Square E n := fun i j => c false i j
      let V : Square E n := fun i j => c true i j
      have hU : p U = (ρ x : Square L n) := rfl
      have hV : p V = (ρ x⁻¹ : Square L n) := rfl
      have hUV : U*V=1 := by
        apply hp
        rw [map_mul,hU,hV,← Units.val_mul,← map_mul,mul_inv_cancel,map_one,map_one]
        exact Units.val_one
      have hVU : V*U=1 := by
        apply hp
        rw [map_mul,hU,hV,← Units.val_mul,← map_mul,inv_mul_cancel,map_one,map_one]
        exact Units.val_one
      let u : (Square E n)ˣ := ⟨U,V,hUV,hVU⟩
      refine ⟨u,Units.ext ?_⟩
      exact hU
    exact ht (Subgroup.mem_top g)
  let r : G →* q.range := {
    toFun := fun g => ⟨ρ g,hR g⟩
    map_one' := Subtype.ext (map_one ρ)
    map_mul' := fun _ _ => Subtype.ext (map_mul ρ _ _) }
  let σ := (MonoidHom.ofInjective hq).symm.toMonoidHom.comp r
  refine ⟨E,hE,σ,?_⟩
  apply MonoidHom.ext
  intro g
  change q ((MonoidHom.ofInjective hq).symm (r g)) = ρ g
  exact congrArg (fun y : q.range => y.val) ((MonoidHom.ofInjective hq).apply_symm_apply (r g))

/-- The Lie–Kolchin reduction for finitely generated rational linear
solvable groups, with entries in a number field. -/
theorem exists_finiteIndex_faithful_triangular_over_numberField [Group.FG G] [IsSolvable G]
    (ρ : G →* (Square ℚ n)ˣ) (hi : Function.Injective ρ) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ)), Module.Finite ℚ E ∧
      ∃ d : ℕ, ∃ σ : H →* (Square E d)ˣ,
        Function.Injective σ ∧ ∀ g : H, ∀ i j, j < i → (σ g : Square E d) i j = 0 := by
  let K := AlgebraicClosure ℚ
  letI : Algebra.IsAlgebraic ℚ K := AlgebraicClosure.isAlgebraic ℚ
  let f : (Square ℚ n)ˣ →* (Square K n)ˣ := Units.map (algebraMap ℚ K).mapMatrix.toMonoidHom
  have hf : Function.Injective f := matrixUnitsMap_injective _ (algebraMap ℚ K).injective
  obtain ⟨H,hn,hH,d,τ,hτ,hu⟩ :=
    exists_finiteIndex_faithful_triangular_of_linear (f.comp ρ) (hf.comp hi)
  letI := hH
  letI : Group.FG H := H.fg_of_index_ne_zero
  obtain ⟨E,hE,σ,hσ⟩ := matrix_representation_descends (K := ℚ) τ
  have hσ' (g : H) : (Units.map E.val.toRingHom.mapMatrix.toMonoidHom) (σ g) = τ g :=
    DFunLike.congr_fun hσ g
  refine ⟨H,hn,hH,E,hE,d,σ,?_,?_⟩
  · intro g g' e
    apply hτ
    rw [← hσ',← hσ',e]
  · intro g i j hij
    have he := congrArg (fun z : (Square K d)ˣ => (z : Square K d) i j) (hσ' g)
    apply E.val.injective
    exact he.trans (hu g i j hij)

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.NumberFieldTriangularization

-- BEGIN COMPLETE MODULE HirschProof.MatrixLayers
section
                                      

set_option autoImplicit false

namespace LocalHirschHyperfinite

open Matrix
open scoped commutatorElement

namespace MatrixLayers

local notation "Square" => fun K n => Matrix (Fin n) (Fin n) K

variable {G K : Type*} [Group G] [CommRing K] {n : ℕ}
variable (ρ : G →* (Square K n)ˣ)
variable (hu : ∀ g : G, ∀ i j, j < i → (ρ g : Square K n) i j = 0)

abbrev Layer := unitriangularFiltration ρ hu

/-- Coordinates on the `k`-th superdiagonal. -/
abbrev Coordinate (n k : ℕ) := {ij : Fin n × Fin n // ij.2.val = ij.1.val+k}

theorem layer_antitone : Antitone (Layer ρ hu) := by
  intro i j hij g hg a b hab
  exact hg a b (by omega)

theorem layer_zero : Layer ρ hu 0 = ⊤ := by
  apply (Subgroup.eq_top_iff' _).2
  intro g i j hij
  have hji : j < i := hij
  change ((ρ g : Square K n) - 1) i j = 0
  rw [Matrix.sub_apply,hu g _ _ hji,Matrix.one_apply_ne hji.ne',sub_zero]

theorem layer_one (hd : ∀ (g : G) (i : Fin n), (ρ g : Square K n) i i = 1) :
    Layer ρ hu 1 = ⊤ := by
  apply (Subgroup.eq_top_iff' _).2
  intro g i j hij
  change ((ρ g : Square K n) - 1) i j = 0
  by_cases he : i = j
  · subst j
    simp [Matrix.sub_apply,hd]
  · have hj : j < i := by
      have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
      change j.val < i.val
      omega
    rw [Matrix.sub_apply, hu g _ _ hj, Matrix.one_apply_ne he,sub_zero]

theorem layer_last (hρ : Function.Injective ρ) : Layer ρ hu n = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply hρ
  apply Units.ext
  rw [map_one,Units.val_one,← sub_eq_zero]
  ext i j
  exact hg i j (by have := j.isLt; omega)

instance layer_normal (k : ℕ) : (Layer ρ hu k).Normal := by
  constructor
  intro g hg h
  have hh : h ∈ Layer ρ hu 0 := by rw [layer_zero]; exact Subgroup.mem_top h
  have hc := commutator_le_unitriangularFiltration ρ hu 0 k
    (Subgroup.commutator_mem_commutator hh hg)
  rw [Nat.zero_add] at hc
  have hProd := (Layer ρ hu k).mul_mem hc hg
  simpa only [commutatorElement_def,inv_mul_cancel_right] using hProd

/-- Restriction to one superdiagonal is a homomorphism on its filtration layer. -/
def superdiagonal (k : ℕ) (hk : 0 < k) : Layer ρ hu k →* Multiplicative (Coordinate n k → K) where
  toFun g := Multiplicative.ofAdd (fun ij => ((ρ g.val : Square K n)-1) ij.val.1 ij.val.2)
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext ij
    simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    ext ij
    let A : Square K n := ρ g.val
    let B : Square K n := ρ h.val
    have hg : VanishesBefore k (A-1) := g.property
    have hh : VanishesBefore k (B-1) := h.property
    have hij := ij.property
    have hprod := (hg.mul hh) ij.val.1 ij.val.2 (by omega)
    change ((ρ (g.val*h.val) : Square K n)-1) ij.val.1 ij.val.2 =
      (A-1) ij.val.1 ij.val.2 + (B-1) ij.val.1 ij.val.2
    rw [map_mul,Units.val_mul]
    change (A*B-1) ij.val.1 ij.val.2 = _
    rw [show A*B-1 = (A-1)+(B-1)+(A-1)*(B-1) by noncomm_ring]
    simp only [Matrix.add_apply,hprod,add_zero]

theorem superdiagonal_ker (k : ℕ) (hk : 0 < k) :
    (superdiagonal ρ hu k hk).ker = (Layer ρ hu (k+1)).subgroupOf (Layer ρ hu k) := by
  ext g
  constructor
  · intro hg
    change superdiagonal ρ hu k hk g = 1 at hg
    change VanishesBefore (k+1) ((ρ g.val : Square K n)-1)
    intro i j hij
    by_cases hlt : j.val < i.val+k
    · exact g.property i j hlt
    · have he : j.val = i.val+k := by omega
      exact congrFun (congrArg Multiplicative.toAdd hg) ⟨(i,j),he⟩
  · intro hg
    change VanishesBefore (k+1) ((ρ g.val : Square K n)-1) at hg
    change superdiagonal ρ hu k hk g = 1
    apply Multiplicative.toAdd.injective
    ext ij
    exact hg ij.val.1 ij.val.2 (by have := ij.property; omega)

end MatrixLayers
end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.MatrixLayers

-- BEGIN COMPLETE MODULE HirschProof.NilpotentUnipotentExtension
section
                                        
                               
                                         

set_option autoImplicit false
noncomputable section

open Set
open scoped commutatorElement

namespace LocalHirschHyperfinite

section KernelSeries

variable {G Q : Type*} [Group G] [Group Q]

theorem map_lowerCentralSeries_le {n : ℕ} (f : G →* Q) :
    (Subgroup.lowerCentralSeries G n).map f ≤ Subgroup.lowerCentralSeries Q n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    change ⁅Subgroup.lowerCentralSeries G n,(⊤ : Subgroup G)⁆.map f ≤
      ⁅Subgroup.lowerCentralSeries Q n,(⊤ : Subgroup Q)⁆
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono ih le_top

/-- Nilpotence of a quotient lifts through any finite central filtration in
the kernel. -/
theorem isNilpotent_of_kernel_filtration (f : G →* Q) [Group.IsNilpotent Q]
    (A : ℕ → Subgroup G) (k : ℕ) (h₀ : f.ker ≤ A 0) (hEnd : A k = ⊥)
    (hStep : ∀ j, ⁅(⊤ : Subgroup G), A j⁆ ≤ A (j+1)) :
    Group.IsNilpotent G := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent Q)
  have hcG : Subgroup.lowerCentralSeries G c ≤ f.ker := by
    have hmap := map_lowerCentralSeries_le (n := c) f
    rw [hc] at hmap
    exact (Subgroup.map_eq_bot_iff _).mp (bot_unique hmap)
  have hcA (j : ℕ) : Subgroup.lowerCentralSeries G (c+j) ≤ A j := by
    induction j with
    | zero => exact hcG.trans h₀
    | succ j ih =>
      change ⁅Subgroup.lowerCentralSeries G (c+j),(⊤ : Subgroup G)⁆ ≤ A (j+1)
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono le_rfl ih).trans (hStep j)
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  exact ⟨c+k,bot_unique ((hcA k).trans hEnd.le)⟩

end KernelSeries

section UnipotentMatrices

variable {G Q K : Type*} [Group G] [Group Q] [Field K] {m : ℕ}

private theorem upper_unitriangular_mulVec_diff
    (M : Matrix (Fin m) (Fin m) K)
    (hupper : ∀ i j, j < i → M i j = 0)
    (hdiag : ∀ i, M i i = 1)
    {b : ℕ} {v : Fin m → K} (hv : ∀ i, m-b ≤ i.val → v i = 0) (i : Fin m)
    (hi : m-(b+1) ≤ i.val) : M.mulVec v i - v i = 0 := by
  apply sub_eq_zero.mpr
  change (∑ j : Fin m, M i j * v j) = v i
  rw [Finset.sum_eq_single i]
  · rw [hdiag,one_mul]
  · intro j _ hne
    rcases lt_or_gt_of_ne hne with hji|hij
    · rw [hupper i j hji,zero_mul]
    · have hlt : i.val < j.val := hij
      rw [hv j (by omega),mul_zero]
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- An extension of a nilpotent group by an abelian kernel is nilpotent
when conjugation on the kernel embeds in one finite unitriangular action. -/
theorem isNilpotent_of_unitriangular_kernel_action (f : G →* Q) [Group.IsNilpotent Q]
    (z : f.ker →* Multiplicative (Fin m → K)) (hz : Function.Injective z)
    (M : G → Matrix (Fin m) (Fin m) K)
    (hupper : ∀ g i j, j < i → M g i j = 0) (hdiag : ∀ g i, M g i i = 1)
    (hconj : ∀ g : G, ∀ x : f.ker,
      Multiplicative.toAdd (z (⟨g*x.val*g⁻¹,(inferInstance : f.ker.Normal).conj_mem x.val x.property g⟩ : f.ker)) =
        (M g).mulVec (Multiplicative.toAdd (z x))) :
    Group.IsNilpotent G := by
  let W (b : ℕ) : Subgroup f.ker := {
    carrier := {x | ∀ i, m-b ≤ (i : Fin m).val → Multiplicative.toAdd (z x) i = 0}
    one_mem' := by
      intro i _
      rw [map_one]
      rfl
    mul_mem' := by
      intro x y hx hy i hi
      rw [map_mul]
      change Multiplicative.toAdd (z x) i + Multiplicative.toAdd (z y) i = 0
      rw [hx i hi,hy i hi,zero_add]
    inv_mem' := by
      intro x hx i hi
      rw [map_inv]
      change -Multiplicative.toAdd (z x) i = 0
      rw [hx i hi,neg_zero] }
  let A (b : ℕ) := (W b).map f.ker.subtype
  have h₀ : f.ker ≤ A 0 := by
    intro x hx
    refine ⟨⟨x,hx⟩,?_ ,rfl⟩
    intro i hi
    exact (Nat.not_le_of_gt i.isLt (by simpa using hi)).elim
  have hEnd : A m = ⊥ := by
    apply bot_unique
    rintro x ⟨x',hx',rfl⟩
    have he : z x' = z 1 := by
      rw [map_one]
      funext i
      exact hx' i (by omega)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hz he))
  apply isNilpotent_of_kernel_filtration f A m h₀ hEnd
  intro j
  apply Subgroup.commutator_le.mpr
  rintro g _ x ⟨a,ha,rfl⟩
  let c : f.ker := ⟨g*a.val*g⁻¹,(inferInstance : f.ker.Normal).conj_mem a.val a.property g⟩
  refine ⟨c*a⁻¹,?_ ,rfl⟩
  intro i hi
  rw [map_mul,map_inv]
  change Multiplicative.toAdd (z c) i + -(Multiplicative.toAdd (z a) i) = 0
  rw [←sub_eq_add_neg]
  rw [show Multiplicative.toAdd (z c) = (M g).mulVec (Multiplicative.toAdd (z a)) from hconj g a]
  exact upper_unitriangular_mulVec_diff (M g) (hupper g) (hdiag g) ha i hi

end UnipotentMatrices

section Torsion

open MatrixLayers

variable {G K : Type*} [Group G] [Field K] [CharZero K] {n : ℕ}
variable (ρ : G →* (Matrix (Fin n) (Fin n) K)ˣ)
variable (hUpper : ∀ g : G, ∀ i j, j < i → (ρ g : Matrix (Fin n) (Fin n) K) i j = 0)

include hUpper in
theorem unitriangular_eq_one_of_finite_order {g : G}
    (hDiag : ∀ i, (ρ g : Matrix (Fin n) (Fin n) K) i i = 1)
    (hFin : IsOfFinOrder (ρ g)) : ρ g = 1 := by
  obtain ⟨a,ha,he⟩ := hFin.exists_pow_eq_one
  have hL1 : g ∈ Layer ρ hUpper 1 := by
    intro i j h
    change ((ρ g : Matrix (Fin n) (Fin n) K)-1) i j = 0
    by_cases hji : j = i
    · subst j
      simp [hDiag]
    · have hk : j.val < i.val := by
        have hj : j.val ≠ i.val := fun e => hji (Fin.ext e)
        omega
      rw [Matrix.sub_apply,hUpper g i j hk,Matrix.one_apply_ne (Ne.symm hji),sub_zero]
  have hAll (k : ℕ) : g ∈ Layer ρ hUpper (k+1) := by
    induction k with
    | zero => exact hL1
    | succ k ih =>
      let z : Layer ρ hUpper (k+1) := ⟨g,ih⟩
      let s := superdiagonal ρ hUpper (k+1) (Nat.succ_pos _)
      have hp : s z ^ a = 1 := by
        rw [← map_pow]
        apply Multiplicative.toAdd.injective
        ext ij
        change ((ρ (g^a) : Matrix (Fin n) (Fin n) K)-1) ij.val.1 ij.val.2 = 0
        rw [map_pow,he,Units.val_one,sub_self]
        rfl
      have hs : s z = 1 := (pow_left_inj ha.ne').mp (hp.trans (one_pow _).symm)
      have hz : z ∈ s.ker := hs
      rw [superdiagonal_ker] at hz
      exact hz
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hn := hAll n i j (by have := j.isLt; omega)
  exact sub_eq_zero.mp hn

end Torsion

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.NilpotentUnipotentExtension

-- BEGIN COMPLETE MODULE HirschProof.CentralQuotientRadical
section
                                       

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set
open scoped commutatorElement

variable {G Q : Type*} [Group G] [Group Q]

private theorem commutator_eq_of_central_right_factors {a b c d : G}
    (hc : c ∈ Subgroup.center G) (hd : d ∈ Subgroup.center G) :
    ⁅a*c,b*d⁆ = ⁅a,b⁆ := by
  have hc' : ⁅c,b*d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hc (b*d)).symm)
  have hd' : ⁅a,d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp hd a)
  rw [commutatorElement_mul_left_eq_conj_mul,hc',mul_one,mul_inv_cancel,one_mul,
    commutatorElement_mul_right_eq_mul_conj,hd',mul_one,mul_inv_cancel_right]

/-- Schur's theorem in the formulation with a finite-index center. -/
theorem finite_commutator_of_finiteIndex_center [(Subgroup.center G).FiniteIndex] :
    Finite (commutator G) := by
  classical
  let Z := Subgroup.center G
  let q := QuotientGroup.mk' Z
  let σ (a : G ⧸ Z) : G := Classical.choose (QuotientGroup.mk'_surjective Z a)
  have hσ (a : G ⧸ Z) : q (σ a) = a := Classical.choose_spec (QuotientGroup.mk'_surjective Z a)
  have hRep (a : G) : (σ (q a))⁻¹*a ∈ Subgroup.center G := by
    have hv : q ((σ (q a))⁻¹*a) = 1 := by rw [map_mul,map_inv,hσ,inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp hv
  let C (p : (G ⧸ Z) × (G ⧸ Z)) := ⁅σ p.1,σ p.2⁆
  have hC : commutatorSet G ⊆ range C := by
    intro x hx
    obtain ⟨a,b,rfl⟩ := mem_commutatorSet_iff.mp hx
    refine ⟨(q a,q b),?_⟩
    have he := commutator_eq_of_central_right_factors (a := σ (q a)) (b := σ (q b)) (hRep a) (hRep b)
    simpa only [C,mul_inv_cancel_left] using he.symm
  letI : Finite (commutatorSet G) := ((finite_range C).subset hC).to_subtype
  infer_instance

/-- Local finiteness is preserved by directed unions of subgroups. -/
theorem IsLocallyFiniteGroup.directed_iSup {ι : Type*} [Nonempty ι] (D : ι → Subgroup G)
    (hD : Directed (· ≤ ·) D) (h : ∀ i, IsLocallyFiniteGroup (D i)) :
    IsLocallyFiniteGroup (⨆ i, D i : Subgroup G) := by
  classical
  let K := ⨆ i, D i
  intro H hH
  obtain ⟨s,rfl⟩ := hH
  have hMem : ∃ i, ∀ x ∈ s, (x : K).val ∈ D i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨Classical.choice inferInstance,by simp⟩
    | @insert a s hnot ih =>
      obtain ⟨i,hi⟩ := ih
      obtain ⟨j,hj⟩ := (Subgroup.mem_iSup_of_directed hD).mp a.property
      obtain ⟨k,hik,hjk⟩ := hD i j
      refine ⟨k,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact hjk hj
      · exact hik (hi x hx)
  obtain ⟨i,hi⟩ := hMem
  have hsub : Subgroup.closure (s : Set K) ≤ (D i).comap K.subtype :=
    (Subgroup.closure_le _).mpr (fun x hx => hi x hx)
  let f : Subgroup.closure (s : Set K) →* D i := {
    toFun := fun x => ⟨x.val.val,hsub x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y e
    exact Subtype.ext (Subtype.ext (congrArg (fun z : D i => z.val) e))
  letI : Group.FG (Subgroup.closure (s : Set K)) :=
    (Group.fg_iff_subgroup_fg _).mpr ⟨s,rfl⟩
  exact IsLocallyFiniteGroup.finite_of_fg (IsLocallyFiniteGroup.of_injective f hf (h i))

/-- If all finitely generated subgroups have finite commutator subgroup,
the commutator subgroup of the whole group is locally finite. -/
theorem isLocallyFiniteGroup_commutator_of_fg
    (h : ∀ H : Subgroup G, H.FG → Finite (commutator H)) :
    IsLocallyFiniteGroup (commutator G) := by
  let I := {H : Subgroup G // H.FG}
  letI : Nonempty I := ⟨⟨⊥,(Subgroup.fg_iff _).mpr ⟨∅,Subgroup.closure_empty,finite_empty⟩⟩⟩
  let D (H : I) : Subgroup G := ⁅H.val,H.val⁆
  have hD : Directed (· ≤ ·) D := by
    intro A B
    let C : I := ⟨A.val ⊔ B.val,A.property.sup B.property⟩
    exact ⟨C,Subgroup.commutator_mono le_sup_left le_sup_left,
      Subgroup.commutator_mono le_sup_right le_sup_right⟩
  have hDC : (⨆ i, D i) = commutator G := by
    apply le_antisymm
    · exact iSup_le (fun i => Subgroup.commutator_mono le_top le_top)
    · change ⁅(⊤ : Subgroup G),⊤⁆ ≤ _
      apply Subgroup.commutator_le.mpr
      intro a _ b _
      let J := Subgroup.closure ({a,b} : Set G)
      have hJ : J.FG := (Subgroup.fg_iff _).mpr ⟨_,rfl,(finite_singleton b).insert a⟩
      have hab : ⁅a,b⁆ ∈ D ⟨J,hJ⟩ := Subgroup.commutator_mem_commutator
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      exact (Subgroup.mem_iSup_of_directed hD).mpr ⟨⟨J,hJ⟩,hab⟩
  rw [← hDC]
  apply IsLocallyFiniteGroup.directed_iSup D hD
  intro i
  change IsLocallyFiniteGroup (⁅i.val,i.val⁆ : Subgroup G)
  rw [← Subgroup.map_subtype_commutator]
  letI : Finite (commutator i.val) := h i.val i.property
  exact IsLocallyFiniteGroup.image _ IsLocallyFiniteGroup.of_finite i.val.subtype

/-- A central extension of a locally finite group has locally finite
commutator subgroup. -/
theorem IsLocallyFiniteGroup.commutator_of_central_kernel (f : G →* Q)
    (hc : f.ker ≤ Subgroup.center G) (hQ : IsLocallyFiniteGroup Q) :
    IsLocallyFiniteGroup (commutator G) := by
  apply isLocallyFiniteGroup_commutator_of_fg
  intro H hH
  let p := f.comp H.subtype
  have hpr : p.range = H.map f := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  letI : Finite p.range := hpr.symm ▸ hQ _ (IsLocallyFiniteGroup.fg_map f H hH)
  letI : p.ker.FiniteIndex := Subgroup.finiteIndex_ker p
  have hK : p.ker ≤ Subgroup.center H := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hx' : x.val ∈ f.ker := hx
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hc hx') y.val)
  letI : (Subgroup.center H).FiniteIndex := Subgroup.finiteIndex_of_le hK
  exact finite_commutator_of_finiteIndex_center

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.CentralQuotientRadical

-- BEGIN COMPLETE MODULE HirschProof.NormalAbelianConjugation
section
                                       
                                               
                                              
                                         

set_option autoImplicit false
noncomputable section

open Set TensorProduct Matrix

namespace LocalHirschHyperfinite

variable {G : Type*} [Group G]

/-- Conjugation restricts to an automorphism of a normal subgroup. -/
def normalSubgroupConjugation (A : Subgroup G) [hA : A.Normal] : G →* MulAut A where
  toFun g := {
    toFun := fun a => ⟨g*a.val*g⁻¹,hA.conj_mem a.val a.property g⟩
    invFun := fun a => ⟨g⁻¹*a.val*g,by simpa only [inv_inv] using hA.conj_mem a.val a.property g⁻¹⟩
    left_inv := fun a => Subtype.ext (by simp [mul_assoc])
    right_inv := fun a => Subtype.ext (by simp [mul_assoc])
    map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext a; simp
  map_mul' := by
    intro g h
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change (g*h)*a.val*(g*h)⁻¹ = g*(h*a.val*h⁻¹)*g⁻¹
    group

@[simp]
theorem normalSubgroupConjugation_val (A : Subgroup G) [A.Normal] (g : G) (a : A) :
    (normalSubgroupConjugation A g a).val = g*a.val*g⁻¹ := rfl

section Abelian

/-- Equip a commutative subgroup with a commutative group structure extending
its canonical subgroup operations. -/
abbrev commGroupOfAbelianSubgroup (A : Subgroup G) [IsMulCommutative A] : CommGroup A :=
  { (inferInstance : Group A) with mul_comm := mul_comm' }

attribute [local instance] commGroupOfAbelianSubgroup

variable (A : Subgroup G) [A.Normal] [IsMulCommutative A]

private def abelianConjLinear (g : G) : Additive A →ₗ[ℤ] Additive A :=
  (normalSubgroupConjugation A g).toMonoidHom.toAdditive.toIntLinearMap

private theorem abelianConjLinear_one : abelianConjLinear A 1 = LinearMap.id := by
  unfold abelianConjLinear
  rw [map_one]
  rfl

private theorem abelianConjLinear_mul (g h : G) :
    abelianConjLinear A (g*h) = (abelianConjLinear A g).comp (abelianConjLinear A h) := by
  unfold abelianConjLinear
  rw [map_mul]
  rfl

private def abelianRationalAction : G →* Module.End ℚ (ℚ ⊗[ℤ] Additive A) where
  toFun g := (abelianConjLinear A g).baseChange ℚ
  map_one' := by
    change (abelianConjLinear A 1).baseChange ℚ = 1
    rw [abelianConjLinear_one,LinearMap.baseChange_id]
    rfl
  map_mul' g h := by
    change (abelianConjLinear A (g*h)).baseChange ℚ = _
    rw [abelianConjLinear_mul,LinearMap.baseChange_comp]
    rfl

omit [A.Normal] in
private theorem rationalization_one_injective [IsMulTorsionFree A] :
    Function.Injective (TensorProduct.mk ℤ ℚ (Additive A) 1) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [eq_bot_iff]
  intro x hx
  have ht : (1 : ℚ) ⊗ₜ[ℤ] x = 0 := hx
  obtain ⟨n,hn,hx'⟩ := (rationalization_eq_zero_iff x).mp ht
  have hpow : (Additive.toMul x : A)^n = 1 := hx'
  have hz : (Additive.toMul x : A) = 1 :=
    (pow_left_inj hn.ne').mp (hpow.trans (one_pow n).symm)
  simpa only [Submodule.mem_bot] using hz

/-- A matrix action retaining an equivariant faithful representation of a
normal abelian group as additive vectors. -/
structure AbelianConjugationChart (A : Subgroup G) [A.Normal] {H : Type*} [Group H] (emb : H →* G)
    (K : Type*) [Field K] where
  dim : ℕ
  matrix : H →* (Matrix (Fin dim) (Fin dim) K)ˣ
  coord : A →* Multiplicative (Fin dim → K)
  injective_coord : Function.Injective coord
  realizes : ∀ (g : H) (a : A),
    Multiplicative.toAdd (coord (normalSubgroupConjugation A (emb g) a)) =
      (matrix g).val.mulVec (Multiplicative.toAdd (coord a))
  reflects_trivial : ∀ g : H, (∀ a : A, normalSubgroupConjugation A (emb g) a = a) → matrix g = 1

/-- Rationalize conjugation on a normal torsion-free abelian subgroup of
finite rational rank, and extend scalars to any field over the rationals. -/
def abelianConjugationChart [IsMulTorsionFree A]
    [Module.Finite ℚ (ℚ ⊗[ℤ] Additive A)] (K : Type*) [Field K] [Algebra ℚ K] :
    AbelianConjugationChart A (MonoidHom.id G) K := by
  let V := ℚ ⊗[ℤ] Additive A
  let n := Module.finrank ℚ V
  let B := Module.finBasis ℚ V
  let t := TensorProduct.mk ℤ ℚ (Additive A) 1
  let β := (B.equivFun.toLinearMap.restrictScalars ℤ).comp t
  let z : A →* Multiplicative (Fin n → ℚ) := β.toAddMonoidHom.toMultiplicative
  let f := algebraMap ℚ K
  let f' : Multiplicative (Fin n → ℚ) →* Multiplicative (Fin n → K) := {
    toFun := fun x => Multiplicative.ofAdd (fun i => f (x i))
    map_one' := by funext i; exact f.map_zero
    map_mul' := by intro x y; funext i; exact f.map_add (x i) (y i) }
  let σ := ((LinearMap.toMatrixAlgEquiv B).toMonoidHom.comp (abelianRationalAction A)).toHomUnits
  let σ' := (Units.map f.mapMatrix.toMonoidHom).comp σ
  have hz : Function.Injective z := B.equivFun.injective.comp (rationalization_one_injective A)
  have hf' : Function.Injective f' := by
    intro a b he
    funext i
    exact f.injective (congrFun he i)
  refine ⟨n,σ',f'.comp z,hf'.comp hz,?_,?_⟩
  · intro g a
    have hcoords : (σ g).val.mulVec (B.equivFun (t (Additive.ofMul a))) =
        B.equivFun (t (Additive.ofMul (normalSubgroupConjugation A g a))) := by
      change (LinearMap.toMatrix B B (abelianRationalAction A g)).mulVec
          (fun i => B.repr (t (Additive.ofMul a)) i) =
        fun i => B.repr (t (Additive.ofMul (normalSubgroupConjugation A g a))) i
      rw [LinearMap.toMatrix_mulVec_repr]
      congr 2
    funext i
    change f (B.equivFun (t (Additive.ofMul (normalSubgroupConjugation A g a))) i) =
      (((σ g).val.map f).mulVec (f ∘ B.equivFun (t (Additive.ofMul a)))) i
    rw [← congrFun hcoords i]
    exact f.map_mulVec _ _ _
  · intro g hg
    have he : abelianConjLinear A g = LinearMap.id := by
      ext a
      exact congrArg Subtype.val (hg a)
    apply Units.ext
    change (f.mapMatrix (LinearMap.toMatrix B B (abelianRationalAction A g))) = 1
    change f.mapMatrix (LinearMap.toMatrix B B ((abelianConjLinear A g).baseChange ℚ)) = 1
    rw [he,LinearMap.baseChange_id,LinearMap.toMatrix_id,map_one]

end Abelian

section TriangularChart

variable {A : Subgroup G} [A.Normal] {K : Type*} [Field K]

/-- The matrix being the identity forces conjugation to act pointwise trivially. -/
theorem AbelianConjugationChart.fixes_of_matrix_eq_one {H : Type*} [Group H]
    {emb : H →* G} (T : AbelianConjugationChart A emb K)
    {g : H} (hg : T.matrix g = 1) (a : A) :
    normalSubgroupConjugation A (emb g) a = a := by
  apply T.injective_coord
  apply Multiplicative.toAdd.injective
  rw [T.realizes,hg,Units.val_one,one_mulVec]

/-- A finite-index subgroup has an upper triangular, equivariant chart. -/
theorem exists_triangular_abelianConjugationChart [IsAlgClosed K] [IsSolvable G]
    (R : AbelianConjugationChart A (MonoidHom.id G) K) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∃ T : AbelianConjugationChart A H.subtype K,
      ∀ g : H, ∀ i j, j < i → (T.matrix g).val i j = 0 := by
  obtain ⟨H,_,hH,d,B,hB⟩ := exists_finiteIndex_triangular_basis_of_matrix R.matrix
  let V := Fin R.dim → K
  let f : (Matrix (Fin R.dim) (Fin R.dim) K)ˣ →* (Module.End K V)ˣ :=
    Units.map Matrix.toLinAlgEquiv'.toMonoidHom
  let q : (Module.End K V)ˣ →* (Matrix (Fin d) (Fin d) K)ˣ :=
    Units.map (LinearMap.toMatrixAlgEquiv B).toMonoidHom
  let σ := q.comp (f.comp (R.matrix.comp H.subtype))
  let z := B.equivFun.toLinearMap.toAddMonoidHom.toMultiplicative.comp R.coord
  refine ⟨H,hH,⟨d,σ,z,B.equivFun.injective.comp R.injective_coord,?_,?_⟩,?_⟩
  · intro g a
    change B.equivFun (Multiplicative.toAdd (R.coord (normalSubgroupConjugation A g.val a))) =
      (LinearMap.toMatrix B B (Matrix.toLin' (R.matrix g.val).val)).mulVec
        (B.equivFun (Multiplicative.toAdd (R.coord a)))
    rw [show Multiplicative.toAdd (R.coord (normalSubgroupConjugation A g.val a)) =
        (R.matrix g.val).val.mulVec (Multiplicative.toAdd (R.coord a)) from R.realizes g.val a]
    exact (LinearMap.toMatrix_mulVec_repr B B (Matrix.toLin' (R.matrix g.val).val)
      (Multiplicative.toAdd (R.coord a))).symm
  · intro g hg
    change q (f (R.matrix g.val)) = 1
    rw [R.reflects_trivial g.val hg,map_one,map_one]
  · intro g i j hij
    change LinearMap.toMatrix B B (Matrix.toLin' (R.matrix g.val).val) i j = 0
    rw [LinearMap.toMatrix_apply]
    exact hB g i j hij


theorem finiteIndex_map_subtype_of_finiteIndices (H : Subgroup G) [H.FiniteIndex]
    (J : Subgroup H) [J.FiniteIndex] : (J.map H.subtype).FiniteIndex := by
  apply Subgroup.finiteIndex_iff.mpr
  rw [Subgroup.index_map_subtype J]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := J))
    (Subgroup.FiniteIndex.index_ne_zero (H := H))

/-- The diagonal coordinates of the triangular conjugation chart can be
recorded by a lattice quotient after one more finite-index restriction. -/
theorem exists_freeDiagonal_abelianConjugationChart [Group.FG G] [IsAlgClosed K] [IsSolvable G]
    (R : AbelianConjugationChart A (MonoidHom.id G) K) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∃ T : AbelianConjugationChart A H.subtype K,
      (∀ g : H, ∀ i j, j < i → (T.matrix g).val i j = 0) ∧
      ∃ d : ℕ, ∃ p : H →* (Fin d → Multiplicative ℤ),
        Function.Surjective p ∧ ∀ g : H, p g = 1 ↔ ∀ i, (T.matrix g).val i i = 1 := by
  obtain ⟨H,hH,T,hUp⟩ := exists_triangular_abelianConjugationChart R
  letI := hH
  letI : Group.FG H := H.fg_of_index_ne_zero
  obtain ⟨J,hJ,d,p,hp,hDiag⟩ := exists_finiteIndex_diagonal_quotient T.matrix hUp
  letI := hJ
  let J' := J.map H.subtype
  let e := J.equivMapOfInjective H.subtype H.subtype_injective
  let f := J.subtype.comp e.symm.toMonoidHom
  have hf (x : J') : (f x).val = x.val := by
    exact congrArg (fun y : J' => y.val) (e.apply_symm_apply x)
  let T' : AbelianConjugationChart A J'.subtype K :=
    ⟨T.dim,T.matrix.comp f,T.coord,T.injective_coord,
      fun x a => by
        change Multiplicative.toAdd (T.coord (normalSubgroupConjugation A x.val a)) = _
        rw [←hf x]
        exact T.realizes (f x) a,
      fun x hx => by
        apply T.reflects_trivial (f x)
        intro a
        change normalSubgroupConjugation A (f x).val a = a
        rw [hf x]
        exact hx a⟩
  have he (g : J') : T'.matrix g = T.matrix (f g) := rfl
  refine ⟨J',finiteIndex_map_subtype_of_finiteIndices H J,T',?_,d,
    p.comp e.symm.toMonoidHom,hp.comp e.symm.surjective,?_⟩
  · intro g i j hij
    rw [he]
    exact hUp (f g) i j hij
  · intro g
    simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,he]
    exact hDiag (e.symm g)

end TriangularChart

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.NormalAbelianConjugation

-- BEGIN COMPLETE MODULE HirschProof.RadicalAbelianReduction
section
                                           

set_option autoImplicit false
noncomputable section

open Set TensorProduct Matrix

namespace LocalHirschHyperfinite

variable {G Q : Type*} [Group G] [Group Q]

attribute [local instance] commGroupOfAbelianSubgroup

theorem isOfFinOrder_of_locallyFinite (h : IsLocallyFiniteGroup G) (g : G) :
    IsOfFinOrder g := by
  let A := Subgroup.closure ({g} : Set G)
  have hA : A.FG := (Subgroup.fg_iff _).mpr ⟨_,rfl,Set.finite_singleton g⟩
  letI : Finite A := h A hA
  let a : A := ⟨g,Subgroup.subset_closure (Set.mem_singleton g)⟩
  obtain ⟨n,hn,he⟩ := (isOfFinOrder_of_finite a).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg Subtype.val he⟩

private theorem conjugation_trivial_of_mem_abelian (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    {g : G} (hg : g ∈ A) (a : A) : normalSubgroupConjugation A g a = a := by
  apply Subtype.ext
  have h : g*a.val = a.val*g := congrArg Subtype.val (mul_comm' (⟨g,hg⟩ : A) a)
  change g*a.val*g⁻¹ = a.val
  rw [h,mul_inv_cancel_right]

/-- Every abelian normal subgroup of a group with trivial locally finite
radical is torsion-free. -/
theorem isMulTorsionFree_of_normal_abelian_radical_free (A : Subgroup G) [A.Normal]
    [IsMulCommutative A] (hG : locallyFiniteRadical G = ⊥) : IsMulTorsionFree A := by
  let T := CommGroup.torsion A
  let L := T.map A.subtype
  have hLn : L.Normal := by
    constructor
    rintro _ ⟨a,ha,rfl⟩ g
    let b := normalSubgroupConjugation A g a
    have hT : b ∈ T := by
      obtain ⟨n,hn,he⟩ := ((CommGroup.mem_torsion A a).mp ha).exists_pow_eq_one
      apply (CommGroup.mem_torsion A b).mpr
      apply isOfFinOrder_iff_pow_eq_one.mpr
      exact ⟨n,hn,by
        change (normalSubgroupConjugation A g a)^n = 1
        rw [← map_pow,he,map_one]⟩
    exact ⟨b,hT,rfl⟩
  have hT : IsLocallyFiniteGroup T := by
    apply locallyFinite_of_torsion_solvable
    intro a
    obtain ⟨n,hn,ha⟩ := ((CommGroup.mem_torsion A a.val).mp a.property).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,Subtype.ext ha⟩
  have hL : IsLocallyFiniteGroup L := IsLocallyFiniteGroup.image T hT A.subtype
  have hle := (le_locallyFiniteRadical G hLn hL).trans hG.le
  apply IsMulTorsionFree.of_not_isOfFinOrder
  intro a hne ha
  have hmem : a.val ∈ L := ⟨a,(CommGroup.mem_torsion A a).mpr ha,rfl⟩
  exact hne (Subtype.ext (Subgroup.mem_bot.mp (hle hmem)))

set_option maxHeartbeats 1000000 in
/-- After a normal finite-index restriction, elements with a positive power in
a normal torsion-free abelian group centralize that group. -/
theorem exists_normal_finiteIndex_centralizes_roots_of_abelian
    [Group.FG G] [IsSolvable G] (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    [IsMulTorsionFree A] [Module.Finite ℚ (ℚ ⊗[ℤ] Additive A)] :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∀ g ∈ H, (∃ n : ℕ, 0 < n ∧ g^n ∈ A) →
        ∀ a : A, normalSubgroupConjugation A g a = a := by
  let K := AlgebraicClosure ℚ
  let R := abelianConjugationChart A K
  obtain ⟨H,hH,T,hUp⟩ := exists_triangular_abelianConjugationChart R
  letI := hH
  letI : Group.FG H := H.fg_of_index_ne_zero
  obtain ⟨J,hJ,d,p,_,hp⟩ := exists_finiteIndex_diagonal_quotient T.matrix hUp
  letI := hJ
  let J' := J.map H.subtype
  letI : J'.FiniteIndex := finiteIndex_map_subtype_of_finiteIndices H J
  let C := J'.normalCore
  have hC : C ≤ J' := J'.normalCore_le
  refine ⟨C,Subgroup.normalCore_normal J',inferInstance,?_⟩
  intro g hg ⟨n,hn,hpow⟩ a
  let e := J.equivMapOfInjective H.subtype H.subtype_injective
  let w : J := e.symm ⟨g,hC hg⟩
  have hw : w.val.val = g := congrArg (fun x : J' => x.val) (e.apply_symm_apply ⟨g,hC hg⟩)
  have hpow' : (w.val^n).val ∈ A := by
    change w.val.val^n ∈ A
    rwa [hw]
  have hid : T.matrix (w.val^n) = 1 := T.reflects_trivial _ (conjugation_trivial_of_mem_abelian A hpow')
  have hFin : IsOfFinOrder (T.matrix w.val) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,(map_pow T.matrix w.val n).symm.trans hid⟩
  have hp' : p (w^n) = 1 := (hp (w^n)).mpr (fun i => by
    change (T.matrix (w.val^n)).val i i = 1
    rw [hid,Units.val_one,Matrix.one_apply_eq])
  have hpw : p w = 1 := (pow_left_inj hn.ne').mp
    (((map_pow p w n).symm.trans hp').trans (one_pow n).symm)
  have hOne := unitriangular_eq_one_of_finite_order T.matrix hUp ((hp w).mp hpw) hFin
  exact hw ▸ T.fixes_of_matrix_eq_one hOne a

/-- Promoting an abelian normal subgroup through a locally finite quotient
again gives an abelian normal subgroup after a normal finite-index restriction. -/
theorem exists_abelian_kernel_after_quotient_radical
    [Group.FG G] (hHirsch : IsSolvableFiniteHirsch G)
    (hG : locallyFiniteRadical G = ⊥)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      IsMulCommutative ((locallyFiniteRadical (G ⧸ A)).comap (QuotientGroup.mk' A) ⊓ H : Subgroup G) := by
  letI : IsSolvable G := hHirsch.1
  letI : IsMulTorsionFree A := isMulTorsionFree_of_normal_abelian_radical_free A hG
  letI : Module.Finite ℚ (ℚ ⊗[ℤ] Additive A) :=
    finite_rationalization_of_solvableFiniteHirsch hHirsch A (MonoidHom.id A) Function.surjective_id
  obtain ⟨H,hHn,hHi,hCentral⟩ := exists_normal_finiteIndex_centralizes_roots_of_abelian A
  letI := hHn
  let q := QuotientGroup.mk' A
  let R := locallyFiniteRadical (G ⧸ A)
  let C := R.comap q ⊓ H
  let p : C →* R := {
    toFun := fun c => ⟨q c.val,c.property.1⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun c d => Subtype.ext (map_mul q _ _) }
  have hKer : p.ker ≤ Subgroup.center C := by
    intro x hx
    have hxA : x.val ∈ A := (QuotientGroup.eq_one_iff _).mp
      (congrArg (fun a : R => a.val) (show p x = 1 from hx))
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hFin : IsOfFinOrder (p y) := isOfFinOrder_of_locallyFinite
      (locallyFiniteRadical_locallyFinite (G ⧸ A)) (p y)
    obtain ⟨n,hn,hpow⟩ := hFin.exists_pow_eq_one
    have hy : y.val^n ∈ A := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (y.val^n) = 1
      rw [map_pow]
      exact congrArg (fun a : R => a.val) hpow
    have he := congrArg (fun a : A => a.val) (hCentral y.val y.property.2 ⟨n,hn,hy⟩ ⟨x.val,hxA⟩)
    apply Subtype.ext
    simpa only [normalSubgroupConjugation_val,mul_assoc,inv_mul_cancel,mul_one] using
      congrArg (fun g : G => g*y.val) he
  have hLF : IsLocallyFiniteGroup (commutator C) :=
    IsLocallyFiniteGroup.commutator_of_central_kernel p hKer (locallyFiniteRadical_locallyFinite _)
  let D := (commutator C).map C.subtype
  have hDn : D.Normal := by
    change ((commutator C).map C.subtype).Normal
    rw [Subgroup.map_subtype_commutator]
    infer_instance
  have hD := IsLocallyFiniteGroup.image (commutator C) hLF C.subtype
  have hle := (le_locallyFiniteRadical G hDn hD).trans hG.le
  have hC : commutator C = ⊥ := by
    apply bot_unique
    intro x hx
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp (hle ⟨x,hx,rfl⟩)))
  exact ⟨H,hHn,hHi,(commutator_eq_bot_iff C).mp hC⟩

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.RadicalAbelianReduction

-- BEGIN COMPLETE MODULE HirschProof.VirtuallyNilpotentLattice
section
                                          

set_option autoImplicit false
noncomputable section

open Set TensorProduct Matrix

namespace LocalHirschHyperfinite

attribute [local instance] commGroupOfAbelianSubgroup

variable {G Q : Type*} [Group G] [Group Q]

/-- A finite-index subgroup admits a free abelian quotient with nilpotent kernel. -/
def HasVirtuallyNilpotentLatticeQuotient (G : Type*) [Group G] : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ ∃ d : ℕ, ∃ p : H →* (Fin d → Multiplicative ℤ),
    Function.Surjective p ∧ Group.IsNilpotent p.ker

theorem isNilpotent_of_injective_hom (p : G →* Q) (hp : Function.Injective p)
    [Group.IsNilpotent Q] : Group.IsNilpotent G := by
  obtain ⟨n,hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent Q)
  have h := map_lowerCentralSeries_le (n := n) p
  rw [hn] at h
  have hl := (Subgroup.map_eq_bot_iff _).mp (bot_unique h)
  rw [p.ker_eq_bot_iff.mpr hp] at hl
  exact Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨n,bot_unique hl⟩

theorem finiteIndex_comap_of_finiteIndex (A : Subgroup Q) [A.FiniteIndex] (p : G →* Q) :
    (A.comap p).FiniteIndex := by
  apply Subgroup.finiteIndex_iff.mpr
  have h : A.relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  have he := Subgroup.relIndex_comap_ne_zero p h
  simpa only [Subgroup.comap_top,Subgroup.relIndex_top_right] using he

/-- Finite-index subgroup representations lift through another finite-index
inclusion by transporting their actual lattice maps. -/
theorem HasVirtuallyNilpotentLatticeQuotient.of_finiteIndex
    (A : Subgroup G) [A.FiniteIndex] (h : HasVirtuallyNilpotentLatticeQuotient A) :
    HasVirtuallyNilpotentLatticeQuotient G := by
  obtain ⟨B,hB,d,p,hp,hNil⟩ := h
  letI := hB
  letI := hNil
  let B' := B.map A.subtype
  let e := B.equivMapOfInjective A.subtype A.subtype_injective
  let q := p.comp e.symm.toMonoidHom
  have hq : Function.Surjective q := hp.comp e.symm.surjective
  let f : q.ker →* p.ker :=
    (e.symm.toMonoidHom.comp q.ker.subtype).codRestrict p.ker fun x => x.property
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val he))
  exact ⟨B',finiteIndex_map_subtype_of_finiteIndices A B,d,q,hq,isNilpotent_of_injective_hom f hf⟩

set_option maxHeartbeats 1000000 in
/-- A torsion-free abelian kernel of finite rational rank can be added to a
nilpotent-by-lattice group after finite-index restriction. -/
theorem HasVirtuallyNilpotentLatticeQuotient.of_abelian_kernel [Group.FG G] [IsSolvable G]
    (f : G →* Q) [IsMulCommutative f.ker] [IsMulTorsionFree f.ker]
    [Module.Finite ℚ (ℚ ⊗[ℤ] Additive f.ker)]
    {m : ℕ} (p : Q →* (Fin m → Multiplicative ℤ)) [Group.IsNilpotent p.ker] :
    HasVirtuallyNilpotentLatticeQuotient G := by
  let K := AlgebraicClosure ℚ
  let A := f.ker
  let C := abelianConjugationChart A K
  obtain ⟨H,hH,T,hU,d,q,_,hDiag⟩ := exists_freeDiagonal_abelianConjugationChart C
  letI := hH
  letI : Group.FG H := H.fg_of_index_ne_zero
  let fH := f.comp H.subtype
  let r := (p.comp fH).prod q
  let N := r.ker
  let fN : N →* p.ker :=
    (fH.comp N.subtype).codRestrict p.ker fun g => congrArg Prod.fst (show r g.val = 1 from g.property)
  let j : fN.ker →* A :=
    (H.subtype.comp (N.subtype.comp fN.ker.subtype)).codRestrict A (fun a =>
      congrArg Subtype.val (show fN a.val = 1 from a.property))
  have hj : Function.Injective j := by
    intro a b he
    have he' : a.val.val.val = b.val.val.val := congrArg (fun x : A => x.val) he
    exact Subtype.ext (Subtype.ext (Subtype.ext he'))
  let z := T.coord.comp j
  have hN : Group.IsNilpotent N := by
    apply isNilpotent_of_unitriangular_kernel_action fN z (T.injective_coord.comp hj)
      (fun g => (T.matrix g.val).val)
    · exact fun g i j => hU g.val i j
    · intro g
      apply (hDiag g.val).mp
      exact congrArg Prod.snd (show r g.val = 1 from g.property)
    · intro g a
      have he := T.realizes g.val (j a)
      exact he
  letI := hN
  obtain ⟨J,hJ,e,t,ht,hKer⟩ := exists_finiteIndex_freeAbelianImage r
  have hJKer : Group.IsNilpotent t.ker := by
    let u : t.ker →* N :=
      (J.subtype.comp t.ker.subtype).codRestrict N fun a => by
        exact (SetLike.ext_iff.mp hKer a.val).mp a.property
    apply isNilpotent_of_injective_hom u
    intro a b h
    have he : a.val.val = b.val.val := congrArg (fun x : N => x.val) h
    exact Subtype.ext (Subtype.ext he)
  exact HasVirtuallyNilpotentLatticeQuotient.of_finiteIndex H ⟨J,hJ,e,t,ht,hJKer⟩


section SolvableInduction

universe u

private theorem isMulCommutative_last_derived {G : Type u} [Group G] {n : ℕ}
    (hn : derivedSeries G (n+1) = ⊥) :
    IsMulCommutative (derivedSeries G n) := by
  let A := derivedSeries G n
  have he : (commutator A).map A.subtype = ⊥ := by
    rw [Subgroup.map_subtype_commutator]
    exact hn
  have hl := (Subgroup.map_eq_bot_iff _).mp he
  rw [A.subtype.ker_eq_bot_iff.mpr A.subtype_injective] at hl
  exact (commutator_eq_bot_iff A).mp (bot_unique hl)

private theorem virtually_lattice_of_subsingleton {G : Type u} [Group G] [Subsingleton G] :
    HasVirtuallyNilpotentLatticeQuotient G := by
  let p : (⊤ : Subgroup G) →* (Fin 0 → Multiplicative ℤ) := 1
  refine ⟨⊤,inferInstance,0,p,fun y => ⟨1,Subsingleton.elim _ y⟩,?_⟩
  apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
  exact ⟨0,Subsingleton.elim _ _⟩

set_option maxHeartbeats 1600000 in
/-- A finitely generated solvable finite-Hirsch group with trivial locally
finite radical is virtually nilpotent-by-free-abelian. -/
theorem virtuallyNilpotentLatticeQuotient_of_finiteHirsch_radicalFree {G : Type u} [Group G]
    [Group.FG G] (hHirsch : IsSolvableFiniteHirsch G) (hRad : locallyFiniteRadical G = ⊥) :
    HasVirtuallyNilpotentLatticeQuotient G := by
  have main (n : ℕ) : ∀ (U : Type u) [Group U] [Group.FG U],
      IsSolvableFiniteHirsch U → locallyFiniteRadical U = ⊥ →
      derivedSeries U n = ⊥ → HasVirtuallyNilpotentLatticeQuotient U := by
    induction n with
    | zero =>
      intro U _ _ _ _ hn
      have ht : (⊤ : Subgroup U) = ⊥ := hn
      letI : Subsingleton U := ⟨fun a b => by
        have ha := Subgroup.mem_bot.mp (ht ▸ Subgroup.mem_top a)
        have hb := Subgroup.mem_bot.mp (ht ▸ Subgroup.mem_top b)
        exact ha.trans hb.symm⟩
      exact virtually_lattice_of_subsingleton
    | succ n ih =>
      intro U _ _ hfinite hr hn
      let A := derivedSeries U n
      letI : IsMulCommutative A := isMulCommutative_last_derived hn
      let qA := QuotientGroup.mk' A
      let R := locallyFiniteRadical (U ⧸ A)
      let Q' := (U ⧸ A) ⧸ R
      let q : U →* Q' := (QuotientGroup.mk' R).comp qA
      have hq : Function.Surjective q :=
        (QuotientGroup.mk'_surjective R).comp (QuotientGroup.mk'_surjective A)
      letI : Group.FG Q' := Group.fg_of_surjective hq
      have hQfinite := hfinite.of_surjective q hq
      have hQrad : locallyFiniteRadical Q' = ⊥ :=
        normal_locallyFinite_in_radical_quotient_eq_bot (U ⧸ A) _ inferInstance
          (locallyFiniteRadical_locallyFinite Q')
      have hQlen : derivedSeries Q' n = ⊥ := by
        rw [← map_derivedSeries_eq hq n]
        apply (Subgroup.map_eq_bot_iff _).mpr
        intro x hx
        change q x = 1
        have h : qA x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
        simp only [q,MonoidHom.comp_apply,h,map_one]
      obtain ⟨H₀,hH₀n,hH₀i,hComm⟩ := exists_abelian_kernel_after_quotient_radical hfinite hr A
      obtain ⟨P,hPi,m,p,_,hpn⟩ := ih Q' hQfinite hQrad hQlen
      letI := hH₀n
      letI := hH₀i
      letI := hPi
      letI := hpn
      let C := R.comap qA ⊓ H₀
      letI : IsMulCommutative C := hComm
      letI : IsMulTorsionFree C := isMulTorsionFree_of_normal_abelian_radical_free C hr
      let H := H₀ ⊓ P.comap q
      letI : (P.comap q).FiniteIndex := finiteIndex_comap_of_finiteIndex P q
      letI : H.FiniteIndex := inferInstanceAs ((H₀ ⊓ P.comap q).FiniteIndex)
      letI : Group.FG H := H.fg_of_index_ne_zero
      let h := (q.comp H.subtype).codRestrict P fun g => g.property.2
      have hHC (g : h.ker) : g.val.val ∈ C := by
        refine ⟨?_,g.val.property.1⟩
        have he : q g.val.val = 1 := congrArg (fun a : P => a.val) (show h g.val = 1 from g.property)
        exact (QuotientGroup.eq_one_iff (qA g.val.val)).mp he
      let a : h.ker →* C := (H.subtype.comp h.ker.subtype).codRestrict C hHC
      have ha : Function.Injective a := by
        intro x y he
        have e : x.val.val = y.val.val := congrArg (fun z : C => z.val) he
        exact Subtype.ext (Subtype.ext e)
      letI : IsMulCommutative h.ker := IsMulCommutative.of_comm fun x y => ha (by
        rw [map_mul,map_mul,mul_comm' (a x) (a y)])
      letI : IsMulTorsionFree h.ker := ⟨fun {k} hk x y hxy => ha ((pow_left_inj hk).mp (by
        have he : x^k = y^k := hxy
        simpa only [map_pow] using congrArg (fun z => a z) he))⟩
      have hHfinite := hfinite.subgroup H
      letI : IsSolvable H := hHfinite.1
      letI : Module.Finite ℚ (ℚ ⊗[ℤ] Additive h.ker) :=
        finite_rationalization_of_solvableFiniteHirsch hHfinite h.ker (MonoidHom.id _) Function.surjective_id
      exact HasVirtuallyNilpotentLatticeQuotient.of_finiteIndex H
        (HasVirtuallyNilpotentLatticeQuotient.of_abelian_kernel h p)
  letI : IsSolvable G := hHirsch.1
  obtain ⟨n,hn⟩ := IsSolvable.solvable (G := G)
  exact main n G hHirsch hRad hn

/-- The locally finite radical quotient of a finitely generated solvable
group of finite Hirsch length has the virtual nilpotent lattice model. -/
theorem virtuallyNilpotentLatticeQuotient_radicalQuotient {G : Type u} [Group G] [Group.FG G]
    (hHirsch : IsSolvableFiniteHirsch G) :
    HasVirtuallyNilpotentLatticeQuotient (G ⧸ locallyFiniteRadical G) := by
  let R := locallyFiniteRadical G
  let q := QuotientGroup.mk' R
  have hQ := hHirsch.of_surjective q (QuotientGroup.mk'_surjective R)
  exact virtuallyNilpotentLatticeQuotient_of_finiteHirsch_radicalFree hQ
    (normal_locallyFinite_in_radical_quotient_eq_bot G _ inferInstance
      (locallyFiniteRadical_locallyFinite _))


/-- Equivalent notation with a single multiplicative tag on the integer lattice. -/
theorem exists_nilpotent_lattice_quotient_radicalQuotient {G : Type u} [Group G] [Group.FG G]
    (hHirsch : IsSolvableFiniteHirsch G) :
    ∃ H : Subgroup (G ⧸ locallyFiniteRadical G), H.FiniteIndex ∧ ∃ d : ℕ,
      ∃ p : H →* Multiplicative (Fin d → ℤ), Function.Surjective p ∧ Group.IsNilpotent p.ker := by
  obtain ⟨H,hH,d,q,hq,hNil⟩ := virtuallyNilpotentLatticeQuotient_radicalQuotient hHirsch
  let e : (Fin d → Multiplicative ℤ) ≃* Multiplicative (Fin d → ℤ) := {
    toFun := fun v => Multiplicative.ofAdd fun i => Multiplicative.toAdd (v i)
    invFun := fun v i => Multiplicative.ofAdd (Multiplicative.toAdd v i)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  let p := e.toMonoidHom.comp q
  have hker : p.ker = q.ker := by
    ext x
    exact map_eq_one_iff e e.injective
  exact ⟨H,hH,d,p,e.surjective.comp hq,hker.symm ▸ hNil⟩

end SolvableInduction

end LocalHirschHyperfinite

end
end
-- END COMPLETE MODULE HirschProof.VirtuallyNilpotentLattice

-- BEGIN COMPLETE MODULE HirschProof.IntegralMatrixCongruence
section
                                         
                              
                                 
                                         
                                 
                                       

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Matrix

variable {n : ℕ}
local notation "Square" => fun K n => Matrix (Fin n) (Fin n) K

private theorem one_add_pow_expansion {R : Type*} [Ring R] (x : R) (m : ℕ) :
    ∃ C : R, (1+x)^m = 1+m•x + x*x*C := by
  induction m with
  | zero => exact ⟨0,by simp⟩
  | succ m ih =>
    obtain ⟨C,hC⟩ := ih
    refine ⟨m • 1+C*(1+x),?_⟩
    rw [pow_succ,hC]
    simp only [add_mul,mul_add,mul_one,one_mul,succ_nsmul,mul_assoc,
      smul_mul_assoc,mul_smul_comm]
    abel

private theorem intScaled_add_pow {R : Type*} [Ring R] (t : ℤ) (B : R) (m : ℕ) :
    ∃ C : R, (1+t•B)^m = 1+((m : ℤ)*t)•B + (t*t)•C := by
  obtain ⟨C,hC⟩ := one_add_pow_expansion (t•B) m
  refine ⟨B*B*C,?_⟩
  rw [hC,← smul_assoc,nsmul_eq_mul,smul_mul_assoc,mul_smul_comm,smul_smul,smul_mul_assoc]

/-- Entrywise reduction of an integral matrix modulo (3). -/
def matrixModThree : Square ℤ n →+* Square (ZMod 3) n :=
  (Int.castRingHom (ZMod 3)).mapMatrix

private theorem exists_three_power_expansion (A : Square ℤ n)
    (hA : A ≠ 1) (hmod : matrixModThree A = 1) :
    ∃ k : ℕ, 0 < k ∧ ∃ B : Square ℤ n, A = 1+(3:ℤ)^k • B ∧
      ∃ i j, (B i j : ZMod 3) ≠ 0 := by
  classical
  let M := A-1
  have hM : M ≠ 0 := fun he => hA (sub_eq_zero.mp he)
  obtain ⟨i,j,hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra! h
    exact hM (Matrix.ext h)
  let a := (M i j).natAbs
  have ha : 0 < a := Int.natAbs_pos.mpr hij
  let P (k : ℕ) := ∀ i j, (3 : ℤ)^k ∣ M i j
  have hBase : P 1 := by
    intro i j
    have h : (M i j : ZMod 3) = 0 := by
      have hz : matrixModThree M = 0 := by rw [show M = A-1 from rfl,map_sub,hmod,map_one,sub_self]
      exact congrArg (fun X : Square (ZMod 3) n => X i j) hz
    simpa only [pow_one] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h
  have hBound (k : ℕ) (hk : P k) : k ≤ a := by
    have hdvd : (3:ℕ)^k ∣ a := by
      simpa [a,Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr (hk i j)
    have hkpow (x : ℕ) : x+1 ≤ 3^x := by
      induction x with
      | zero => simp
      | succ x ih => rw [pow_succ]; omega
    exact (Nat.le_succ k).trans ((hkpow k).trans (Nat.le_of_dvd ha hdvd))
  let k := Nat.findGreatest P a
  have hk : 0 < k := Nat.le_findGreatest (hBound 1 hBase) hBase
  have hp : P k := Nat.findGreatest_spec (hBound 1 hBase) hBase
  have hmax : ¬ P (k+1) := fun h => by
    have hb : k+1 ≤ k := Nat.le_findGreatest (hBound _ h) h
    omega
  choose B hB using hp
  refine ⟨k,hk,B,?_ ,?_⟩
  · apply Matrix.ext
    intro i j
    have hz := hB i j
    change A i j - (1 : Square ℤ n) i j = (3:ℤ)^k * B i j at hz
    change A i j = (1 : Square ℤ n) i j+(3:ℤ)^k * B i j
    omega
  · by_contra! h
    apply hmax
    intro i j
    obtain ⟨c,hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (h i j)
    change B i j = (3:ℤ)*c at hc
    use c
    rw [hB i j,hc,pow_succ,mul_assoc]

private theorem three_dvd_exponent_of_not_one (A : Square ℤ n)
    (hA : A ≠ 1) (hmod : matrixModThree A = 1) (m : ℕ) (hm : A^m=1) : 3 ∣ m := by
  obtain ⟨k,hk,B,hB,i,j,hnz⟩ := exists_three_power_expansion A hA hmod
  let t : ℤ := 3^k
  have htn : t ≠ 0 := pow_ne_zero _ (by decide)
  have hz : (t : ZMod 3) = 0 := by
    change (((3:ℤ)^k : ℤ) : ZMod 3) = 0
    rw [Int.cast_pow]
    exact zero_pow hk.ne'
  obtain ⟨C,hC⟩ := intScaled_add_pow t B m
  have he : (1 : Square ℤ n) = 1+((m:ℤ)*t)•B+(t*t)•C := by
    rw [hB] at hm
    exact hm.symm.trans hC
  have hp := congrArg (fun X : Square ℤ n => X i j) he
  change (1 : Square ℤ n) i j = (1 : Square ℤ n) i j+((m:ℤ)*t)*B i j+(t*t)*C i j at hp
  have hEq : t*((m:ℤ)*B i j+t*C i j)=0 := by
    linear_combination -hp
  have h' := congrArg (fun z : ℤ => (z : ZMod 3)) ((mul_eq_zero.mp hEq).resolve_left htn)
  have hmul : (m : ZMod 3)*(B i j : ZMod 3)=0 := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_zero,hz,zero_mul,add_zero] using h'
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact (ZMod.natCast_eq_zero_iff m 3).mp ((mul_eq_zero.mp hmul).resolve_right hnz)

private theorem not_cube_eq_one_of_not_one (A : Square ℤ n)
    (hA : A ≠ 1) (hmod : matrixModThree A = 1) : A^3 ≠ 1 := by
  intro hCube
  obtain ⟨k,hk,B,hB,i,j,hnz⟩ := exists_three_power_expansion A hA hmod
  let t : ℤ := 3^k
  let s : ℤ := 3^(k-1)
  have hts : t = 3*s := by
    change (3:ℤ)^k = 3*3^(k-1)
    rw [← pow_succ',Nat.sub_add_cancel hk]
  have htn : t ≠ 0 := pow_ne_zero _ (by decide)
  have hz : (t : ZMod 3) = 0 := by
    rw [hts,Int.cast_mul,show ((3:ℤ) : ZMod 3) = 0 by decide,zero_mul]
  have he : (1+t•B)^3 = (1 : Square ℤ n)+(3*t)•B+(3*t*t)•(B*B)+(t*t*t)•(B*B*B) := by
    simp only [pow_succ, pow_zero, one_mul, add_mul, mul_add, mul_one,
      smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
    rw [show (3*t*t:ℤ)=t*t+t*t+t*t by ring,show (3*t:ℤ)=t+t+t by ring]
    simp only [add_smul]
    abel_nf
    rw [mul_assoc t t t]
  rw [hB,he] at hCube
  have hp := congrArg (fun X : Square ℤ n => X i j) hCube
  change (1 : Square ℤ n) i j+(3*t)*B i j+(3*t*t)*(B*B) i j+(t*t*t)*(B*B*B) i j =
    (1 : Square ℤ n) i j at hp
  have hf : (3*t)*(B i j+t*(B*B) i j+(t*s)*(B*B*B) i j)=0 := by
    rw [hts] at hp ⊢
    linear_combination hp
  have h' := congrArg (fun z : ℤ => (z : ZMod 3)) ((mul_eq_zero.mp hf).resolve_left
    (mul_ne_zero (by decide : (3:ℤ)≠0) htn))
  exact hnz (by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_zero,hz,zero_mul,add_zero] using h')

/-- A finite-order integral matrix congruent to the identity modulo (3)
is the identity. -/
theorem integral_matrix_eq_one_of_finiteOrder_mod_three (A : Square ℤ n)
    (hA : IsOfFinOrder A) (hmod : matrixModThree A = 1) : A = 1 := by
  by_contra hn
  let m := orderOf A
  have hm : 0 < m := hA.orderOf_pos
  have hAp : A^m=1 := pow_orderOf_eq_one A
  obtain ⟨l,hl⟩ := three_dvd_exponent_of_not_one A hn hmod m hAp
  let B := A^l
  have hBn : B ≠ 1 := fun h => by
    have hdl : m ∣ l := orderOf_dvd_of_pow_eq_one h
    have hb : m ≤ l := Nat.le_of_dvd (by omega) hdl
    omega
  have hBmod : matrixModThree B = 1 := by
    change matrixModThree (A^l) = 1
    rw [map_pow,hmod,one_pow]
  have hBp : B^3=1 := by
    change (A^l)^3=1
    rw [← pow_mul,Nat.mul_comm,← hl]
    exact hAp
  exact not_cube_eq_one_of_not_one B hBn hBmod hBp

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.IntegralMatrixCongruence

-- BEGIN COMPLETE MODULE HirschProof.MatrixGeneratorRank
section
                                     
                               
                                                

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set TensorProduct

/-- In a torsion-free abelian group with finite rational rank, every
finitely generated subgroup has an integral basis of at most that size. -/
theorem GeneratorRankLE.of_finite_rationalization {A : Type*} [CommGroup A] [IsMulTorsionFree A]
    [Module.Finite ℚ (ℚ ⊗[ℤ] Additive A)] :
    GeneratorRankLE A (Module.finrank ℚ (ℚ ⊗[ℤ] Additive A)) := by
  classical
  intro H hH
  letI : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  letI : Module.Finite ℤ (Additive H) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  letI : Module.IsTorsionFree ℤ (Additive H) :=
    Module.isTorsionFree_int_iff_isAddTorsionFree.mpr inferInstance
  obtain ⟨k,b⟩ : Σ k : ℕ, Module.Basis (Fin k) ℤ (Additive H) :=
    Module.basisOfFiniteTypeTorsionFree'
  let f := H.subtype.toAdditive.toIntLinearMap
  have hk : k ≤ Module.finrank ℚ (ℚ ⊗[ℤ] Additive A) := by
    have he : Module.finrank ℚ (ℚ ⊗[ℤ] Additive H) = k := by
      rw [Module.finrank_eq_card_basis (b.baseChange ℚ),Fintype.card_fin]
    rw [← he]
    exact LinearMap.finrank_le_finrank_of_injective (rationalization_injective f H.subtype_injective)
  let U := Finset.univ.image (fun i : Fin k => (b i).toMul.val)
  let D := Subgroup.closure (U : Set A)
  let J := (D.comap H.subtype).toAddSubgroup.toIntSubmodule
  have hJ : J = ⊤ := by
    refine top_unique ?_
    rw [← b.span_eq,Submodule.span_le]
    rintro y ⟨i,rfl⟩
    change (b i).toMul.val ∈ D
    exact Subgroup.subset_closure (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  refine ⟨U,le_antisymm ?_ ?_,?_⟩
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact (b i).toMul.property
  · intro x hx
    have hy : Additive.ofMul (⟨x,hx⟩ : H) ∈ J := by rw [hJ]; exact Submodule.mem_top
    exact hy
  · exact (Finset.card_image_le.trans_eq (by simp : (Finset.univ : Finset (Fin k)).card = k)).trans hk

/-- The additive group of a finite-dimensional rational vector space has
finite Prüfer rank. -/
theorem GeneratorRankLE.of_rational_vector {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] : GeneratorRankLE (Multiplicative V) (Module.finrank ℚ V) := by
  let S := nonZeroDivisors ℤ
  haveI : IsLocalizedModule S (LinearMap.id : V →ₗ[ℤ] V) := isLocalizedModule_id S V ℚ
  let e : ℚ ⊗[ℤ] V ≃ₗ[ℚ] V :=
    (IsLocalizedModule.isBaseChange S ℚ (LinearMap.id : V →ₗ[ℤ] V)).equiv
  haveI : Module.Finite ℚ (ℚ ⊗[ℤ] Additive (Multiplicative V)) := Module.Finite.equiv e.symm
  haveI : IsAddTorsionFree V := ⟨fun {n} hn x y hxy => by
    have hz : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    apply smul_right_injective (M := V) hz
    simpa only [Nat.cast_smul_eq_nsmul] using hxy⟩
  have he : Module.finrank ℚ (ℚ ⊗[ℤ] Additive (Multiplicative V)) = Module.finrank ℚ V := e.finrank_eq
  rw [← he]
  exact GeneratorRankLE.of_finite_rationalization

section Unitriangular

local notation "Square" => fun K n => Matrix (Fin n) (Fin n) K

variable {G K : Type*} [Group G] [CommRing K] [Algebra ℚ K] [Module.Finite ℚ K] {n : ℕ}

/-- A faithfully unitriangular group over a finite-dimensional rational
algebra has finite Prüfer rank, by successive superdiagonal maps. -/
theorem exists_generatorRankLE_of_faithful_unitriangular (ρ : G →* (Square K n)ˣ)
    (hu : ∀ g : G, ∀ i j, j < i → (ρ g : Square K n) i j = 0)
    (hi : Function.Injective ρ) (hd : ∀ g i, (ρ g : Square K n) i i = 1) :
    ∃ d, GeneratorRankLE G d := by
  let F := MatrixLayers.Layer ρ hu
  have hFn : F (n+1) = ⊥ := bot_unique
    ((MatrixLayers.layer_antitone ρ hu (Nat.le_succ n)).trans (MatrixLayers.layer_last ρ hu hi).le)
  have hbase : GeneratorRankLE (F (n+1)) 0 := by
    rw [hFn]
    intro L hL
    have hbot : L = ⊥ := Subsingleton.elim _ _
    exact ⟨∅,by rw [Finset.coe_empty,Subgroup.closure_empty,hbot],by simp⟩
  have hStep (k : ℕ) (hk : 0 < k) (d : ℕ) (hprev : GeneratorRankLE (F (k+1)) d) :
      ∃ e, GeneratorRankLE (F k) e := by
    let p := MatrixLayers.superdiagonal ρ hu k hk
    have hker (x : F k) (hx : x ∈ p.ker) : x.val ∈ F (k+1) := by
      change x ∈ (MatrixLayers.superdiagonal ρ hu k hk).ker at hx
      rw [MatrixLayers.superdiagonal_ker] at hx
      exact hx
    let u : p.ker →* F (k+1) := {
      toFun := fun x => ⟨x.val.val,hker x.val x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hu' : Function.Injective u := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : F (k+1) => z.val) h))
    exact ⟨_,GeneratorRankLE.extension p (GeneratorRankLE.of_injective u hu' hprev)
      (GeneratorRankLE.of_rational_vector (V := MatrixLayers.Coordinate n k → K))⟩
  have hInd (m : ℕ) : ∀ k, 0 < k → m+k=n+1 → ∃ d, GeneratorRankLE (F k) d := by
    induction m with
    | zero =>
      intro k _ hk
      rw [Nat.zero_add] at hk
      exact ⟨0,hk.symm ▸ hbase⟩
    | succ m hm =>
      intro k hk h
      obtain ⟨d,hd'⟩ := hm (k+1) (by omega) (by omega)
      exact hStep k hk d hd'
  obtain ⟨d,h₀⟩ := hInd n 1 Nat.one_pos rfl
  let v : G →* F 1 := {
    toFun := fun g => ⟨g,by
      change g ∈ MatrixLayers.Layer ρ hu 1
      rw [MatrixLayers.layer_one ρ hu hd]
      exact Subgroup.mem_top g⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hv : Function.Injective v := fun _ _ h => congrArg (fun x : F 1 => x.val) h
  exact ⟨d,GeneratorRankLE.of_injective v hv h₀⟩

/-- The upper triangular finite-index model and all its subquotients can use
a single finite bound on subgroup generator numbers. -/
theorem exists_finiteIndex_generatorRankLE_of_faithful_triangular [Group.FG G]
    (ρ : G →* (Square K n)ˣ) (hu : ∀ g : G, ∀ i j, j < i → (ρ g : Square K n) i j = 0)
    (hi : Function.Injective ρ) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ ∃ d : ℕ, ∃ p : H →* (Fin d → Multiplicative ℤ),
      Function.Surjective p ∧ Group.IsNilpotent p.ker ∧
      (∀ g : H, (p g = 1 ↔ ∀ i, (ρ g.val : Square K n) i i = 1)) ∧
      ∃ e, GeneratorRankLE H e := by
  obtain ⟨H,hH,d,p,hp,hpn,hpd⟩ := exists_finiteIndex_nilpotent_freeAbelian_extension ρ hu hi
  let σ := ρ.comp (H.subtype.comp p.ker.subtype)
  have hσ : Function.Injective σ := hi.comp (H.subtype_injective.comp p.ker.subtype_injective)
  obtain ⟨e,he⟩ := exists_generatorRankLE_of_faithful_unitriangular σ
    (fun a => hu a.val.val) hσ (fun a => (hpd a.val).mp a.property)
  let j : (Fin d → Multiplicative ℤ) →* Multiplicative (Fin d → ℚ) := {
    toFun := fun x => Multiplicative.ofAdd (fun i => (x i).toAdd)
    map_one' := by apply Multiplicative.toAdd.injective; ext i; simp
    map_mul' := by
      intro a b
      apply Multiplicative.toAdd.injective
      ext i
      exact Int.cast_add (a i).toAdd (b i).toAdd }
  have hj : Function.Injective j := by
    intro a b h
    ext i
    apply Multiplicative.toAdd.injective
    have he := congrFun (congrArg (fun x : Multiplicative (Fin d → ℚ) => x.toAdd) h) i
    exact Int.cast_injective he
  exact ⟨H,hH,d,p,hp,hpn,hpd,_,GeneratorRankLE.extension p he
    (GeneratorRankLE.of_injective j hj GeneratorRankLE.of_rational_vector)⟩

end Unitriangular

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.MatrixGeneratorRank

-- BEGIN COMPLETE MODULE HirschProof.RationalLinearTorsion
section
                                           
                                      
                                         

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℚ V]
local notation "Square" => fun K n => Matrix (Fin n) (Fin n) K

private theorem injective_mod_three_on_finite {m : ℕ} [Finite G]
    (a : G →* (Square ℤ m)ˣ) (ha : Function.Injective a) :
    Function.Injective ((Units.map (matrixModThree (n := m)).toMonoidHom).comp a) := by
  let f := (Units.map (matrixModThree (n := m)).toMonoidHom).comp a
  apply (f.ker_eq_bot_iff).mp
  apply bot_unique
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply ha
  apply Units.ext
  have h₀ : f g = 1 := hg
  have h₁ : matrixModThree (a g : Square ℤ m) = 1 :=
    congrArg (fun x : (Square (ZMod 3) m)ˣ => (x : Square (ZMod 3) m)) h₀
  have hord : IsOfFinOrder (a g : Square ℤ m) := by
    obtain ⟨k,hk,he⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨k,hk,?_⟩
    rw [← Units.val_pow_eq_pow_val,← map_pow,he,map_one,Units.val_one]
  simpa only [map_one,Units.val_one] using integral_matrix_eq_one_of_finiteOrder_mod_three _ hord h₁

/-- A finite group acting faithfully on a rational vector space of
dimension (r) has order at most (3^{r^2}). Use an invariant integral
lattice and reduction modulo three. -/
theorem finite_rational_representation_bound [Finite G] [FiniteDimensional ℚ V]
    (ρ : G →* (V ≃ₗ[ℚ] V)) (hρ : Function.Injective ρ) :
    Nat.card G ≤ 3 ^ (Module.finrank ℚ V * Module.finrank ℚ V) := by
  classical
  let n := Module.finrank ℚ V
  let e := Module.finBasis ℚ V
  let s (t : G × Fin n) : V := ρ t.1 (e t.2)
  let L := Submodule.span ℤ (range s)
  letI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr (Submodule.fg_span (finite_range s))
  letI : IsAddTorsionFree V := ⟨fun {k} hk u v h => by
    have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    apply smul_right_injective (M := V) hkq
    simpa only [Nat.cast_smul_eq_nsmul] using h⟩
  letI : IsAddTorsionFree L := ⟨fun {k} hk x y h => by
    apply Subtype.ext
    apply nsmul_right_injective (M := V) hk
    exact congrArg (fun z : L => z.val) h⟩
  letI : Module.IsTorsionFree ℤ L :=
    Module.isTorsionFree_int_iff_isAddTorsionFree.mpr inferInstance
  obtain ⟨m,b⟩ : Σ m : ℕ, Module.Basis (Fin m) ℤ L := Module.basisOfFiniteTypeTorsionFree'
  have hm : m ≤ n := by
    let S := nonZeroDivisors ℤ
    haveI : IsLocalizedModule S (LinearMap.id : V →ₗ[ℤ] V) := isLocalizedModule_id S V ℚ
    let q : ℚ ⊗[ℤ] V ≃ₗ[ℚ] V :=
      (IsLocalizedModule.isBaseChange S ℚ (LinearMap.id : V →ₗ[ℤ] V)).equiv
    letI : Module.Finite ℚ (ℚ ⊗[ℤ] V) := Module.Finite.equiv q.symm
    calc
      m = Module.finrank ℚ (ℚ ⊗[ℤ] L) := by rw [Module.finrank_eq_card_basis (b.baseChange ℚ),Fintype.card_fin]
      _ ≤ Module.finrank ℚ (ℚ ⊗[ℤ] V) :=
        LinearMap.finrank_le_finrank_of_injective (rationalization_injective L.subtype L.subtype_injective)
      _ = n := q.finrank_eq
  let a (g : G) : Module.End ℤ V := (ρ g : Module.End ℚ V).restrictScalars ℤ
  have hL (g : G) : MapsTo (a g) (L : Set V) L := by
    change L ≤ L.comap (a g)
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨h,i⟩,rfl⟩
    change ρ g (ρ h (e i)) ∈ L
    rw [← LinearEquiv.mul_apply,← map_mul]
    exact Submodule.subset_span ⟨(g*h,i),rfl⟩
  let aL (g : G) : Module.End ℤ L := (a g).restrict (hL g)
  have haL (g h : G) : aL (g*h) = aL g * aL h := by
    ext w
    exact congrArg (fun u : V ≃ₗ[ℚ] V => u w.val) (map_mul ρ g h)
  have ha₁ : aL 1 = 1 := by
    ext w
    exact congrArg (fun u : V ≃ₗ[ℚ] V => u w.val) (map_one ρ)
  let f : G →* (Module.End ℤ L)ˣ := {
    toFun := fun g => ⟨aL g,aL g⁻¹,
      by rw [← haL,mul_inv_cancel,ha₁],by rw [← haL,inv_mul_cancel,ha₁]⟩
    map_one' := Units.ext ha₁
    map_mul' := fun g h => Units.ext (haL g h) }
  have hfi : Function.Injective f := by
    intro g h hf
    apply hρ
    apply LinearEquiv.toLinearMap_injective
    apply e.ext
    intro i
    have hi : e i ∈ L := Submodule.subset_span ⟨(1,i),by simp [s]⟩
    exact congrArg (fun q : (Module.End ℤ L)ˣ => (q.val ⟨e i,hi⟩).val) hf
  let E := Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv
  let r := E.toMonoidHom.comp f
  have hr : Function.Injective r := E.injective.comp hfi
  let h := (Units.map (matrixModThree (n := m)).toMonoidHom).comp r
  have hh : Function.Injective h := injective_mod_three_on_finite r hr
  calc
    Nat.card G ≤ Nat.card (Square (ZMod 3) m) := Nat.card_le_card_of_injective
      (fun g => (h g : Square (ZMod 3) m)) (Units.val_injective.comp hh)
    _ = 3^(m*m) := by simp [Matrix,Nat.card_eq_fintype_card,ZMod.card,← pow_mul]
    _ ≤ 3^(n*n) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hm hm)

/-- A locally finite group with a faithful finite-dimensional rational
representation is finite. -/
theorem finite_of_locallyFinite_of_faithful_rational [FiniteDimensional ℚ V]
    (hG : IsLocallyFiniteGroup G) (ρ : G →* (V ≃ₗ[ℚ] V)) (hρ : Function.Injective ρ) : Finite G := by
  classical
  by_contra h
  letI : Infinite G := not_finite_iff_infinite.mp h
  let C := 3^(Module.finrank ℚ V * Module.finrank ℚ V)
  obtain ⟨S,hS⟩ := Infinite.exists_subset_card_eq G (C+1)
  let H := Subgroup.closure (S : Set G)
  have hH : H.FG := (Subgroup.fg_iff _).mpr ⟨S,rfl,S.finite_toSet⟩
  letI : Finite H := hG H hH
  have hC : Nat.card H ≤ C :=
    finite_rational_representation_bound (ρ.comp H.subtype) (hρ.comp H.subtype_injective)
  have hlo : S.card ≤ Nat.card H := by
    let j (x : (↑S : Type _)) : H := ⟨x.val,Subgroup.subset_closure x.property⟩
    have hj : Function.Injective j := fun _ _ h => Subtype.ext (congrArg (fun x : H => x.val) h)
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_le_card_of_injective j hj
  omega

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.RationalLinearTorsion

-- BEGIN COMPLETE MODULE HirschProof.RationalConjugationAction
section
                                            
                                              
                                               
                                         

set_option autoImplicit false

namespace LocalHirschHyperfinite

open scoped TensorProduct IsMulCommutative

/-- The canonical map to the rationalization of a torsion-free abelian
group is injective. -/
theorem rationalization_unit_injective {V : Type*} [AddCommGroup V] [IsAddTorsionFree V] :
    Function.Injective (fun a : V => (1 : ℚ) ⊗ₜ[ℤ] a) := by
  intro a b hab
  change (1 : ℚ) ⊗ₜ[ℤ] a = (1 : ℚ) ⊗ₜ[ℤ] b at hab
  have hz : (1 : ℚ) ⊗ₜ[ℤ] (a-b) = 0 := by
    rw [TensorProduct.tmul_sub,hab,sub_self]
  obtain ⟨m,hm,hmz⟩ := (rationalization_eq_zero_iff _).mp hz
  have h : a-b = 0 := (nsmul_eq_zero_iff_right hm.ne').mp hmz
  exact sub_eq_zero.mp h

variable {G : Type*} [Group G]
variable (A : Subgroup G) [A.Normal] [IsMulCommutative A]

/-- Conjugation on a normal abelian subgroup gives an integral linear
action on its additive form. -/
def integralConjugation : G →* Module.End ℤ (Additive A) where
  toFun g := (MulAut.conjNormal (H := A) g).toMonoidHom.toAdditive.toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro a
    change Additive.ofMul (MulAut.conjNormal (H := A) (1 : G) a.toMul) = a
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro a
    change Additive.ofMul (MulAut.conjNormal (H := A) (g*h) a.toMul) =
      Additive.ofMul (MulAut.conjNormal (H := A) g (MulAut.conjNormal h a.toMul))
    rw [map_mul]
    rfl

/-- The above action extended to the finite-dimensional rationalization
when the normal subgroup has finite rational rank. -/
noncomputable def rationalConjugation : G →* Module.End ℚ (ℚ ⊗[ℤ] Additive A) :=
  (Module.End.baseChangeHom ℤ ℚ (Additive A)).toMonoidHom.comp (integralConjugation A)

theorem rationalConjugation_tmul (g : G) (r : ℚ) (a : A) :
    rationalConjugation A g (r ⊗ₜ[ℤ] Additive.ofMul a) =
      r ⊗ₜ[ℤ] Additive.ofMul (MulAut.conjNormal (H := A) g a) := by
  exact LinearMap.baseChange_tmul _ _ _

/-- Torsion-freeness makes the kernel of the rationalized conjugation
exactly the centralizer of the subgroup. -/
theorem rationalConjugation_eq_one_iff [IsMulTorsionFree A] (g : G) :
    rationalConjugation A g = 1 ↔ g ∈ Subgroup.centralizer (A : Set G) := by
  constructor
  · intro hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    let a' : A := ⟨a,ha⟩
    have he := DFunLike.congr_fun hg ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul a')
    rw [rationalConjugation_tmul,Module.End.one_apply] at he
    have he' := rationalization_unit_injective he
    have h := congrArg Subtype.val (congrArg Additive.toMul he')
    change (MulAut.conjNormal (H := A) g a').val = a at h
    rw [MulAut.conjNormal_apply] at h
    change g*a*g⁻¹ = a at h
    have heq := congrArg (fun y : G => y*g) h
    simpa [mul_assoc] using heq.symm
  · intro hg
    have he : integralConjugation A g = 1 := by
      apply LinearMap.ext
      intro a
      change Additive.ofMul (MulAut.conjNormal (H := A) g a.toMul) = Additive.ofMul a.toMul
      apply congrArg Additive.ofMul
      apply Subtype.ext
      rw [MulAut.conjNormal_apply,← Subgroup.mem_centralizer_iff.mp hg _ a.toMul.property]
      simp [mul_assoc]
    change (Module.End.baseChangeHom ℤ ℚ (Additive A)) (integralConjugation A g) = 1
    rw [he,map_one]

theorem rationalConjugation_units_ker [IsMulTorsionFree A] :
    (rationalConjugation A).toHomUnits.ker = Subgroup.centralizer (A : Set G) := by
  ext g
  change (rationalConjugation A).toHomUnits g = 1 ↔ _
  rw [← Units.val_inj]
  exact rationalConjugation_eq_one_iff A g

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.RationalConjugationAction

-- BEGIN COMPLETE MODULE HirschProof.RadicalQuotientRank
section
                                        
                                          
                                            

set_option autoImplicit false

namespace LocalHirschHyperfinite
open Set TensorProduct

attribute [local instance] commGroupOfAbelianSubgroup

variable {G : Type*} [Group G]

/-- Subgroups of a finite group are generated by their full underlying sets. -/
theorem GeneratorRankLE.of_finite [Finite G] : GeneratorRankLE G (Nat.card G) := by
  classical
  intro H _
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite H
  let S := Finset.univ.image H.subtype
  have hS : (S : Set G) = H := by
    ext g
    constructor
    · intro hg
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hg
      exact x.property
    · intro hg
      exact Finset.mem_image.mpr ⟨⟨g,hg⟩,Finset.mem_univ _,rfl⟩
  refine ⟨S,by rw [hS,Subgroup.closure_eq],Finset.card_image_le.trans ?_⟩
  simpa only [Finset.card_univ,Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_injective H.subtype H.subtype_injective

/-- The preimage of the locally finite radical modulo a normal abelian
subgroup has finite Prüfer rank in a radical-free solvable group of finite
Hirsch length. Its conjugation image is finite, and the kernel is abelian. -/
theorem exists_generatorRankLE_preimage_radical_of_abelian
    (hG : IsSolvableFiniteHirsch G) (hR : locallyFiniteRadical G = ⊥)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] :
    ∃ d, GeneratorRankLE ((locallyFiniteRadical (G ⧸ A)).comap (QuotientGroup.mk' A)) d := by
  letI : IsMulTorsionFree A := isMulTorsionFree_of_normal_abelian_radical_free A hR
  let V := ℚ ⊗[ℤ] Additive A
  letI : Module.Finite ℚ V :=
    finite_rationalization_of_solvableFiniteHirsch hG A (MonoidHom.id A) Function.surjective_id
  let u := (rationalConjugation A).toHomUnits
  let E := LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ V
  let ρ : G →* (V ≃ₗ[ℚ] V) := E.toMonoidHom.comp u
  have hρ : ρ.ker = Subgroup.centralizer (A : Set G) := by
    rw [← rationalConjugation_units_ker A]
    ext g
    change E (u g) = 1 ↔ u g = 1
    rw [← E.map_one,E.injective.eq_iff]
  have hA : A ≤ ρ.ker := by
    rw [hρ]
    intro a ha
    apply Subgroup.mem_centralizer_iff.mpr
    intro b hb
    exact congrArg Subtype.val (mul_comm' (⟨b,hb⟩ : A) ⟨a,ha⟩)
  let q := QuotientGroup.mk' A
  let R := locallyFiniteRadical (G ⧸ A)
  let B := R.comap q
  let C := B ⊓ ρ.ker
  let σ := QuotientGroup.lift A ρ hA
  let f := ρ.comp B.subtype
  have hσ (g : G) : σ (q g) = ρ g := rfl
  have hF : f.range = R.map σ := by
    ext x
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨q b.val,b.property,hσ b.val⟩
    · rintro ⟨r,hr,rfl⟩
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective A r
      exact ⟨⟨g,hr⟩,(hσ g).symm⟩
  have hFL : IsLocallyFiniteGroup f.range := hF.symm ▸
    IsLocallyFiniteGroup.image R (locallyFiniteRadical_locallyFinite _) σ
  letI : Finite f.range :=
    finite_of_locallyFinite_of_faithful_rational hFL f.range.subtype f.range.subtype_injective
  let p : C →* R := (q.comp C.subtype).codRestrict R (fun x => x.property.1)
  have hp : p.ker ≤ Subgroup.center C := by
    intro x hx
    have hxA : x.val ∈ A := (QuotientGroup.eq_one_iff _).mp
      (congrArg (fun a : R => a.val) (show p x = 1 from hx))
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hy : y.val ∈ Subgroup.centralizer (A : Set G) := hρ ▸ y.property.2
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hy _ hxA).symm)
  have hLF := IsLocallyFiniteGroup.commutator_of_central_kernel p hp
    (locallyFiniteRadical_locallyFinite (G ⧸ A))
  let D := (commutator C).map C.subtype
  have hDn : D.Normal := by
    change ((commutator C).map C.subtype).Normal
    rw [Subgroup.map_subtype_commutator]
    infer_instance
  have hD := IsLocallyFiniteGroup.image (commutator C) hLF C.subtype
  have hDbot := (le_locallyFiniteRadical G hDn hD).trans hR.le
  letI : IsMulCommutative C := (commutator_eq_bot_iff C).mp (bot_unique (by
    intro x hx
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp (hDbot ⟨x,hx,rfl⟩)))))
  letI : IsMulTorsionFree C := isMulTorsionFree_of_normal_abelian_radical_free C hR
  letI : Module.Finite ℚ (ℚ ⊗[ℤ] Additive C) :=
    finite_rationalization_of_solvableFiniteHirsch hG C (MonoidHom.id C) Function.surjective_id
  let j : f.rangeRestrict.ker →* C :=
    (B.subtype.comp f.rangeRestrict.ker.subtype).codRestrict C (fun x =>
      ⟨x.val.property, congrArg (fun a : f.range => a.val) (show f.rangeRestrict x.val = 1 from x.property)⟩)
  have hj : Function.Injective j := fun _ _ he =>
    Subtype.ext (Subtype.ext (congrArg (fun x : C => x.val) he))
  exact ⟨_,GeneratorRankLE.extension f.rangeRestrict
    (GeneratorRankLE.of_injective j hj GeneratorRankLE.of_finite_rationalization)
    GeneratorRankLE.of_finite⟩

set_option maxHeartbeats 1000000 in
/-- Radical-free solvable groups of finite Hirsch length have finite Prüfer
rank. Strip the last abelian derived subgroup and the locally finite radical
of its quotient so that the induction applies to a radical-free group. -/
theorem exists_generatorRankLE_of_radical_free (hG : IsSolvableFiniteHirsch G)
    (hR : locallyFiniteRadical G = ⊥) : ∃ d, GeneratorRankLE G d := by
  have main (n : ℕ) : ∀ (Q : Type _) [Group Q], IsSolvableFiniteHirsch Q →
      locallyFiniteRadical Q = ⊥ → derivedSeries Q n = ⊥ → ∃ d, GeneratorRankLE Q d := by
    induction n with
    | zero =>
      intro Q _ _ _ h
      have htop : (⊤ : Subgroup Q) = ⊥ := h
      letI : Subsingleton Q := ⟨fun a b =>
        (Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top a)).trans
          (Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top b)).symm⟩
      exact ⟨_,GeneratorRankLE.of_finite⟩
    | succ n ih =>
      intro Q _ hh hR' h
      let A := derivedSeries Q n
      letI : A.Normal := derivedSeries_normal Q n
      have hA : commutator A = ⊥ := by
        apply Subgroup.map_subtype_inj.mp
        rw [Subgroup.map_subtype_commutator,Subgroup.map_bot,← derivedSeries_succ]
        exact h
      letI : IsMulCommutative A := (commutator_eq_bot_iff A).mp hA
      let q := QuotientGroup.mk' A
      let R := locallyFiniteRadical (Q ⧸ A)
      let B := R.comap q
      let t := QuotientGroup.mk' R
      let p := t.comp q
      have hp : Function.Surjective p :=
        (QuotientGroup.mk'_surjective R).comp (QuotientGroup.mk'_surjective A)
      have hpK : p.ker = B := by rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
      have hRad : locallyFiniteRadical ((Q ⧸ A) ⧸ R) = ⊥ :=
        normal_locallyFinite_in_radical_quotient_eq_bot (Q ⧸ A) _ inferInstance
          (locallyFiniteRadical_locallyFinite _)
      have hq : derivedSeries ((Q ⧸ A) ⧸ R) n = ⊥ := by
        rw [← map_derivedSeries_eq hp n]
        apply (Subgroup.map_eq_bot_iff A).mpr
        rw [hpK]
        intro x hx
        change q x ∈ R
        rw [show q x = 1 from (QuotientGroup.eq_one_iff _).mpr hx]
        exact R.one_mem
      obtain ⟨a,ha⟩ := exists_generatorRankLE_preimage_radical_of_abelian hh hR' A
      obtain ⟨b,hb⟩ := ih _ (hh.of_surjective p hp) hRad hq
      exact ⟨a+b,GeneratorRankLE.extension p (hpK.symm ▸ ha) hb⟩
  obtain ⟨n,hn⟩ := hG.1.solvable
  exact main n G hG hR hn

/-- The quotient by the locally finite radical of a solvable finite-Hirsch
group has finite Prüfer rank. -/
theorem exists_generatorRankLE_radical_quotient (hG : IsSolvableFiniteHirsch G) :
    ∃ d, GeneratorRankLE (G ⧸ locallyFiniteRadical G) d := by
  let R := locallyFiniteRadical G
  exact exists_generatorRankLE_of_radical_free
    (hG.of_surjective (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R))
    (normal_locallyFinite_in_radical_quotient_eq_bot G _ inferInstance (locallyFiniteRadical_locallyFinite _))

end LocalHirschHyperfinite

end
-- END COMPLETE MODULE HirschProof.RadicalQuotientRank

-- BEGIN COMPLETE MODULE Solutions.Main
section
                                           
                                            
                                      

set_option autoImplicit false

theorem LocalHirschHyperfinite.theorem1_1 (G X : Type*)
    [Group G] [Countable G] [MulAction G X] [MeasurableSpace X] [StandardBorelSpace X]
    (hG : LocalHirschHyperfinite.IsLocallyVirtuallySolvableFiniteHirsch G)
    (hX : LocalHirschHyperfinite.BorelAction G X) :
    LocalHirschHyperfinite.IsHyperfinite (LocalHirschHyperfinite.orbitRel G (X := X)) := by
  apply LocalHirschHyperfinite.hyperfinite_of_nilpotent_lattice_radical_quotients G X hG hX
  · intro J _ _ hJ
    exact LocalHirschHyperfinite.exists_nilpotent_lattice_quotient_radicalQuotient hJ
  · intro J _ _ hJ
    exact LocalHirschHyperfinite.exists_generatorRankLE_radical_quotient hJ

end
-- END COMPLETE MODULE Solutions.Main

set_option autoImplicit false

theorem solution (G X : Type*)
    [Group G] [Countable G] [MulAction G X] [MeasurableSpace X] [StandardBorelSpace X]
    (hG : LocalHirschHyperfinite.IsLocallyVirtuallySolvableFiniteHirsch G)
    (hX : LocalHirschHyperfinite.BorelAction G X) :
    LocalHirschHyperfinite.IsHyperfinite (LocalHirschHyperfinite.orbitRel G (X := X)) := by
  first
  | exact @LocalHirschHyperfinite.theorem1_1
  | apply @LocalHirschHyperfinite.theorem1_1 <;> assumption

#print axioms solution
