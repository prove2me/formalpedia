-- Prove2me | solution 1 for FSCofinality.invariant_real_parameters
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-11-02T15:31:52.741725+00:00
-- url     : https://prove2.me/submissions/2a76de34-92be-400e-af2b-6e1d79717d8b

import Definitions.Def_FSCofinalityStructures20261102
import Definitions.Def_FSCofinalityTrees20261102
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Indexes
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.List
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.WellFounded
import Mathlib.Order.WithBot
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Tactic
import Mathlib.Topology.List
import Mathlib.Topology.MetricSpace.PiNat

-- Original module: FSCofinalityProof.StructuresBasics
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality

theorem Isomorphic.refl {L : CountableRelationalLanguage} (M : Structures L) :
    Isomorphic M M := ⟨Equiv.refl ℕ, fun _ _ => rfl⟩

theorem Isomorphic.symm {L : CountableRelationalLanguage} {M N : Structures L}
    (h : Isomorphic M N) : Isomorphic N M := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,fun s a => ?_⟩
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using (he s (e.symm ∘ a)).symm

theorem Isomorphic.trans {L : CountableRelationalLanguage} {M N P : Structures L}
    (hMN : Isomorphic M N) (hNP : Isomorphic N P) : Isomorphic M P := by
  obtain ⟨e,he⟩ := hMN
  obtain ⟨f,hf⟩ := hNP
  refine ⟨e.trans f,fun s a => ?_⟩
  exact (he s a).trans (hf s (e ∘ a))

theorem isomorphic_equivalence (L : CountableRelationalLanguage) :
    Equivalence (@Isomorphic L) :=
  ⟨Isomorphic.refl,Isomorphic.symm,Isomorphic.trans⟩

def structuresSetoid (L : CountableRelationalLanguage) : Setoid (Structures L) :=
  ⟨Isomorphic,isomorphic_equivalence L⟩

theorem IsInvariant.mem_iff {L : CountableRelationalLanguage} {K : Set (Structures L)}
    (hK : IsInvariant K) {M N : Structures L} (hMN : Isomorphic M N) : M ∈ K ↔ N ∈ K :=
  ⟨fun hM => hK hM hMN,fun hN => hK hN hMN.symm⟩

theorem GraphIsomorphic.refl (G : GraphSpace) : GraphIsomorphic G G :=
  ⟨Equiv.refl ℕ,fun _ _ => rfl⟩

theorem GraphIsomorphic.symm {G H : GraphSpace} (h : GraphIsomorphic G H) :
    GraphIsomorphic H G := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,fun m n => ?_⟩
  simpa only [Equiv.apply_symm_apply] using (he (e.symm m) (e.symm n)).symm

theorem GraphIsomorphic.trans {G H K : GraphSpace}
    (hGH : GraphIsomorphic G H) (hHK : GraphIsomorphic H K) : GraphIsomorphic G K := by
  obtain ⟨e,he⟩ := hGH
  obtain ⟨f,hf⟩ := hHK
  exact ⟨e.trans f,fun m n => (he m n).trans (hf (e m) (e n))⟩

theorem graphIsomorphic_equivalence : Equivalence GraphIsomorphic :=
  ⟨GraphIsomorphic.refl,GraphIsomorphic.symm,GraphIsomorphic.trans⟩

def graphSetoid : Setoid GraphSpace := ⟨GraphIsomorphic,graphIsomorphic_equivalence⟩

theorem BorelReducible.refl {X : Type} [MeasurableSpace X] (E : X → X → Prop) :
    BorelReducible E E := ⟨id,measurable_id,fun _ _ => Iff.rfl⟩

theorem BorelReducible.trans {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {E : X → X → Prop} {F : Y → Y → Prop} {R : Z → Z → Prop}
    (hEF : BorelReducible E F) (hFR : BorelReducible F R) : BorelReducible E R := by
  obtain ⟨f,hf,hredf⟩ := hEF
  obtain ⟨g,hg,hredg⟩ := hFR
  exact ⟨g ∘ f,hg.comp hf,fun x y => (hredf x y).trans (hredg (f x) (f y))⟩

theorem CodedRelation.Reduces.refl (E : CodedRelation) : E.Reduces E :=
  BorelReducible.refl E.rel

theorem CodedRelation.Reduces.trans {E F R : CodedRelation}
    (hEF : E.Reduces F) (hFR : F.Reduces R) : E.Reduces R :=
  BorelReducible.trans hEF hFR

theorem BorelReducible.target_nonempty {X Y : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X]
    {E : X → X → Prop} {F : Y → Y → Prop} (h : BorelReducible E F) : Nonempty Y := by
  obtain ⟨f,_,_⟩ := h
  exact ⟨f (Classical.choice inferInstance)⟩

end FSCofinality

end
end

-- Original module: FSCofinalityProof.PartialIsomorphism
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory TopologicalSpace

namespace FSCofinality.PartialIso

/-- Agreement of complete atomic diagrams on a finite correspondence.
Repeated entries are permitted; equality agreement makes the induced
correspondence a partial bijection. Nullary symbols are included. -/
def AtomicCompatible {L : CountableRelationalLanguage} (M N : Structures L)
    (R : Set (ℕ × ℕ)) : Prop :=
  (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 ↔ p.2 = q.2) ∧
  ∀ (s : L.Symbol) (a : Fin (L.arity s) → ℕ × ℕ),
    (∀ i, a i ∈ R) → M ⟨s,fun i => (a i).1⟩ = N ⟨s,fun i => (a i).2⟩

theorem AtomicCompatible.mono {L : CountableRelationalLanguage} {M N : Structures L}
    {R S : Set (ℕ × ℕ)} (h : AtomicCompatible M N S) (hRS : R ⊆ S) :
    AtomicCompatible M N R :=
  ⟨fun p hp q hq => h.1 p (hRS hp) q (hRS hq),
    fun s a ha => h.2 s a (fun i => hRS (ha i))⟩

/-- Even stages ensure domain coverage, odd stages ensure range coverage. -/
def scheduledPair (k a : ℕ) : ℕ × ℕ :=
  if k % 2 = 0 then (k/2,a) else (a,k/2)

@[simp] theorem scheduledPair_even (i a : ℕ) : scheduledPair (2*i) a = (i,a) := by
  simp [scheduledPair]

@[simp] theorem scheduledPair_odd (i a : ℕ) : scheduledPair (2*i+1) a = (a,i) := by
  simp [scheduledPair]
  omega

def pairsFrom : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | k, a :: s => scheduledPair k a :: pairsFrom (k+1) s

theorem pairsFrom_append (k : ℕ) (s t : List ℕ) :
    pairsFrom k (s ++ t) = pairsFrom k s ++ pairsFrom (k+s.length) t := by
  induction s generalizing k with
  | nil => simp [pairsFrom]
  | cons a s IH =>
      simp only [List.cons_append,pairsFrom,List.length_cons]
      rw [IH]
      simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem pairsFrom_ofFn {n : ℕ} (k : ℕ) (f : Fin n → ℕ) :
    pairsFrom k (List.ofFn f) = List.ofFn (fun i : Fin n => scheduledPair (k+i.val) (f i)) := by
  induction n generalizing k with
  | zero => simp [pairsFrom]
  | succ n IH =>
      rw [List.ofFn_succ,pairsFrom,IH,List.ofFn_succ]
      congr 1
      apply congrArg List.ofFn
      funext i
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def attemptTree {L : CountableRelationalLanguage} (M N : Structures L) :
    RootedTrees.TreeSpace where
  val := fun s => decide (AtomicCompatible M N {p | p ∈ pairsFrom 0 s})
  property := by
    intro s n hs
    apply of_decide_eq_true at hs
    apply decide_eq_true
    apply hs.mono
    intro p hp
    simpa only [pairsFrom_append,List.mem_append,mem_setOf_eq] using Or.inl hp

def initialSegment (b : ℕ → ℕ) (n : ℕ) : List ℕ := List.ofFn (fun i : Fin n => b i.val)

theorem scheduledPair_mem_prefix (b : ℕ → ℕ) {k n : ℕ} (hk : k < n) :
    scheduledPair k (b k) ∈ pairsFrom 0 (initialSegment b n) := by
  rw [initialSegment,pairsFrom_ofFn]
  exact List.mem_ofFn.mpr ⟨⟨k,hk⟩,by simp⟩

theorem compatible_of_branch {L : CountableRelationalLanguage} {M N : Structures L}
    {b : ℕ → ℕ} (hb : ∀ n, attemptTree M N (initialSegment b n) = true) (n : ℕ) :
    AtomicCompatible M N {p | p ∈ pairsFrom 0 (initialSegment b n)} :=
  of_decide_eq_true (hb n)

theorem isomorphic_of_branch {L : CountableRelationalLanguage} {M N : Structures L}
    (b : ℕ → ℕ) (hb : ∀ n, attemptTree M N (initialSegment b n) = true) : Isomorphic M N := by
  let f : ℕ → ℕ := fun i => b (2*i)
  let g : ℕ → ℕ := fun i => b (2*i+1)
  have hpair (i : ℕ) {n : ℕ} (hn : 2*i < n) :
      (i,f i) ∈ pairsFrom 0 (initialSegment b n) := by
    simpa only [scheduledPair_even,f] using scheduledPair_mem_prefix b hn
  have hipair (i : ℕ) {n : ℕ} (hn : 2*i+1 < n) :
      (g i,i) ∈ pairsFrom 0 (initialSegment b n) := by
    simpa only [scheduledPair_odd,g] using scheduledPair_mem_prefix b hn
  have hgf (i : ℕ) : g (f i) = i := by
    let n := max (2*i) (2*(f i)+1)+1
    exact ((compatible_of_branch hb n).1 (i,f i) (hpair i (by omega))
      (g (f i),f i) (hipair (f i) (by omega))).mpr rfl |>.symm
  have hfg (i : ℕ) : f (g i) = i := by
    let n := max (2*(g i)) (2*i+1)+1
    exact ((compatible_of_branch hb n).1 (g i,f (g i)) (hpair (g i) (by omega))
      (g i,i) (hipair i (by omega))).mp rfl
  let e : ℕ ≃ ℕ := ⟨f,g,hgf,hfg⟩
  refine ⟨e,fun s a => ?_⟩
  let n : ℕ := (Finset.univ.sup (fun i : Fin (L.arity s) => 2*(a i)))+1
  exact (compatible_of_branch hb n).2 s (fun i => (a i,f (a i)))
    (fun i => hpair (a i) (by
      exact Nat.lt_succ_of_le (Finset.le_sup
        (f := fun i : Fin (L.arity s) => 2*(a i)) (Finset.mem_univ i))))

theorem compatible_graph {L : CountableRelationalLanguage} {M N : Structures L}
    (e : ℕ ≃ ℕ) (he : ∀ s a, M ⟨s,a⟩ = N ⟨s,e ∘ a⟩)
    {R : Set (ℕ × ℕ)} (hR : ∀ p ∈ R, e p.1 = p.2) : AtomicCompatible M N R := by
  refine ⟨?_,?_⟩
  · intro p hp q hq
    rw [← hR p hp,← hR q hq]
    exact e.injective.eq_iff.symm
  · intro s a ha
    have h := he s (fun i => (a i).1)
    have ht : (fun i => (a i).2) = e ∘ (fun i => (a i).1) :=
      funext (fun i => (hR (a i) (ha i)).symm)
    rwa [ht]

theorem branch_of_isomorphic {L : CountableRelationalLanguage} {M N : Structures L}
    (h : Isomorphic M N) :
    ∃ b : ℕ → ℕ, ∀ n, attemptTree M N (initialSegment b n) = true := by
  obtain ⟨e,he⟩ := h
  let b : ℕ → ℕ := fun k => if k % 2 = 0 then e (k/2) else e.symm (k/2)
  refine ⟨b,fun n => ?_⟩
  apply decide_eq_true
  apply compatible_graph e he
  intro p hp
  rw [initialSegment,pairsFrom_ofFn] at hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  simp only [Nat.zero_add]
  dsimp only [scheduledPair,b]
  split_ifs <;> simp

theorem branch_iff_isomorphic {L : CountableRelationalLanguage} (M N : Structures L) :
    (∃ b : ℕ → ℕ, ∀ n, attemptTree M N (initialSegment b n) = true) ↔ Isomorphic M N :=
  ⟨fun ⟨b,hb⟩ => isomorphic_of_branch b hb,branch_of_isomorphic⟩

theorem measurableSet_atomicCompatible {L : CountableRelationalLanguage}
    (R : Set (ℕ × ℕ)) :
    MeasurableSet {p : Structures L × Structures L | AtomicCompatible p.1 p.2 R} := by
  have heq : MeasurableSet {p : Structures L × Structures L |
      ∀ u ∈ R, ∀ v ∈ R, u.1 = v.1 ↔ u.2 = v.2} := by
    by_cases h : ∀ u ∈ R, ∀ v ∈ R, u.1 = v.1 ↔ u.2 = v.2 <;> simp [h]
  unfold AtomicCompatible
  rw [setOf_and]
  apply heq.inter
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro s
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro ha
  let c₁ : Coordinate L := ⟨s,fun i => (a i).1⟩
  let c₂ : Coordinate L := ⟨s,fun i => (a i).2⟩
  have hc₁ : Continuous (fun M : Structures L => M c₁) := _root_.continuous_apply c₁
  have hc₂ : Continuous (fun M : Structures L => M c₂) := _root_.continuous_apply c₂
  exact measurableSet_eq_fun (hc₁.comp continuous_fst).measurable
    (hc₂.comp continuous_snd).measurable

/-- The tree of all scheduled partial-isomorphism attempts depends
Borel measurably on the pair of structures. -/
theorem measurable_attemptTree {L : CountableRelationalLanguage} :
    Measurable (fun p : Structures L × Structures L => attemptTree p.1 p.2) := by
  have hemb : MeasurableEmbedding
      (fun T : RootedTrees.TreeSpace => T.val) :=
    (show Topology.IsClosedEmbedding (fun T : RootedTrees.TreeSpace => T.val) from
      RootedTrees.isClosed_prefixClosed.isClosedEmbedding_subtypeVal).measurableEmbedding
  apply hemb.measurable_comp_iff.mp
  change Measurable (fun p : Structures L × Structures L =>
    fun s : RootedTrees.Node => decide (AtomicCompatible p.1 p.2 {q | q ∈ pairsFrom 0 s}))
  apply measurable_pi_iff.mpr
  intro s
  exact Measurable.ite (measurableSet_atomicCompatible {q | q ∈ pairsFrom 0 s})
    measurable_const measurable_const

end FSCofinality.PartialIso


end
end

-- Original module: FSCofinalityProof.PartialIsomorphismRank
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

/-- The ordinary transfinite back-and-forth relation on a finite partial
correspondence. At every lower stage, one new element on either side can
be matched. Equality and all relation symbols are checked at stage zero. -/
def BackAndForth {L : CountableRelationalLanguage} (M N : Structures L)
    (a : Ordinal.{0}) (R : List (ℕ × ℕ)) : Prop :=
  AtomicCompatible M N {p | p ∈ R} ∧
  ∀ b : Ordinal.{0}, b < a →
    (∀ x : ℕ, ∃ y : ℕ, BackAndForth M N b (R ++ [(x,y)])) ∧
    (∀ y : ℕ, ∃ x : ℕ, BackAndForth M N b (R ++ [(x,y)]))
termination_by a

theorem BackAndForth.atomic {L : CountableRelationalLanguage} {M N : Structures L}
    {a : Ordinal.{0}} {R : List (ℕ × ℕ)} (h : BackAndForth M N a R) :
    AtomicCompatible M N {p | p ∈ R} := by
  rw [BackAndForth] at h
  exact h.1

theorem BackAndForth.mono {L : CountableRelationalLanguage} {M N : Structures L}
    {a b : Ordinal.{0}} {R : List (ℕ × ℕ)}
    (h : BackAndForth M N a R) (hba : b ≤ a) : BackAndForth M N b R := by
  rw [BackAndForth] at h ⊢
  exact ⟨h.1,fun c hc => h.2 c (lt_of_lt_of_le hc hba)⟩

theorem BackAndForth.scheduled_extension
    {L : CountableRelationalLanguage} {M N : Structures L}
    {a b : Ordinal.{0}} (s : List ℕ)
    (h : BackAndForth M N a (pairsFrom 0 s)) (hba : b < a) :
    ∃ n : ℕ, BackAndForth M N b (pairsFrom 0 (s ++ [n])) := by
  rw [BackAndForth] at h
  by_cases heven : s.length % 2 = 0
  · obtain ⟨y,hy⟩ := (h.2 b hba).1 (s.length/2)
    refine ⟨y,?_⟩
    simpa only [pairsFrom_append,pairsFrom,Nat.zero_add,List.append_nil,
      scheduledPair,if_pos heven] using hy
  · obtain ⟨x,hx⟩ := (h.2 b hba).2 (s.length/2)
    refine ⟨x,?_⟩
    simpa only [pairsFrom_append,pairsFrom,Nat.zero_add,List.append_nil,
      scheduledPair,if_neg heven] using hx

theorem BackAndForth.mem_attemptTree
    {L : CountableRelationalLanguage} {M N : Structures L}
    {a : Ordinal.{0}} {s : List ℕ}
    (h : BackAndForth M N a (pairsFrom 0 s)) : attemptTree M N s = true :=
  decide_eq_true h.atomic

/-- A back-and-forth level is a lower bound for every strictly decreasing
ordinal assignment on the partial-isomorphism attempt tree. -/
theorem backAndForth_le_ordinal_assignment
    {L : CountableRelationalLanguage} (M N : Structures L)
    (ρ : RootedTrees.Nodes (attemptTree M N) → Ordinal.{0})
    (hρ : ∀ s t, RootedTrees.Child s t → ρ s < ρ t)
    (a : Ordinal.{0}) (s : List ℕ)
    (h : BackAndForth M N a (pairsFrom 0 s)) :
    a ≤ ρ ⟨s,h.mem_attemptTree⟩ := by
  induction a using WellFoundedLT.induction generalizing s with
  | ind a IH =>
      by_contra hn
      have hlt : ρ ⟨s,h.mem_attemptTree⟩ < a := lt_of_not_ge hn
      obtain ⟨n,hchild⟩ := h.scheduled_extension s hlt
      have hle := IH (ρ ⟨s,h.mem_attemptTree⟩) hlt (s ++ [n]) hchild
      have hstrict := hρ ⟨s ++ [n],hchild.mem_attemptTree⟩
        ⟨s,h.mem_attemptTree⟩ ⟨n,rfl⟩
      exact (not_le_of_gt hstrict) hle

/-- A single back-and-forth equivalence at level `a` excludes every
well-founded height bound `a` on the complete attempt tree. -/
theorem not_bounded_attemptTree_of_backAndForth
    {L : CountableRelationalLanguage} {M N : Structures L} (a : Ordinal.{0})
    (h : BackAndForth M N a []) : ¬ RootedTrees.BoundedTree (attemptTree M N) a := by
  rintro ⟨ρ,hbound,hdecr⟩
  have h' : BackAndForth M N a (pairsFrom 0 []) := h
  have hle := backAndForth_le_ordinal_assignment M N ρ hdecr a [] h'
  exact (not_le_of_gt (hbound ⟨[],h'.mem_attemptTree⟩)) hle

end FSCofinality.PartialIso

end
end

-- Original module: FSCofinalityProof.PaddingBasics
section


set_option autoImplicit false
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq α
open Set Order

namespace FSCofinality.Padding

/-- The cutoff used in the fat-tree back-and-forth argument. -/
def cutoff (b : Ordinal.{0}) : Ordinal.{0} := Ordinal.omega0 * b

/-- Below the cutoff ranks must agree exactly; above it they may differ.
The top rank denotes an original vertex on an infinite branch. -/
def RankAgrees (b : Ordinal.{0}) (r s : WithTop Ordinal.{0}) : Prop :=
  r = s ∨ ((cutoff b : WithTop Ordinal.{0}) ≤ r ∧ (cutoff b : WithTop Ordinal.{0}) ≤ s)

theorem cutoff_mono {b d : Ordinal.{0}} (h : d ≤ b) : cutoff d ≤ cutoff b :=
  mul_le_mul_left' h Ordinal.omega0

theorem RankAgrees.mono {b d : Ordinal.{0}} {r s : WithTop Ordinal.{0}}
    (h : RankAgrees b r s) (hdb : d ≤ b) : RankAgrees d r s := by
  rcases h with h | ⟨hr,hs⟩
  · exact Or.inl h
  · have hcut : (cutoff d : WithTop Ordinal.{0}) ≤ (cutoff b : WithTop Ordinal.{0}) :=
      WithTop.coe_le_coe.mpr (cutoff_mono hdb)
    exact Or.inr ⟨hcut.trans hr,hcut.trans hs⟩

/-- The underlying rooted colored tree, with finite depth to the root
and an ordinal or infinite rank at each vertex. -/
structure RankedTree where
  Vertex : Type 1
  root : Vertex
  parent : Vertex → Vertex
  color : Vertex → ℕ
  height : Vertex → ℕ
  rank : Vertex → WithTop Ordinal.{0}
  parent_root : parent root = root
  height_root : height root = 0
  height_zero : ∀ v, height v = 0 → v = root
  parent_height : ∀ v, v ≠ root → height (parent v)+1 = height v
  rank_parent : ∀ v, rank v ≤ rank (parent v)
  finite_rank_strict : ∀ v, v ≠ root → rank v ≠ ⊤ → rank v < rank (parent v)

/-- The reservoirs supply infinitely many fresh children of every
available smaller ordinal rank and color. This property will be proved
for the explicit canonical and padded trees. -/
def HasFatReservoirs (T : RankedTree) (a : Ordinal.{0}) : Prop :=
  ∀ (v : T.Vertex) (r : Ordinal.{0}), r < a →
    (r : WithTop Ordinal.{0}) < T.rank v → ∀ c : ℕ,
      Set.Infinite {w : T.Vertex | w ≠ T.root ∧ T.parent w = v ∧
        T.rank w = (r : WithTop Ordinal.{0}) ∧ T.color w = c}

/-- A finite ancestor-closed partial tree isomorphism with the required
rank comparison. The root pair is always present. -/
structure GoodPartial (T U : RankedTree) (b : Ordinal.{0}) where
  pairs : Finset (T.Vertex × U.Vertex)
  roots : (T.root,U.root) ∈ pairs
  bijective : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 = q.1 ↔ p.2 = q.2
  parents : ∀ p ∈ pairs, (T.parent p.1,U.parent p.2) ∈ pairs
  colors : ∀ p ∈ pairs, T.color p.1 = U.color p.2
  ranks : ∀ p ∈ pairs, RankAgrees b (T.rank p.1) (U.rank p.2)

def GoodPartial.source {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : Finset T.Vertex := f.pairs.image Prod.fst

def GoodPartial.target {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : Finset U.Vertex := f.pairs.image Prod.snd

def GoodPartial.lower {T U : RankedTree} {b d : Ordinal.{0}}
    (f : GoodPartial T U b) (hdb : d ≤ b) : GoodPartial T U d where
  pairs := f.pairs
  roots := f.roots
  bijective := f.bijective
  parents := f.parents
  colors := f.colors
  ranks := fun p hp => (f.ranks p hp).mono hdb

theorem GoodPartial.root_mem_source {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : T.root ∈ f.source :=
  Finset.mem_image.mpr ⟨(T.root,U.root),f.roots,rfl⟩

theorem GoodPartial.root_mem_target {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : U.root ∈ f.target :=
  Finset.mem_image.mpr ⟨(T.root,U.root),f.roots,rfl⟩

theorem GoodPartial.parent_mem_source {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) {v : T.Vertex} (hv : v ∈ f.source) :
    T.parent v ∈ f.source := by
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨(T.parent x,U.parent y),f.parents (x,y) hxy,rfl⟩

theorem GoodPartial.parent_mem_target {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) {v : U.Vertex} (hv : v ∈ f.target) :
    U.parent v ∈ f.target := by
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨(T.parent x,U.parent y),f.parents (x,y) hxy,rfl⟩

/-- Adding a fresh child pair preserves the complete finite tree
matching. Its parents must already be matched. -/
def GoodPartial.extend {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) (y : U.Vertex)
    (hx : x ∉ f.source) (hy : y ∉ f.target)
    (hparent : (T.parent x,U.parent y) ∈ f.pairs)
    (hcolor : T.color x = U.color y)
    (hrank : RankAgrees b (T.rank x) (U.rank y)) : GoodPartial T U b where
  pairs := insert (x,y) f.pairs
  roots := Finset.mem_insert_of_mem f.roots
  bijective := by
    intro p hp q hq
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · exact ⟨fun _ => rfl,fun _ => rfl⟩
      · have hxq : x ≠ q.1 := fun h => hx (h.symm ▸ Finset.mem_image.mpr ⟨q,hq,rfl⟩)
        have hyq : y ≠ q.2 := fun h => hy (h.symm ▸ Finset.mem_image.mpr ⟨q,hq,rfl⟩)
        exact ⟨fun h => False.elim (hxq h),fun h => False.elim (hyq h)⟩
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · have hpx : p.1 ≠ x := fun h => hx (h ▸ Finset.mem_image.mpr ⟨p,hp,rfl⟩)
        have hpy : p.2 ≠ y := fun h => hy (h ▸ Finset.mem_image.mpr ⟨p,hp,rfl⟩)
        exact ⟨fun h => False.elim (hpx h),fun h => False.elim (hpy h)⟩
      · exact f.bijective p hp q hq
  parents := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_insert_of_mem hparent
    · exact Finset.mem_insert_of_mem (f.parents p hp)
  colors := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hcolor
    · exact f.colors p hp
  ranks := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hrank
    · exact f.ranks p hp

/-- An explicit fresh reservoir point exists outside every finite
forbidden range. -/
theorem exists_fresh_child {U : RankedTree} {a : Ordinal.{0}}
    (hU : HasFatReservoirs U a) (v : U.Vertex) (r : Ordinal.{0})
    (hra : r < a) (hrv : (r : WithTop Ordinal.{0}) < U.rank v)
    (c : ℕ) (forbidden : Finset U.Vertex) :
    ∃ w : U.Vertex, w ∉ forbidden ∧ w ≠ U.root ∧ U.parent w = v ∧
      U.rank w = (r : WithTop Ordinal.{0}) ∧ U.color w = c := by
  obtain ⟨w,hw,hwf⟩ := (hU v r hra hrv c).exists_notMem_finset forbidden
  exact ⟨w,hwf,hw⟩

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingLanguage
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.Padding

/-- One fixed relational language for rooted colored predecessor trees:
one root predicate, the predecessor graph, and countably many colors. -/
def treeLanguage : CountableRelationalLanguage where
  Symbol := Unit ⊕ (Unit ⊕ ℕ)
  arity := fun s => match s with
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl _) => 2
    | Sum.inr (Sum.inr _) => 1
  countable := inferInstance

def code (T : RankedTree) (e : ℕ ≃ T.Vertex) : Structures treeLanguage :=
  fun ⟨s,a⟩ => match s with
    | Sum.inl _ => decide (e (a ⟨0,by simp [treeLanguage]⟩) = T.root)
    | Sum.inr (Sum.inl _) => decide
        (T.parent (e (a ⟨0,by simp [treeLanguage]⟩)) = e (a ⟨1,by simp [treeLanguage]⟩))
    | Sum.inr (Sum.inr c) => decide (T.color (e (a ⟨0,by simp [treeLanguage]⟩)) = c)

theorem GoodPartial.parent_iff {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) {p q : T.Vertex × U.Vertex}
    (hp : p ∈ f.pairs) (hq : q ∈ f.pairs) :
    T.parent p.1 = q.1 ↔ U.parent p.2 = q.2 :=
  f.bijective _ (f.parents p hp) q hq

theorem GoodPartial.root_iff {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) {p : T.Vertex × U.Vertex} (hp : p ∈ f.pairs) :
    p.1 = T.root ↔ p.2 = U.root := f.bijective p hp _ f.roots

/-- Ancestor closure is sufficient to preserve every atomic relation
in the fixed tree language. -/
theorem GoodPartial.atomicCompatible {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (eT : ℕ ≃ T.Vertex) (eU : ℕ ≃ U.Vertex)
    (R : Set (ℕ × ℕ)) (hR : ∀ p ∈ R, (eT p.1,eU p.2) ∈ f.pairs) :
    PartialIso.AtomicCompatible (code T eT) (code U eU) R := by
  refine ⟨?_,?_⟩
  · intro p hp q hq
    exact eT.injective.eq_iff.symm.trans
      ((f.bijective _ (hR p hp) _ (hR q hq)).trans eU.injective.eq_iff)
  · intro s a ha
    rcases s with _ | (_ | c)
    · change (Fin 1 → ℕ × ℕ) at a
      change (∀ i : Fin 1, a i ∈ R) at ha
      simp only [code,decide_eq_decide]
      exact f.root_iff (hR (a 0) (ha 0))
    · change (Fin 2 → ℕ × ℕ) at a
      change (∀ i : Fin 2, a i ∈ R) at ha
      simp only [code,decide_eq_decide]
      exact f.parent_iff (hR (a 0) (ha 0)) (hR (a 1) (ha 1))
    · change (Fin 1 → ℕ × ℕ) at a
      change (∀ i : Fin 1, a i ∈ R) at ha
      simp only [code]
      change decide (T.color (eT (a 0).1) = c) = decide (U.color (eU (a 0).2) = c)
      have hc : T.color (eT (a 0).1) = U.color (eU (a 0).2) :=
        f.colors _ (hR (a 0) (ha 0))
      rw [hc]

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingIsomorphism
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

structure TreeIso (T U : RankedTree) where
  equiv : T.Vertex ≃ U.Vertex
  roots : equiv T.root = U.root
  parents : ∀ v, equiv (T.parent v) = U.parent (equiv v)
  colors : ∀ v, U.color (equiv v) = T.color v

/-- The native countable-structure code retains the actual rooted
colored predecessor-tree isomorphism. -/
theorem treeIso_of_code_isomorphic
    (T U : RankedTree) (eT : ℕ ≃ T.Vertex) (eU : ℕ ≃ U.Vertex)
    (h : Isomorphic (code T eT) (code U eU)) : Nonempty (TreeIso T U) := by
  obtain ⟨e,he⟩ := h
  let φ : T.Vertex ≃ U.Vertex := (eT.symm.trans e).trans eU
  have hroot (n : ℕ) : eT n = T.root ↔ eU (e n) = U.root := by
    have hh := he (Sum.inl ()) (fun _ => n)
    simpa only [code,decide_eq_decide,Function.comp_apply] using hh
  have hparent (n m : ℕ) : T.parent (eT n) = eT m ↔ U.parent (eU (e n)) = eU (e m) := by
    let a : Fin (treeLanguage.arity (Sum.inr (Sum.inl ()))) → ℕ :=
      fun i => if i.val = 0 then n else m
    have hh := he (Sum.inr (Sum.inl ())) a
    simpa [code,a,Function.comp_def] using hh
  have hcolor (n c : ℕ) : T.color (eT n) = c ↔ U.color (eU (e n)) = c := by
    have hh := he (Sum.inr (Sum.inr c)) (fun _ => n)
    simpa only [code,decide_eq_decide,Function.comp_apply] using hh
  refine ⟨⟨φ,?_,?_,?_⟩⟩
  · exact (hroot (eT.symm T.root)).mp (eT.apply_symm_apply _)
  · intro v
    have hp := (hparent (eT.symm v) (eT.symm (T.parent v))).mp (by simp)
    exact hp.symm
  · intro v
    exact (hcolor (eT.symm v) (T.color v)).mp (by simp)

theorem code_isomorphic_of_treeIso
    (T U : RankedTree) (eT : ℕ ≃ T.Vertex) (eU : ℕ ≃ U.Vertex) (e : TreeIso T U) :
    Isomorphic (code T eT) (code U eU) := by
  let q : ℕ ≃ ℕ := (eT.trans e.equiv).trans eU.symm
  have hq (n : ℕ) : eU (q n) = e.equiv (eT n) := by simp only [q,Equiv.trans_apply,Equiv.apply_symm_apply]
  refine ⟨q,fun s a => ?_⟩
  rcases s with _ | (_ | c)
  · simp only [code,Function.comp_apply]
    apply decide_eq_decide.mpr
    rw [hq]
    rw [← e.roots]
    exact e.equiv.injective.eq_iff.symm
  · simp only [code,Function.comp_apply]
    apply decide_eq_decide.mpr
    rw [hq,hq,← e.parents]
    exact e.equiv.injective.eq_iff.symm
  · simp only [code,Function.comp_apply]
    apply decide_eq_decide.mpr
    rw [hq,e.colors]

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingAncestors
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

theorem RankedTree.height_iterate_parent (T : RankedTree) (v : T.Vertex)
    (n : ℕ) (hn : n ≤ T.height v) :
    T.height ((T.parent^[n]) v) = T.height v-n := by
  induction n with
  | zero => simp
  | succ n IH =>
      have hi := IH (by omega)
      rw [Function.iterate_succ_apply']
      have hneq : (T.parent^[n]) v ≠ T.root := by
        intro heq
        rw [heq,T.height_root] at hi
        omega
      have hp := T.parent_height ((T.parent^[n]) v) hneq
      omega

theorem RankedTree.iterate_parent_height (T : RankedTree) (v : T.Vertex) :
    (T.parent^[T.height v]) v = T.root :=
  T.height_zero _ (by simpa using T.height_iterate_parent v (T.height v) le_rfl)

theorem GoodPartial.exists_mapped_ancestor {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) :
    ∃ n : ℕ, (T.parent^[n]) x ∈ f.source :=
  ⟨T.height x,by rw [T.iterate_parent_height]; exact f.root_mem_source⟩

/-- The first already matched ancestor separates a new finite path
from the ancestor-closed domain of an existing partial map. -/
def GoodPartial.firstMappedAncestorDepth {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) : ℕ := by
  classical
  exact Nat.find (f.exists_mapped_ancestor x)

theorem GoodPartial.firstMappedAncestor_mem {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) :
    (T.parent^[f.firstMappedAncestorDepth x]) x ∈ f.source := by
  classical
  exact Nat.find_spec (f.exists_mapped_ancestor x)

theorem GoodPartial.before_firstMappedAncestor {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) {n : ℕ}
    (hn : n < f.firstMappedAncestorDepth x) : (T.parent^[n]) x ∉ f.source := by
  classical
  exact Nat.find_min (f.exists_mapped_ancestor x) hn

/-- The reservoir argument for one fresh edge, with its ordinal rank
chosen explicitly by the finite-path rank template. -/
theorem exists_one_edge_extension
    {T U : RankedTree} {a b : Ordinal.{0}}
    (hU : HasFatReservoirs U a) (f : GoodPartial T U b)
    (x : T.Vertex) (hx : x ∉ f.source) (y : U.Vertex)
    (hparent : (T.parent x,y) ∈ f.pairs)
    (r : Ordinal.{0}) (hra : r < a)
    (hry : (r : WithTop Ordinal.{0}) < U.rank y)
    (hrank : RankAgrees b (T.rank x) (r : WithTop Ordinal.{0})) :
    ∃ g : GoodPartial T U b, f.pairs ⊆ g.pairs ∧ x ∈ g.source := by
  classical
  obtain ⟨w,hwfresh,_,hwparent,hwrank,hwcolor⟩ :=
    exists_fresh_child hU y r hra hry (T.color x) f.target
  have hp : (T.parent x,U.parent w) ∈ f.pairs := by rwa [hwparent]
  have hr : RankAgrees b (T.rank x) (U.rank w) := by rwa [hwrank]
  let g := f.extend x w hx hwfresh hp hwcolor.symm hr
  refine ⟨g,?_,?_⟩
  · exact Finset.subset_insert (x,w) f.pairs
  · exact Finset.mem_image.mpr ⟨(x,w),Finset.mem_insert_self _ _,rfl⟩

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingCanonical
section


set_option autoImplicit false
noncomputable section
open Set

namespace FSCofinality.Padding

/-- A vertex of the canonical fat tree. Each descent chooses a smaller
ordinal rank, a color, and an independent multiplicity index. -/
inductive FatNode : Ordinal.{0} → Type 1
  | root {a : Ordinal.{0}} : FatNode a
  | descend {a : Ordinal.{0}} (r : a.ToType) (color copy : ℕ)
      (sub : FatNode (r : Ordinal.{0})) : FatNode a

namespace FatNode

def rank {a : Ordinal.{0}} : FatNode a → Ordinal.{0}
  | root => a
  | descend _ _ _ sub => rank sub

def height {a : Ordinal.{0}} : FatNode a → ℕ
  | root => 0
  | descend _ _ _ sub => height sub+1

def color {a : Ordinal.{0}} (rootColor : ℕ) : FatNode a → ℕ
  | root => rootColor
  | descend _ c _ sub => color c sub

def parent {a : Ordinal.{0}} : FatNode a → FatNode a
  | root => root
  | descend _ _ _ root => root
  | descend r c k (descend s d l sub) => descend r c k (parent (descend s d l sub))

theorem rank_le {a : Ordinal.{0}} (v : FatNode a) : rank v ≤ a := by
  induction v with
  | root => exact le_rfl
  | @descend a r c k sub IH => exact IH.trans r.toOrd.property.le

theorem rank_lt_of_ne_root {a : Ordinal.{0}} (v : FatNode a) (hv : v ≠ root) :
    rank v < a := by
  cases v with
  | root => exact False.elim (hv rfl)
  | descend r c k sub => exact (rank_le sub).trans_lt r.toOrd.property

theorem height_pos_of_ne_root {a : Ordinal.{0}} (v : FatNode a) (hv : v ≠ root) :
    0 < height v := by
  cases v with
  | root => exact False.elim (hv rfl)
  | descend r c k sub => exact Nat.zero_lt_succ _

theorem height_zero {a : Ordinal.{0}} (v : FatNode a) (hv : height v = 0) : v = root := by
  cases v with
  | root => rfl
  | descend r c k sub => simp [height] at hv

theorem parent_height {a : Ordinal.{0}} (v : FatNode a) (hv : v ≠ root) :
    height (parent v)+1 = height v := by
  induction v with
  | root => exact False.elim (hv rfl)
  | @descend a r c k sub IH =>
      cases sub with
      | root => rfl
      | descend s d l sub =>
          have hsub : (descend s d l sub : FatNode (r : Ordinal.{0})) ≠ root := by
            intro h; cases h
          simpa only [parent,height] using congrArg (fun n : ℕ => n+1) (IH hsub)

theorem rank_parent_lt {a : Ordinal.{0}} (v : FatNode a) (hv : v ≠ root) :
    rank v < rank (parent v) := by
  induction v with
  | root => exact False.elim (hv rfl)
  | @descend a r c k sub IH =>
      cases sub with
      | root => exact r.toOrd.property
      | descend s d l sub =>
          have hsub : (descend s d l sub : FatNode (r : Ordinal.{0})) ≠ root := by
            intro h; cases h
          exact IH hsub

def tree (a : Ordinal.{0}) (rootColor : ℕ) : RankedTree where
  Vertex := FatNode a
  root := root
  parent := parent
  color := color rootColor
  height := height
  rank := fun v => (rank v : WithTop Ordinal.{0})
  parent_root := rfl
  height_root := rfl
  height_zero := height_zero
  parent_height := parent_height
  rank_parent := by
    intro v
    by_cases hv : v = root
    · subst v; exact le_rfl
    · exact (WithTop.coe_lt_coe.mpr (rank_parent_lt v hv)).le
  finite_rank_strict := by
    intro v hv _
    exact WithTop.coe_lt_coe.mpr (rank_parent_lt v hv)

/-- Append a new reservoir child at the current vertex. -/
def child {a : Ordinal.{0}} : (v : FatNode a) →
    (r : Ordinal.{0}) → r < rank v → ℕ → ℕ → FatNode a
  | root, r, hr, c, k => descend (Ordinal.ToType.mk ⟨r,hr⟩) c k root
  | descend s d l sub, r, hr, c, k => descend s d l (child sub r hr c k)

theorem child_ne_root {a : Ordinal.{0}} (v : FatNode a)
    (r : Ordinal.{0}) (hr : r < rank v) (c k : ℕ) : child v r hr c k ≠ root := by
  cases v <;> simp only [child] <;> intro h <;> cases h

theorem parent_descend {a : Ordinal.{0}} (s : a.ToType) (c k : ℕ)
    (v : FatNode (s : Ordinal.{0})) (hv : v ≠ root) :
    parent (descend s c k v) = descend s c k (parent v) := by
  cases v with
  | root => exact False.elim (hv rfl)
  | descend t d l sub => rfl

theorem parent_child {a : Ordinal.{0}} (v : FatNode a)
    (r : Ordinal.{0}) (hr : r < rank v) (c k : ℕ) : parent (child v r hr c k) = v := by
  induction v with
  | root => rfl
  | descend s d l sub IH =>
      rw [child,parent_descend s d l _ (child_ne_root sub r hr c k),IH]

theorem rank_child {a : Ordinal.{0}} (v : FatNode a)
    (r : Ordinal.{0}) (hr : r < rank v) (c k : ℕ) : rank (child v r hr c k) = r := by
  induction v with
  | root => simp [child,rank,Ordinal.ToType.toOrd]
  | descend s d l sub IH => exact IH hr

theorem color_child {a : Ordinal.{0}} (v : FatNode a)
    (r : Ordinal.{0}) (hr : r < rank v) (c k rootColor : ℕ) :
    color rootColor (child v r hr c k) = c := by
  induction v generalizing rootColor with
  | root => rfl
  | descend s d l sub IH => exact IH hr d

theorem child_copy_injective {a : Ordinal.{0}} (v : FatNode a)
    (r : Ordinal.{0}) (hr : r < rank v) (c : ℕ) :
    Function.Injective (fun k : ℕ => child v r hr c k) := by
  induction v with
  | root => intro k l h; simpa [child,descend.injEq] using h
  | descend s d l sub IH =>
      intro k l h
      apply IH hr
      simpa [child,descend.injEq] using h

/-- Every canonical fat tree has all the reservoirs used by the
finite-path extension argument. -/
theorem hasFatReservoirs (a : Ordinal.{0}) (rootColor : ℕ) :
    HasFatReservoirs (tree a rootColor) a := by
  intro v r _ hr c
  have hrv : r < rank v := WithTop.coe_lt_coe.mp hr
  have hinf : Set.Infinite (Set.range (fun k : ℕ => child v r hrv c k)) :=
    Set.infinite_range_of_injective (child_copy_injective v r hrv c)
  apply hinf.mono
  rintro w ⟨k,rfl⟩
  exact ⟨child_ne_root v r hrv c k,parent_child v r hrv c k,
    by simp only [tree,rank_child],color_child v r hrv c k rootColor⟩

def split {a : Ordinal.{0}} : FatNode a →
    Unit ⊕ (Σ r : a.ToType, ℕ × ℕ × FatNode (r : Ordinal.{0}))
  | root => Sum.inl ()
  | descend r c k sub => Sum.inr ⟨r,c,k,sub⟩

def join {a : Ordinal.{0}} :
    Unit ⊕ (Σ r : a.ToType, ℕ × ℕ × FatNode (r : Ordinal.{0})) → FatNode a
  | Sum.inl _ => root
  | Sum.inr ⟨r,c,k,sub⟩ => descend r c k sub

theorem join_split {a : Ordinal.{0}} (v : FatNode a) : join (split v) = v := by
  cases v <;> rfl

/-- Each canonical fat tree at a countable ordinal has countably many
vertices, despite its ordinal-indexed semantic presentation. -/
theorem countable (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) : Countable (FatNode a) := by
  revert ha
  induction a using WellFoundedLT.induction with
  | ind a IH =>
      intro ha
      haveI : Countable a.ToType := Cardinal.mk_le_aleph0_iff.mp (by
        rw [Cardinal.mk_toType]
        exact Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp ha))
      letI : ∀ r : a.ToType, Countable (FatNode (r : Ordinal.{0})) := fun r =>
        IH (r : Ordinal.{0}) r.toOrd.property (r.toOrd.property.trans ha)
      have hi : Function.Injective (@split a) :=
        Function.LeftInverse.injective (fun v => join_split v)
      exact hi.countable

end FatNode
end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingPaddedTree
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.Padding

/-- The fixed domain of a padded tuple tree: original finite tuples,
and nonroot canonical-fat vertices attached below each tuple. -/
def PaddedNode (a : Ordinal.{0}) :=
  List ℕ ⊕ (List ℕ × {v : FatNode a // v ≠ FatNode.root})

namespace PaddedNode

def root (a : Ordinal.{0}) : PaddedNode a := Sum.inl []

def parent {a : Ordinal.{0}} : PaddedNode a → PaddedNode a
  | Sum.inl s => Sum.inl s.dropLast
  | Sum.inr (s,v) => if h : FatNode.parent v.val = FatNode.root then Sum.inl s
      else Sum.inr (s,⟨FatNode.parent v.val,h⟩)

def height {a : Ordinal.{0}} : PaddedNode a → ℕ
  | Sum.inl s => s.length
  | Sum.inr (s,v) => s.length+FatNode.height v.val

def rank {a : Ordinal.{0}} : PaddedNode a → WithTop Ordinal.{0}
  | Sum.inl _ => ⊤
  | Sum.inr (_,v) => (FatNode.rank v.val : WithTop Ordinal.{0})

def color {a : Ordinal.{0}} (originalColor : List ℕ → ℕ) : PaddedNode a → ℕ
  | Sum.inl s => originalColor s
  | Sum.inr (_,v) => FatNode.color 0 v.val

theorem height_zero {a : Ordinal.{0}} (v : PaddedNode a) (hv : height v = 0) : v = root a := by
  cases v with
  | inl s =>
      have hs : s = [] := List.length_eq_zero_iff.mp hv
      rw [hs]
      rfl
  | inr v =>
      have hp := FatNode.height_pos_of_ne_root v.2.val v.2.property
      simp only [height] at hv
      omega

theorem parent_height {a : Ordinal.{0}} (v : PaddedNode a) (hv : v ≠ root a) :
    height (parent v)+1 = height v := by
  cases v with
  | inl s =>
      have hs : s ≠ [] := fun hs => hv (by rw [hs]; rfl)
      have hlen : 0 < s.length := List.length_pos_iff.mpr hs
      simp only [parent,height,List.length_dropLast]
      omega
  | inr v =>
      have hp := FatNode.parent_height v.2.val v.2.property
      dsimp only [parent]
      split_ifs with h
      · rw [h] at hp
        simp only [FatNode.height] at hp
        simp only [height]
        omega
      · simp only [height]
        omega

theorem rank_parent {a : Ordinal.{0}} (v : PaddedNode a) : rank v ≤ rank (parent v) := by
  cases v with
  | inl s => exact le_rfl
  | inr v =>
      have hp := FatNode.rank_parent_lt v.2.val v.2.property
      dsimp only [parent]
      split_ifs
      · exact le_top
      · exact (WithTop.coe_lt_coe.mpr hp).le

theorem finite_rank_strict {a : Ordinal.{0}} (v : PaddedNode a)
    (_ : v ≠ root a) (hv : rank v ≠ ⊤) : rank v < rank (parent v) := by
  cases v with
  | inl s => exact False.elim (hv rfl)
  | inr v =>
      have hp := FatNode.rank_parent_lt v.2.val v.2.property
      dsimp only [parent]
      split_ifs
      · exact WithTop.coe_lt_top _
      · exact WithTop.coe_lt_coe.mpr hp

def tree (a : Ordinal.{0}) (originalColor : List ℕ → ℕ) : RankedTree where
  Vertex := PaddedNode a
  root := root a
  parent := parent
  color := color originalColor
  height := height
  rank := rank
  parent_root := rfl
  height_root := rfl
  height_zero := height_zero
  parent_height := parent_height
  rank_parent := rank_parent
  finite_rank_strict := finite_rank_strict

def embed {a : Ordinal.{0}} (s : List ℕ) (v : FatNode a) : PaddedNode a :=
  if h : v = FatNode.root then Sum.inl s else Sum.inr (s,⟨v,h⟩)

@[simp] theorem embed_root {a : Ordinal.{0}} (s : List ℕ) :
    embed s (FatNode.root : FatNode a) = Sum.inl s := by simp [embed]

theorem embed_injective {a : Ordinal.{0}} (s : List ℕ) :
    Function.Injective (embed (a := a) s) := by
  intro v w h
  by_cases hv : v = FatNode.root <;> by_cases hw : w = FatNode.root
  · exact hv.trans hw.symm
  · simp [embed,hv,hw] at h
  · simp [embed,hv,hw] at h
  · simp only [embed,dif_neg hv,dif_neg hw] at h
    exact congrArg Subtype.val (congrArg Prod.snd (Sum.inr.inj h))

theorem embed_ne_root {a : Ordinal.{0}} (s : List ℕ) (v : FatNode a)
    (hv : v ≠ FatNode.root) : embed s v ≠ root a := by simp [embed,hv,root]

theorem parent_embed {a : Ordinal.{0}} (s : List ℕ) (v : FatNode a)
    (hv : v ≠ FatNode.root) : parent (embed s v) = embed s (FatNode.parent v) := by
  simp only [embed,dif_neg hv,parent]

theorem rank_embed {a : Ordinal.{0}} (s : List ℕ) (v : FatNode a)
    (hv : v ≠ FatNode.root) : rank (embed s v) = (FatNode.rank v : WithTop Ordinal.{0}) := by
  simp [embed,hv,rank]

theorem color_embed {a : Ordinal.{0}} (C : List ℕ → ℕ) (s : List ℕ) (v : FatNode a)
    (hv : v ≠ FatNode.root) : color C (embed s v) = FatNode.color 0 v := by
  simp [embed,hv,color]

/-- Padding adds the same fat reservoirs below every original vertex
and retains them below every attached canonical vertex. -/
theorem hasFatReservoirs (a : Ordinal.{0}) (C : List ℕ → ℕ) :
    HasFatReservoirs (tree a C) a := by
  intro v r hra hr c
  cases v with
  | inl s =>
      let child := fun k : ℕ => FatNode.child (FatNode.root : FatNode a) r hra c k
      have hne (k : ℕ) : child k ≠ FatNode.root := FatNode.child_ne_root _ _ _ _ _
      have hinf : Set.Infinite (Set.range (fun k : ℕ => embed s (child k))) :=
        Set.infinite_range_of_injective ((embed_injective s).comp
          (FatNode.child_copy_injective (FatNode.root : FatNode a) r hra c))
      apply hinf.mono
      rintro w ⟨k,rfl⟩
      refine ⟨embed_ne_root s _ (hne k),?_,?_,?_⟩
      · exact (parent_embed s _ (hne k)).trans (by simp [child,FatNode.parent_child])
      · rw [show (tree a C).rank = rank from rfl,rank_embed s _ (hne k)]
        rw [FatNode.rank_child]
      · rw [show (tree a C).color = color C from rfl,color_embed C s _ (hne k)]
        exact FatNode.color_child (FatNode.root : FatNode a) r hra c k 0
  | inr v =>
      have hrv : r < FatNode.rank v.2.val := WithTop.coe_lt_coe.mp hr
      let child := fun k : ℕ => FatNode.child v.2.val r hrv c k
      have hne (k : ℕ) : child k ≠ FatNode.root := FatNode.child_ne_root _ _ _ _ _
      have hinf : Set.Infinite (Set.range (fun k : ℕ => embed v.1 (child k))) :=
        Set.infinite_range_of_injective ((embed_injective v.1).comp
          (FatNode.child_copy_injective _ r hrv c))
      apply hinf.mono
      rintro w ⟨k,rfl⟩
      refine ⟨embed_ne_root v.1 _ (hne k),?_,?_,?_⟩
      · exact (parent_embed v.1 _ (hne k)).trans
          (by simp [child,FatNode.parent_child,embed,v.2.property])
      · rw [show (tree a C).rank = rank from rfl,rank_embed v.1 _ (hne k)]
        rw [FatNode.rank_child]
      · rw [show (tree a C).color = color C from rfl,color_embed C v.1 _ (hne k)]
        exact FatNode.color_child _ r hrv c k 0

theorem countable (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) : Countable (PaddedNode a) := by
  letI := FatNode.countable a ha
  unfold PaddedNode
  infer_instance

end PaddedNode
end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingPath
section


set_option autoImplicit false
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq α
open Set

namespace FSCofinality.Padding

/-- A finite downward path with explicit target ranks. -/
def PathTemplate (T : RankedTree) (a d : Ordinal.{0}) :
    T.Vertex → WithTop Ordinal.{0} → List (T.Vertex × Ordinal.{0}) → Prop
  | _, _, [] => True
  | anchor, anchorRank, (v,r) :: rest =>
      T.parent v = anchor ∧ r < a ∧ (r : WithTop Ordinal.{0}) < anchorRank ∧
      RankAgrees d (T.rank v) (r : WithTop Ordinal.{0}) ∧
      PathTemplate T a d v (r : WithTop Ordinal.{0}) rest

theorem GoodPartial.source_extend {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) (y : U.Vertex)
    (hx : x ∉ f.source) (hy : y ∉ f.target)
    (hp : (T.parent x,U.parent y) ∈ f.pairs)
    (hc : T.color x = U.color y) (hr : RankAgrees b (T.rank x) (U.rank y)) :
    (f.extend x y hx hy hp hc hr).source = insert x f.source := by
  classical
  exact Finset.image_insert (Prod.fst : T.Vertex × U.Vertex → T.Vertex) (x,y) f.pairs

/-- A whole fresh ancestor path can be realized, preserving all old
pairs, once its decreasing rank template is specified. Infinitely many
copies provide fresh vertices at each step. -/
theorem extend_path
    {T U : RankedTree} {a d : Ordinal.{0}}
    (hU : HasFatReservoirs U a) (f : GoodPartial T U d)
    (anchor : T.Vertex) (targetAnchor : U.Vertex)
    (hanchor : (anchor,targetAnchor) ∈ f.pairs)
    (path : List (T.Vertex × Ordinal.{0}))
    (ht : PathTemplate T a d anchor (U.rank targetAnchor) path)
    (hfresh : ∀ p ∈ path, p.1 ∉ f.source)
    (hnodup : (path.map Prod.fst).Nodup) :
    ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧
      ∀ p ∈ path, ∃ y : U.Vertex, (p.1,y) ∈ g.pairs ∧ U.rank y = (p.2 : WithTop Ordinal.{0}) := by
  classical
  induction path generalizing f anchor targetAnchor with
  | nil => exact ⟨f,(fun _ h => h),fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons p rest IH =>
      obtain ⟨v,r⟩ := p
      obtain ⟨hp,hra,hra',hr,htail⟩ := ht
      obtain ⟨w,hwfresh,_,hwparent,hwrank,hwcolor⟩ :=
        exists_fresh_child hU targetAnchor r hra hra' (T.color v) f.target
      have hvfresh : v ∉ f.source := hfresh (v,r) (List.mem_cons_self)
      have hparent : (T.parent v,U.parent w) ∈ f.pairs := by
        simpa only [hp,hwparent] using hanchor
      have hrank : RankAgrees d (T.rank v) (U.rank w) := by rwa [hwrank]
      let f' := f.extend v w hvfresh hwfresh hparent hwcolor.symm hrank
      have hfsub : f.pairs ⊆ f'.pairs := Finset.subset_insert (v,w) f.pairs
      have hnew : (v,w) ∈ f'.pairs := Finset.mem_insert_self _ _
      have htail' : PathTemplate T a d v (U.rank w) rest := by rwa [hwrank]
      have hfresh' : ∀ p ∈ rest, p.1 ∉ f'.source := by
        intro p hpRest hpSource
        rw [GoodPartial.source_extend] at hpSource
        rcases Finset.mem_insert.mp hpSource with hpEq | hpOld
        · have hvnot : v ∉ rest.map Prod.fst := (List.nodup_cons.mp hnodup).1
          exact hvnot (hpEq ▸ List.mem_map.mpr ⟨p,hpRest,rfl⟩)
        · exact hfresh p (List.mem_cons_of_mem _ hpRest) hpOld
      have hnrest : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hnodup).2
      obtain ⟨g,hg,hrg⟩ := IH f' v w hnew htail' hfresh' hnrest
      refine ⟨g,hfsub.trans hg,fun p hpMem => ?_⟩
      rcases List.mem_cons.mp hpMem with rfl | hpMem
      · exact ⟨w,hg hnew,hwrank⟩
      · exact hrg p hpMem

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingTemplate
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

def ancestorPath (T : RankedTree) (x : T.Vertex) (σ : ℕ → Ordinal.{0}) (m : ℕ) :
    List (T.Vertex × Ordinal.{0}) :=
  (List.range m).reverse.map (fun j => ((T.parent^[j]) x,σ j))

theorem ancestorPath_succ (T : RankedTree) (x : T.Vertex) (σ : ℕ → Ordinal.{0}) (m : ℕ) :
    ancestorPath T x σ (m+1) = ((T.parent^[m]) x,σ m) :: ancestorPath T x σ m := by
  simp [ancestorPath,List.range_succ,List.reverse_append]

/-- Strictly increasing ranks indexed from the leaf give the required
decreasing template when the ancestor path is read from its anchor. -/
theorem ancestorPath_template
    (T : RankedTree) (a d : Ordinal.{0}) (x : T.Vertex) (σ : ℕ → Ordinal.{0})
    (m : ℕ) (anchorRank : WithTop Ordinal.{0})
    (ha : ∀ j < m, σ j < a)
    (hinc : ∀ j < m, σ j < σ (j+1))
    (hag : ∀ j < m, RankAgrees d (T.rank ((T.parent^[j]) x)) (σ j : WithTop Ordinal.{0}))
    (hanchor : (σ m : WithTop Ordinal.{0}) ≤ anchorRank) :
    PathTemplate T a d ((T.parent^[m]) x) anchorRank (ancestorPath T x σ m) := by
  induction m generalizing anchorRank with
  | zero => trivial
  | succ m IH =>
      rw [ancestorPath_succ]
      refine ⟨?_,ha m (by omega),?_,hag m (by omega),?_⟩
      · exact (Function.iterate_succ_apply' T.parent m x).symm
      · exact (WithTop.coe_lt_coe.mpr (hinc m (by omega))).trans_le hanchor
      · exact IH (σ m) (fun j hj => ha j (by omega))
          (fun j hj => hinc j (by omega)) (fun j hj => hag j (by omega)) le_rfl

theorem RankedTree.iterate_parent_injective_below_height
    (T : RankedTree) (x : T.Vertex) {i j : ℕ}
    (hi : i ≤ T.height x) (hj : j ≤ T.height x)
    (h : (T.parent^[i]) x = (T.parent^[j]) x) : i = j := by
  have hh := congrArg T.height h
  rw [T.height_iterate_parent x i hi,T.height_iterate_parent x j hj] at hh
  omega

theorem ancestorPath_nodup (T : RankedTree) (x : T.Vertex)
    (σ : ℕ → Ordinal.{0}) (m : ℕ) (hm : m ≤ T.height x) :
    ((ancestorPath T x σ m).map Prod.fst).Nodup := by
  rw [ancestorPath,List.map_map]
  apply List.Nodup.map_on ?_ (List.nodup_reverse.mpr
    (show (List.range m).Nodup from List.nodup_range))
  intro i hi j hj hij
  have hi' : i < m := List.mem_range.mp (List.mem_reverse.mp hi)
  have hj' : j < m := List.mem_range.mp (List.mem_reverse.mp hj)
  exact T.iterate_parent_injective_below_height x (by omega) (by omega) hij

theorem GoodPartial.firstMappedAncestorDepth_le_height
    {T U : RankedTree} {b : Ordinal.{0}} (f : GoodPartial T U b) (x : T.Vertex) :
    f.firstMappedAncestorDepth x ≤ T.height x := by
  classical
  apply Nat.find_min'
  rw [T.iterate_parent_height]
  exact f.root_mem_source

theorem ancestorPath_fresh {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (x : T.Vertex) (σ : ℕ → Ordinal.{0}) :
    ∀ p ∈ ancestorPath T x σ (f.firstMappedAncestorDepth x), p.1 ∉ f.source := by
  intro p hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
  exact f.before_firstMappedAncestor x (List.mem_range.mp (List.mem_reverse.mp hj))

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingOrdinalBasics
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.Padding

theorem RankAgrees.eq_of_lt_left {b : Ordinal.{0}} {r s : WithTop Ordinal.{0}}
    (h : RankAgrees b r s) (hr : r < (cutoff b : WithTop Ordinal.{0})) : r = s := by
  rcases h with heq | ⟨hhigh,_⟩
  · exact heq
  · exact False.elim ((not_lt_of_ge hhigh) hr)

theorem RankAgrees.high_right {b : Ordinal.{0}} {r s : WithTop Ordinal.{0}}
    (h : RankAgrees b r s) (hr : (cutoff b : WithTop Ordinal.{0}) ≤ r) :
    (cutoff b : WithTop Ordinal.{0}) ≤ s := by
  rcases h with heq | ⟨_,hs⟩
  · exact heq ▸ hr
  · exact hs

/-- The finite slack in a new path fits below every strictly later
omega-multiple cutoff. -/
theorem cutoff_add_nat_lt {d b : Ordinal.{0}} (hdb : d < b) (n : ℕ) :
    cutoff d + (n : Ordinal.{0}) < cutoff b := by
  calc
    cutoff d + (n : Ordinal.{0}) < cutoff d + Ordinal.omega0 :=
      (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 n)
    _ = cutoff (Order.succ d) := by simp only [cutoff,Ordinal.mul_succ]
    _ ≤ cutoff b := cutoff_mono (Order.succ_le_of_lt hdb)

def finiteOrdinal (r : WithTop Ordinal.{0}) : Ordinal.{0} :=
  @WithTop.untopD Ordinal.{0} 0 r

theorem coe_untopD_of_lt {r : WithTop Ordinal.{0}} {a : Ordinal.{0}}
    (hr : r < (a : WithTop Ordinal.{0})) : (finiteOrdinal r : WithTop Ordinal.{0}) = r := by
  rcases r with _ | r
  · exact False.elim ((not_lt_of_ge le_top) hr)
  · rfl

theorem RankedTree.rank_iterate_parent_monotone (T : RankedTree) (x : T.Vertex) :
    Monotone (fun n : ℕ => T.rank ((T.parent^[n]) x)) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [Function.iterate_succ_apply'] using T.rank_parent ((T.parent^[n]) x)

/-- The ordinal rank assigned to a new path vertex in the high-anchor
case. Low vertices retain their exact rank; high vertices use finite
slack above the new cutoff. -/
def pathRank (T : RankedTree) (x : T.Vertex) (d : Ordinal.{0}) (j : ℕ) : Ordinal.{0} :=
  if T.rank ((T.parent^[j]) x) < (cutoff d : WithTop Ordinal.{0}) then
    finiteOrdinal (T.rank ((T.parent^[j]) x)) else cutoff d+j

theorem pathRank_agrees (T : RankedTree) (x : T.Vertex) (d : Ordinal.{0}) (j : ℕ) :
    RankAgrees d (T.rank ((T.parent^[j]) x)) (pathRank T x d j : WithTop Ordinal.{0}) := by
  unfold pathRank
  split_ifs with hj
  · exact Or.inl (coe_untopD_of_lt hj).symm
  · exact Or.inr ⟨le_of_not_gt hj,WithTop.coe_le_coe.mpr (le_self_add)⟩

theorem pathRank_lt {T : RankedTree} (x : T.Vertex) {a b d : Ordinal.{0}}
    (hdb : d < b) (hba : cutoff b ≤ a) (j : ℕ) : pathRank T x d j < a := by
  unfold pathRank
  split_ifs with hj
  · have hco : (finiteOrdinal (T.rank ((T.parent^[j]) x)) : WithTop Ordinal.{0}) =
        T.rank ((T.parent^[j]) x) := coe_untopD_of_lt hj
    have hlt : finiteOrdinal (T.rank ((T.parent^[j]) x)) < cutoff d :=
      WithTop.coe_lt_coe.mp (by rwa [hco])
    exact hlt.trans_le ((cutoff_mono hdb.le).trans hba)
  · exact (cutoff_add_nat_lt hdb j).trans_le hba

theorem pathRank_lt_succ (T : RankedTree) (x : T.Vertex) (d : Ordinal.{0}) (j : ℕ)
    (hne : (T.parent^[j]) x ≠ T.root) : pathRank T x d j < pathRank T x d (j+1) := by
  have hp : T.rank ((T.parent^[j]) x) ≤ T.rank ((T.parent^[j+1]) x) :=
    T.rank_iterate_parent_monotone x (by omega)
  unfold pathRank
  by_cases hj : T.rank ((T.parent^[j]) x) < (cutoff d : WithTop Ordinal.{0})
  · have he : (finiteOrdinal (T.rank ((T.parent^[j]) x)) : WithTop Ordinal.{0}) =
        T.rank ((T.parent^[j]) x) := coe_untopD_of_lt hj
    by_cases hj' : T.rank ((T.parent^[j+1]) x) < (cutoff d : WithTop Ordinal.{0})
    · simp only [if_pos hj,if_pos hj']
      have he' := coe_untopD_of_lt hj'
      apply WithTop.coe_lt_coe.mp
      rw [he,he']
      have hfinite : T.rank ((T.parent^[j]) x) ≠ ⊤ := by
        intro htop
        rw [htop] at hj
        exact (not_lt_of_ge le_top) hj
      simpa only [Function.iterate_succ_apply'] using
        T.finite_rank_strict ((T.parent^[j]) x) hne hfinite
    · simp only [if_pos hj,if_neg hj']
      have hl : finiteOrdinal (T.rank ((T.parent^[j]) x)) < cutoff d :=
        WithTop.coe_lt_coe.mp (by rwa [he])
      exact hl.trans_le le_self_add
  · by_cases hj' : T.rank ((T.parent^[j+1]) x) < (cutoff d : WithTop Ordinal.{0})
    · exact False.elim (hj (hp.trans_lt hj'))
    · simp only [if_neg hj,if_neg hj']
      apply (add_lt_add_iff_left _).mpr
      exact_mod_cast Nat.lt_succ_self j

theorem pathRank_anchor_le {T : RankedTree} {x : T.Vertex} {b d : Ordinal.{0}}
    (hdb : d < b) (m : ℕ) (targetRank : WithTop Ordinal.{0})
    (hhigh : (cutoff b : WithTop Ordinal.{0}) ≤ T.rank ((T.parent^[m]) x))
    (hmatch : RankAgrees b (T.rank ((T.parent^[m]) x)) targetRank) :
    (pathRank T x d m : WithTop Ordinal.{0}) ≤ targetRank := by
  have htarget := hmatch.high_right hhigh
  have hnot : ¬ T.rank ((T.parent^[m]) x) < (cutoff d : WithTop Ordinal.{0}) := by
    apply not_lt_of_ge
    exact (WithTop.coe_le_coe.mpr (cutoff_mono hdb.le)).trans hhigh
  simp only [pathRank,if_neg hnot]
  exact (WithTop.coe_lt_coe.mpr (cutoff_add_nat_lt hdb m)).le.trans htarget

end FSCofinality.Padding



end
end

-- Original module: FSCofinalityProof.PaddingBranches
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

def HasInfiniteBranchFrom (T : RankedTree) (v : T.Vertex) : Prop :=
  ∃ f : ℕ → T.Vertex, f 0 = v ∧
    ∀ n, T.parent (f (n+1)) = f n ∧ f (n+1) ≠ f n

def TreeIso.symm {T U : RankedTree} (e : TreeIso T U) : TreeIso U T where
  equiv := e.equiv.symm
  roots := by
    apply e.equiv.injective
    simp only [Equiv.apply_symm_apply,e.roots]
  parents := by
    intro v
    apply e.equiv.injective
    simp only [Equiv.apply_symm_apply,e.parents]
  colors := by
    intro v
    simpa only [Equiv.apply_symm_apply] using (e.colors (e.equiv.symm v)).symm

theorem TreeIso.map_branch {T U : RankedTree} (e : TreeIso T U) {v : T.Vertex}
    (h : HasInfiniteBranchFrom T v) : HasInfiniteBranchFrom U (e.equiv v) := by
  obtain ⟨f,hf0,hf⟩ := h
  refine ⟨e.equiv ∘ f,congrArg e.equiv hf0,fun n => ?_⟩
  exact ⟨(e.parents (f (n+1))).symm.trans (congrArg e.equiv (hf n).1),
    fun h => (hf n).2 (e.equiv.injective h)⟩

/-- A finite ordinal rank excludes an infinite branch. -/
theorem no_branch_of_finite_rank (T : RankedTree) (v : T.Vertex)
    (hv : T.rank v ≠ ⊤) : ¬ HasInfiniteBranchFrom T v := by
  rintro ⟨f,hf0,hf⟩
  have hle : ∀ n, T.rank (f n) ≤ T.rank v := by
    intro n
    induction n with
    | zero => simpa only [hf0] using (le_rfl : T.rank v ≤ T.rank v)
    | succ n IH =>
        have hp : T.rank (f (n+1)) ≤ T.rank (f n) := by
          simpa only [(hf n).1] using T.rank_parent (f (n+1))
        exact hp.trans IH
  have hfinite (n : ℕ) : T.rank (f n) ≠ ⊤ := by
    intro ht
    have hh := hle n
    rw [ht] at hh
    exact hv (le_antisymm le_top hh)
  let σ : ℕ → Ordinal.{0} := fun n => finiteOrdinal (T.rank (f n))
  have hco (n : ℕ) : (σ n : WithTop Ordinal.{0}) = T.rank (f n) := by
    obtain ⟨r,hr⟩ := WithTop.ne_top_iff_exists.mp (hfinite n)
    change (finiteOrdinal (T.rank (f n)) : WithTop Ordinal.{0}) = T.rank (f n)
    rw [← hr]
    rfl
  have hdecr (n : ℕ) : σ (n+1) < σ n := by
    apply WithTop.coe_lt_coe.mp
    rw [hco (n+1),hco n]
    have hroot : f (n+1) ≠ T.root := by
      intro heq
      have hp : T.root = f n := by simpa only [heq,T.parent_root] using (hf n).1
      exact (hf n).2 (heq.trans hp)
    simpa only [(hf n).1] using T.finite_rank_strict (f (n+1)) hroot (hfinite (n+1))
  exact (not_acc_iff_exists_descending_chain.mpr ⟨σ,rfl,hdecr⟩) (Ordinal.lt_wf.apply (σ 0))

theorem PaddedNode.branch_from_original (a : Ordinal.{0}) (C : List ℕ → ℕ) (s : List ℕ) :
    HasInfiniteBranchFrom (PaddedNode.tree a C) (Sum.inl s) := by
  refine ⟨fun n => Sum.inl (s ++ List.replicate n 0),by simp,fun n => ⟨?_,?_⟩⟩
  · simp [PaddedNode.tree,PaddedNode.parent,List.replicate_succ',← List.append_assoc]
  · intro h
    have hh := congrArg PaddedNode.height h
    simp only [PaddedNode.height,List.length_append,List.length_replicate] at hh
    omega

/-- Original tuple vertices are intrinsically the vertices on infinite
branches. Hence padding is faithful under actual tree isomorphisms. -/
theorem PaddedNode.branch_iff_original (a : Ordinal.{0}) (C : List ℕ → ℕ) (v : PaddedNode a) :
    HasInfiniteBranchFrom (PaddedNode.tree a C) v ↔ ∃ s : List ℕ, v = Sum.inl s := by
  cases v with
  | inl s => exact ⟨fun _ => ⟨s,rfl⟩,fun _ => PaddedNode.branch_from_original a C s⟩
  | inr v =>
      constructor
      · intro h
        exact False.elim (no_branch_of_finite_rank (PaddedNode.tree a C) (Sum.inr v)
          (by exact WithTop.coe_ne_top) h)
      · rintro ⟨s,h⟩
        cases h

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingExtension
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

/-- The two cases of the source padding argument: below the old cutoff
retain the exact source ranks, and above it use finite slack over the
new cutoff. -/
theorem exists_ancestor_rank_template
    (T : RankedTree) (x : T.Vertex) (m : ℕ) (a b d : Ordinal.{0})
    (hdb : d < b) (hba : cutoff b ≤ a) (targetRank : WithTop Ordinal.{0})
    (hmatch : RankAgrees b (T.rank ((T.parent^[m]) x)) targetRank)
    (hne : ∀ j < m, (T.parent^[j]) x ≠ T.root) :
    ∃ σ : ℕ → Ordinal.{0}, PathTemplate T a d ((T.parent^[m]) x) targetRank
      (ancestorPath T x σ m) := by
  classical
  by_cases hlow : T.rank ((T.parent^[m]) x) < (cutoff b : WithTop Ordinal.{0})
  · let σ : ℕ → Ordinal.{0} := fun j => finiteOrdinal (T.rank ((T.parent^[j]) x))
    have hlt (j : ℕ) (hj : j ≤ m) :
        T.rank ((T.parent^[j]) x) < (cutoff b : WithTop Ordinal.{0}) :=
      (T.rank_iterate_parent_monotone x hj).trans_lt hlow
    have hco (j : ℕ) (hj : j ≤ m) : (σ j : WithTop Ordinal.{0}) = T.rank ((T.parent^[j]) x) :=
      coe_untopD_of_lt (hlt j hj)
    refine ⟨σ,ancestorPath_template T a d x σ m targetRank ?_ ?_ ?_ ?_⟩
    · intro j hj
      apply WithTop.coe_lt_coe.mp
      rw [hco j hj.le]
      exact (hlt j hj.le).trans_le (WithTop.coe_le_coe.mpr hba)
    · intro j hj
      apply WithTop.coe_lt_coe.mp
      rw [hco j hj.le,hco (j+1) (by omega)]
      have hfinite : T.rank ((T.parent^[j]) x) ≠ ⊤ := by
        intro ht
        have hl := hlt j hj.le
        rw [ht] at hl
        exact (not_lt_of_ge le_top) hl
      simpa only [Function.iterate_succ_apply'] using
        T.finite_rank_strict ((T.parent^[j]) x) (hne j hj) hfinite
    · intro j hj
      exact Or.inl (hco j hj.le).symm
    · rw [hco m le_rfl,hmatch.eq_of_lt_left hlow]
  · refine ⟨pathRank T x d,ancestorPath_template T a d x (pathRank T x d) m targetRank
      (fun j _ => pathRank_lt x hdb hba j)
      (fun j hj => pathRank_lt_succ T x d j (hne j hj))
      (fun j _ => pathRank_agrees T x d j) ?_⟩
    exact pathRank_anchor_le hdb m targetRank (le_of_not_gt hlow) hmatch

/-- Every good finite partial map has a lower-level extension covering
one prescribed source point. This discharges the actual finite-path
reservoir extension obligation. -/
theorem exists_good_extension
    {T U : RankedTree} {a b d : Ordinal.{0}}
    (hU : HasFatReservoirs U a) (f : GoodPartial T U b)
    (hdb : d < b) (hba : cutoff b ≤ a) (x : T.Vertex) :
    ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧ x ∈ g.source := by
  classical
  by_cases hx : x ∈ f.source
  · exact ⟨f.lower hdb.le,(fun _ h => h),hx⟩
  let m := f.firstMappedAncestorDepth x
  have hm : 0 < m := by
    by_contra hn
    have hm0 : m = 0 := by omega
    have hf := f.firstMappedAncestor_mem x
    rw [show f.firstMappedAncestorDepth x = 0 from hm0] at hf
    exact hx hf
  obtain ⟨⟨v,y⟩,hvy,hv⟩ := Finset.mem_image.mp (f.firstMappedAncestor_mem x)
  dsimp at hv
  subst v
  have hmatch : RankAgrees b (T.rank ((T.parent^[m]) x)) (U.rank y) := f.ranks _ hvy
  have hne : ∀ j < m, (T.parent^[j]) x ≠ T.root := by
    intro j hj heq
    exact f.before_firstMappedAncestor x hj (heq ▸ f.root_mem_source)
  obtain ⟨σ,ht⟩ := exists_ancestor_rank_template T x m a b d hdb hba (U.rank y) hmatch hne
  let f' := f.lower hdb.le
  obtain ⟨g,hg,hpath⟩ := extend_path hU f' ((T.parent^[m]) x) y hvy
    (ancestorPath T x σ m) ht (ancestorPath_fresh f x σ)
    (ancestorPath_nodup T x σ m (f.firstMappedAncestorDepth_le_height x))
  refine ⟨g,hg,?_⟩
  have hmem : (x,σ 0) ∈ ancestorPath T x σ m := by
    apply List.mem_map.mpr
    refine ⟨0,List.mem_reverse.mpr (List.mem_range.mpr hm),?_⟩
    rfl
  obtain ⟨w,hw,_⟩ := hpath (x,σ 0) hmem
  exact Finset.mem_image.mpr ⟨(x,w),hw,rfl⟩

end FSCofinality.Padding


end
end

-- Original module: FSCofinalityProof.PaddingBackAndForth
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

/-- Good partial tree maps yield the ordinary back-and-forth relation
once their explicit extension property has been proved. The two
extension hypotheses are the finite-path reservoir argument. -/
theorem backAndForth_of_goodPartial
    (T U : RankedTree) (eT : ℕ ≃ T.Vertex) (eU : ℕ ≃ U.Vertex)
    (B : Ordinal.{0})
    (hforth : ∀ b ≤ B, ∀ d < b, ∀ f : GoodPartial T U b, ∀ x : T.Vertex,
      ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧ x ∈ g.source)
    (hback : ∀ b ≤ B, ∀ d < b, ∀ f : GoodPartial T U b, ∀ y : U.Vertex,
      ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧ y ∈ g.target)
    (b : Ordinal.{0}) (hbB : b ≤ B) (f : GoodPartial T U b)
    (R : List (ℕ × ℕ)) (hR : ∀ p ∈ R, (eT p.1,eU p.2) ∈ f.pairs) :
    PartialIso.BackAndForth (code T eT) (code U eU) b R := by
  classical
  induction b using WellFoundedLT.induction generalizing R with
  | ind b IH =>
      rw [PartialIso.BackAndForth]
      refine ⟨f.atomicCompatible eT eU {p | p ∈ R} hR,fun d hdb => ⟨?_,?_⟩⟩
      · intro x
        obtain ⟨g,hfg,hx⟩ := hforth b hbB d hdb f (eT x)
        obtain ⟨⟨v,w⟩,hvw,hvx⟩ := Finset.mem_image.mp hx
        dsimp at hvx
        subst v
        refine ⟨eU.symm w,IH d hdb (le_trans hdb.le hbB) g
          (R ++ [(x,eU.symm w)]) ?_⟩
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hfg (hR p hp)
        · have hpe : p = (x,eU.symm w) := List.mem_singleton.mp hp
          subst p
          simpa only [Equiv.apply_symm_apply] using hvw
      · intro y
        obtain ⟨g,hfg,hy⟩ := hback b hbB d hdb f (eU y)
        obtain ⟨⟨v,w⟩,hvw,hwy⟩ := Finset.mem_image.mp hy
        dsimp at hwy
        subst w
        refine ⟨eT.symm v,IH d hdb (le_trans hdb.le hbB) g
          (R ++ [(eT.symm v,y)]) ?_⟩
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hfg (hR p hp)
        · have hpe : p = (eT.symm v,y) := List.mem_singleton.mp hp
          subst p
          simpa only [Equiv.apply_symm_apply] using hvw

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingFatLemma
section


set_option autoImplicit false
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq α

namespace FSCofinality.Padding

theorem RankAgrees.symm {b : Ordinal.{0}} {r s : WithTop Ordinal.{0}}
    (h : RankAgrees b r s) : RankAgrees b s r := by
  rcases h with h | ⟨hr,hs⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨hs,hr⟩

def GoodPartial.swap {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : GoodPartial U T b where
  pairs := f.pairs.image Prod.swap
  roots := Finset.mem_image.mpr ⟨(T.root,U.root),f.roots,rfl⟩
  bijective := by
    rintro p hp q hq
    obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q₀,hq₀,rfl⟩ := Finset.mem_image.mp hq
    exact (f.bijective p₀ hp₀ q₀ hq₀).symm
  parents := by
    intro p hp
    obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨(T.parent p₀.1,U.parent p₀.2),f.parents p₀ hp₀,rfl⟩
  colors := by
    intro p hp
    obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
    exact (f.colors p₀ hp₀).symm
  ranks := by
    intro p hp
    obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
    exact (f.ranks p₀ hp₀).symm

theorem GoodPartial.mem_swap_iff {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) (p : U.Vertex × T.Vertex) :
    p ∈ f.swap.pairs ↔ p.swap ∈ f.pairs := by
  constructor
  · intro hp
    obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hp
    subst p
    exact hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p.swap,hp,by cases p; rfl⟩

theorem GoodPartial.target_swap {T U : RankedTree} {b : Ordinal.{0}}
    (f : GoodPartial T U b) : f.swap.target = f.source := by
  simp only [GoodPartial.target,GoodPartial.source,GoodPartial.swap,Finset.image_image,
    Function.comp_def]
  rfl

def rootPartial (T U : RankedTree) (b : Ordinal.{0})
    (hc : T.color T.root = U.color U.root)
    (hr : RankAgrees b (T.rank T.root) (U.rank U.root)) : GoodPartial T U b where
  pairs := {(T.root,U.root)}
  roots := Finset.mem_singleton_self _
  bijective := by
    intro p hp q hq
    obtain rfl := Finset.mem_singleton.mp hp
    obtain rfl := Finset.mem_singleton.mp hq
    exact ⟨fun _ => rfl,fun _ => rfl⟩
  parents := by
    intro p hp
    obtain rfl := Finset.mem_singleton.mp hp
    simpa only [T.parent_root,U.parent_root] using Finset.mem_singleton_self (T.root,U.root)
  colors := by
    intro p hp
    obtain rfl := Finset.mem_singleton.mp hp
    exact hc
  ranks := by
    intro p hp
    obtain rfl := Finset.mem_singleton.mp hp
    exact hr

/-- The genuine fat-padding back-and-forth lemma, in the fixed native
relational tree language. The vertex enumerations can be any bijections. -/
theorem fat_padding_backAndForth
    (a b : Ordinal.{0}) (hba : cutoff b ≤ a) (C : List ℕ → ℕ)
    (eP : ℕ ≃ PaddedNode a) (eF : ℕ ≃ FatNode a) :
    PartialIso.BackAndForth
      (code (PaddedNode.tree a C) eP) (code (FatNode.tree a (C [])) eF) b [] := by
  let T := PaddedNode.tree a C
  let U := FatNode.tree a (C [])
  have hforth : ∀ c ≤ b, ∀ d < c, ∀ f : GoodPartial T U c, ∀ x : T.Vertex,
      ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧ x ∈ g.source := by
    intro c hcb d hdc f x
    exact exists_good_extension (FatNode.hasFatReservoirs a (C [])) f hdc
      ((cutoff_mono hcb).trans hba) x
  have hback : ∀ c ≤ b, ∀ d < c, ∀ f : GoodPartial T U c, ∀ y : U.Vertex,
      ∃ g : GoodPartial T U d, f.pairs ⊆ g.pairs ∧ y ∈ g.target := by
    intro c hcb d hdc f y
    obtain ⟨g,hg,hy⟩ := exists_good_extension (PaddedNode.hasFatReservoirs a C) f.swap hdc
      ((cutoff_mono hcb).trans hba) y
    refine ⟨g.swap,?_,?_⟩
    · intro p hp
      apply (g.mem_swap_iff p).mpr
      exact hg ((f.mem_swap_iff p.swap).mpr hp)
    · rwa [g.target_swap]
  have hrank : RankAgrees b (T.rank T.root) (U.rank U.root) :=
    Or.inr ⟨le_top,WithTop.coe_le_coe.mpr hba⟩
  let f := rootPartial T U b rfl hrank
  exact backAndForth_of_goodPartial T U eP eF b hforth hback b le_rfl f []
    (fun _ h => False.elim (List.not_mem_nil h))

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingEnumeration
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

theorem FatNode.infinite (a : Ordinal.{0}) (ha : 0 < a) : Infinite (FatNode a) :=
  Infinite.of_injective (fun k : ℕ => FatNode.child (FatNode.root : FatNode a) 0 ha 0 k)
    (FatNode.child_copy_injective (FatNode.root : FatNode a) 0 ha 0)

theorem PaddedNode.infinite (a : Ordinal.{0}) : Infinite (PaddedNode a) := by
  apply Infinite.of_injective (fun n : ℕ => (Sum.inl [n] : PaddedNode a))
  intro m n h
  have he := Sum.inl.inj h
  exact List.singleton_inj.mp he

theorem exists_fat_enumeration (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (hpos : 0 < a) :
    Nonempty (ℕ ≃ FatNode a) := by
  letI := FatNode.countable a ha
  letI := FatNode.infinite a hpos
  infer_instance

theorem exists_padded_enumeration (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    Nonempty (ℕ ≃ PaddedNode a) := by
  letI := PaddedNode.countable a ha
  letI := PaddedNode.infinite a
  infer_instance

def fatEnumeration (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (hpos : 0 < a) :
    ℕ ≃ FatNode a := Classical.choice (exists_fat_enumeration a ha hpos)

def paddedEnumeration (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    ℕ ≃ PaddedNode a := Classical.choice (exists_padded_enumeration a ha)

/-- The canonical and padded trees now have actual structures on the
mission's fixed domain `ℕ`; the enumerations are fixed separately for
each countable ordinal, as required by the source quantifiers. -/
theorem fat_padding_on_nat (a b : Ordinal.{0})
    (ha : a < Ordinal.omega 1) (hpos : 0 < a) (hba : cutoff b ≤ a)
    (C : List ℕ → ℕ) :
    PartialIso.BackAndForth
      (code (PaddedNode.tree a C) (paddedEnumeration a ha))
      (code (FatNode.tree a (C [])) (fatEnumeration a ha hpos)) b [] :=
  fat_padding_backAndForth a b hba C (paddedEnumeration a ha) (fatEnumeration a ha hpos)

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingTupleGraphs
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open TopologicalSpace

namespace FSCofinality.Padding

def tupleData (G : GraphSpace) (s : List ℕ) : ℕ × (List (List Bool) × List (List Bool)) :=
  (s.length,
    (List.ofFn (fun i : Fin s.length => List.ofFn (fun j : Fin s.length =>
        decide (s.getD i.val 0 = s.getD j.val 0))),
      List.ofFn (fun i : Fin s.length => List.ofFn (fun j : Fin s.length =>
        G.val (s.getD i.val 0,s.getD j.val 0)))))

def tupleColor (G : GraphSpace) (s : List ℕ) : ℕ := Encodable.encode (tupleData G s)

theorem tupleColor_nil (G H : GraphSpace) : tupleColor G [] = tupleColor H [] := by
  rfl

theorem length_eq_of_tupleColor_eq {G H : GraphSpace} {s t : List ℕ}
    (h : tupleColor G s = tupleColor H t) : s.length = t.length :=
  congrArg Prod.fst (Encodable.encode_injective h)

/-- A tuple color records the complete equality and adjacency diagram. -/
theorem atomic_of_tupleColor_eq {G H : GraphSpace} {s t : List ℕ}
    (h : tupleColor G s = tupleColor H t) (i j : ℕ) (hi : i < s.length) (hj : j < s.length) :
    (s.getD i 0 = s.getD j 0 ↔ t.getD i 0 = t.getD j 0) ∧
      G.val (s.getD i 0,s.getD j 0) = H.val (t.getD i 0,t.getD j 0) := by
  have he := Encodable.encode_injective h
  have hlen : s.length = t.length := congrArg Prod.fst he
  have hEq := congrArg (fun x : ℕ × (List (List Bool) × List (List Bool)) => x.2.1) he
  have hAdj := congrArg (fun x : ℕ × (List (List Bool) × List (List Bool)) => x.2.2) he
  dsimp only [tupleData] at hEq hAdj
  rw [← hlen] at hEq hAdj
  have hiEq := congrFun (List.ofFn_injective hEq) ⟨i,hi⟩
  have hijEq := congrFun (List.ofFn_injective hiEq) ⟨j,hj⟩
  have hiAdj := congrFun (List.ofFn_injective hAdj) ⟨i,hi⟩
  have hijAdj := congrFun (List.ofFn_injective hiAdj) ⟨j,hj⟩
  exact ⟨by simpa only [decide_eq_decide] using hijEq,hijAdj⟩

theorem continuous_tupleColor (s : List ℕ) : Continuous (fun G : GraphSpace => tupleColor G s) := by
  have hentry (i j : Fin s.length) : Continuous (fun G : GraphSpace =>
      G.val (s.getD i.val 0,s.getD j.val 0)) :=
    (_root_.continuous_apply _).comp continuous_subtype_val
  have hrow (i : Fin s.length) : Continuous (fun G : GraphSpace =>
      List.ofFn (fun j : Fin s.length => G.val (s.getD i.val 0,s.getD j.val 0))) :=
    (continuous_of_discreteTopology : Continuous (List.ofFn : (Fin s.length → Bool) → List Bool)).comp
      (continuous_pi (fun j => hentry i j))
  have hmatrix : Continuous (fun G : GraphSpace =>
      List.ofFn (fun i : Fin s.length => List.ofFn (fun j : Fin s.length =>
        G.val (s.getD i.val 0,s.getD j.val 0)))) :=
    (continuous_of_discreteTopology : Continuous
      (List.ofFn : (Fin s.length → List Bool) → List (List Bool))).comp
        (continuous_pi hrow)
  have hdata : Continuous (fun G : GraphSpace => tupleData G s) :=
    continuous_const.prodMk (continuous_const.prodMk hmatrix)
  exact (continuous_of_discreteTopology : Continuous
    (Encodable.encode : (ℕ × (List (List Bool) × List (List Bool))) → ℕ)).comp hdata

def paddedGraphCode (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (G : GraphSpace) :
    Structures treeLanguage :=
  code (PaddedNode.tree a (tupleColor G)) (paddedEnumeration a ha)

theorem continuous_paddedGraphCode (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    Continuous (paddedGraphCode a ha) := by
  have hcolor (v : PaddedNode a) : Continuous
      (fun G : GraphSpace => PaddedNode.color (tupleColor G) v) := by
    cases v with
    | inl s => exact continuous_tupleColor s
    | inr v => exact continuous_const
  apply continuous_pi
  rintro ⟨s,t⟩
  rcases s with _ | (_ | c)
  · change Continuous (fun _ : GraphSpace => decide
      ((paddedEnumeration a ha) (t ⟨0,by simp [treeLanguage]⟩) = PaddedNode.root a))
    exact continuous_const
  · change Continuous (fun _ : GraphSpace => decide
      (PaddedNode.parent ((paddedEnumeration a ha) (t ⟨0,by simp [treeLanguage]⟩)) =
        (paddedEnumeration a ha) (t ⟨1,by simp [treeLanguage]⟩)))
    exact continuous_const
  · exact (continuous_of_discreteTopology : Continuous (fun n : ℕ => decide (n = c))).comp
      (hcolor ((paddedEnumeration a ha) (t ⟨0,by simp [treeLanguage]⟩)))

theorem measurable_paddedGraphCode (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    Measurable (paddedGraphCode a ha) := (continuous_paddedGraphCode a ha).measurable

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingOriginalEquiv
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

theorem TreeIso.original_image {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) (s : List ℕ) :
    ∃ t : List ℕ, e.equiv (Sum.inl s) = Sum.inl t :=
  (PaddedNode.branch_iff_original a D _).mp
    (e.map_branch (PaddedNode.branch_from_original a C s))

def TreeIso.originalMap {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) (s : List ℕ) : List ℕ :=
  Classical.choose (e.original_image s)

theorem TreeIso.originalMap_spec {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) (s : List ℕ) :
    e.equiv (Sum.inl s) = Sum.inl (e.originalMap s) := Classical.choose_spec (e.original_image s)

theorem TreeIso.originalMap_bijective {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) :
    Function.Bijective e.originalMap := by
  constructor
  · intro s t h
    apply Sum.inl.inj
    apply e.equiv.injective
    rw [e.originalMap_spec s,e.originalMap_spec t,h]
  · intro t
    obtain ⟨s,hs⟩ := e.symm.original_image t
    refine ⟨s,?_⟩
    apply Sum.inl.inj
    have he := congrArg e.equiv hs
    simpa only [TreeIso.symm,Equiv.apply_symm_apply,e.originalMap_spec s] using he.symm

def TreeIso.originalEquiv {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) : List ℕ ≃ List ℕ :=
  Equiv.ofBijective e.originalMap e.originalMap_bijective

theorem TreeIso.originalEquiv_colors {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) (s : List ℕ) :
    D (e.originalEquiv s) = C s := by
  have h := e.colors (Sum.inl s)
  rw [e.originalMap_spec s] at h
  exact h

theorem TreeIso.originalEquiv_root {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) : e.originalEquiv [] = [] := by
  apply Sum.inl.inj
  exact (e.originalMap_spec []).symm.trans e.roots

theorem TreeIso.originalEquiv_parent {a : Ordinal.{0}} {C D : List ℕ → ℕ}
    (e : TreeIso (PaddedNode.tree a C) (PaddedNode.tree a D)) (s : List ℕ) :
    e.originalEquiv s.dropLast = (e.originalEquiv s).dropLast := by
  have h := e.parents (Sum.inl s)
  change e.equiv (Sum.inl s.dropLast) = PaddedNode.parent (e.equiv (Sum.inl s)) at h
  rw [e.originalMap_spec s.dropLast,e.originalMap_spec s] at h
  exact Sum.inl.inj h

theorem TreeIso.originalEquiv_length {a : Ordinal.{0}} {G H : GraphSpace}
    (e : TreeIso (PaddedNode.tree a (tupleColor G)) (PaddedNode.tree a (tupleColor H)))
    (s : List ℕ) : (e.originalEquiv s).length = s.length :=
  length_eq_of_tupleColor_eq (e.originalEquiv_colors s)

theorem TreeIso.originalEquiv_extension {a : Ordinal.{0}} {G H : GraphSpace}
    (e : TreeIso (PaddedNode.tree a (tupleColor G)) (PaddedNode.tree a (tupleColor H)))
    (s : List ℕ) (n : ℕ) :
    ∃ m : ℕ, e.originalEquiv (s ++ [n]) = e.originalEquiv s ++ [m] := by
  let t := e.originalEquiv (s ++ [n])
  have hne : t ≠ [] := by
    intro ht
    have hlen := e.originalEquiv_length (s ++ [n])
    change t.length = (s ++ [n]).length at hlen
    rw [ht] at hlen
    simp at hlen
  refine ⟨t.getLast hne,?_⟩
  have hp : t.dropLast = e.originalEquiv s := by
    simpa only [List.dropLast_append_getLast,List.dropLast_concat] using
      (e.originalEquiv_parent (s ++ [n])).symm
  simpa only [hp] using (List.dropLast_append_getLast hne).symm

theorem TreeIso.originalEquiv_backextension {a : Ordinal.{0}} {G H : GraphSpace}
    (e : TreeIso (PaddedNode.tree a (tupleColor G)) (PaddedNode.tree a (tupleColor H)))
    (s : List ℕ) (m : ℕ) :
    ∃ n : ℕ, e.originalEquiv (s ++ [n]) = e.originalEquiv s ++ [m] := by
  let t := e.originalEquiv.symm (e.originalEquiv s ++ [m])
  have ht : e.originalEquiv t = e.originalEquiv s ++ [m] := e.originalEquiv.apply_symm_apply _
  have hne : t ≠ [] := by
    intro hn
    rw [hn,e.originalEquiv_root] at ht
    simp at ht
  have hp : t.dropLast = s := by
    apply e.originalEquiv.injective
    rw [e.originalEquiv_parent t,ht]
    simp
  refine ⟨t.getLast hne,?_⟩
  have hst : s ++ [t.getLast hne] = t := by
    simpa only [hp] using List.dropLast_append_getLast hne
  rwa [hst]

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingTupleBranch
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

def sourceTuple (s : List ℕ) : List ℕ := (PartialIso.pairsFrom 0 s).map Prod.fst
def targetTuple (s : List ℕ) : List ℕ := (PartialIso.pairsFrom 0 s).map Prod.snd

@[simp] theorem sourceTuple_length (s : List ℕ) : (sourceTuple s).length = s.length := by
  have hp : ∀ (k : ℕ) (s : List ℕ), (PartialIso.pairsFrom k s).length = s.length := by
    intro k s
    induction s generalizing k <;> simp_all [PartialIso.pairsFrom]
  simpa only [sourceTuple,List.length_map] using hp 0 s

@[simp] theorem targetTuple_length (s : List ℕ) : (targetTuple s).length = s.length := by
  have hp : ∀ (k : ℕ) (s : List ℕ), (PartialIso.pairsFrom k s).length = s.length := by
    intro k s
    induction s generalizing k <;> simp_all [PartialIso.pairsFrom]
  simpa only [targetTuple,List.length_map] using hp 0 s

theorem sourceTuple_append (s : List ℕ) (n : ℕ) :
    sourceTuple (s ++ [n]) = sourceTuple s ++ [(PartialIso.scheduledPair s.length n).1] := by
  simp [sourceTuple,PartialIso.pairsFrom_append,PartialIso.pairsFrom]

theorem targetTuple_append (s : List ℕ) (n : ℕ) :
    targetTuple (s ++ [n]) = targetTuple s ++ [(PartialIso.scheduledPair s.length n).2] := by
  simp [targetTuple,PartialIso.pairsFrom_append,PartialIso.pairsFrom]

theorem sourceTuple_getD_prefix (b : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    (sourceTuple (PartialIso.initialSegment b n)).getD i 0 = (PartialIso.scheduledPair i (b i)).1 := by
  simp only [sourceTuple,PartialIso.initialSegment,PartialIso.pairsFrom_ofFn,List.map_ofFn,Nat.zero_add]
  rw [List.getD_eq_getElem _ _ (by simpa)]
  simp only [List.getElem_ofFn,Function.comp_apply]

theorem targetTuple_getD_prefix (b : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    (targetTuple (PartialIso.initialSegment b n)).getD i 0 = (PartialIso.scheduledPair i (b i)).2 := by
  simp only [targetTuple,PartialIso.initialSegment,PartialIso.pairsFrom_ofFn,List.map_ofFn,Nat.zero_add]
  rw [List.getD_eq_getElem _ _ (by simpa)]
  simp only [List.getElem_ofFn,Function.comp_apply]

/-- Scheduled tuple correspondences with identical finite graph diagrams
along every prefix recover one actual graph isomorphism. -/
theorem graphIsomorphic_of_tuple_branch (G H : GraphSpace) (b : ℕ → ℕ)
    (hb : ∀ n, tupleColor G (sourceTuple (PartialIso.initialSegment b n)) =
      tupleColor H (targetTuple (PartialIso.initialSegment b n))) : GraphIsomorphic G H := by
  have hdiagram (n i j : ℕ) (hi : i < n) (hj : j < n) :
      ((PartialIso.scheduledPair i (b i)).1 = (PartialIso.scheduledPair j (b j)).1 ↔
        (PartialIso.scheduledPair i (b i)).2 = (PartialIso.scheduledPair j (b j)).2) ∧
      G.val ((PartialIso.scheduledPair i (b i)).1,(PartialIso.scheduledPair j (b j)).1) =
        H.val ((PartialIso.scheduledPair i (b i)).2,(PartialIso.scheduledPair j (b j)).2) := by
    have h := atomic_of_tupleColor_eq (hb n) i j (by simpa [PartialIso.initialSegment] using hi)
      (by simpa [PartialIso.initialSegment] using hj)
    simpa only [sourceTuple_getD_prefix b n i hi,sourceTuple_getD_prefix b n j hj,
      targetTuple_getD_prefix b n i hi,targetTuple_getD_prefix b n j hj] using h
  let f : ℕ → ℕ := fun i => b (2*i)
  let g : ℕ → ℕ := fun i => b (2*i+1)
  have hgf (i : ℕ) : g (f i) = i := by
    have h := (hdiagram (max (2*i) (2*(f i)+1)+1) (2*i) (2*(f i)+1) (by omega) (by omega)).1
    simp only [PartialIso.scheduledPair_even,PartialIso.scheduledPair_odd] at h
    exact (h.mpr rfl).symm
  have hfg (i : ℕ) : f (g i) = i := by
    have h := (hdiagram (max (2*(g i)) (2*i+1)+1) (2*(g i)) (2*i+1) (by omega) (by omega)).1
    simp only [PartialIso.scheduledPair_even,PartialIso.scheduledPair_odd] at h
    exact h.mp rfl
  let e : ℕ ≃ ℕ := ⟨f,g,hgf,hfg⟩
  refine ⟨e,fun m n => ?_⟩
  simpa only [PartialIso.scheduledPair_even] using
    (hdiagram (max (2*m) (2*n)+1) (2*m) (2*n) (by omega) (by omega)).2

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.TreeBranches
section


noncomputable section
open Set Filter TopologicalSpace Topology

namespace FSCofinality.RootedTrees

abbrev Baire := ℕ → ℕ

theorem mem_parent (T : TreeSpace) (s : Node) (n : ℕ) (h : T (s ++ [n]) = true) :
    T s = true := T.property s n h

theorem mem_of_append (T : TreeSpace) (s t : Node) (h : T (s ++ t) = true) : T s = true := by
  induction t using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton t n ih =>
    exact ih (mem_parent T (s ++ t) n (by simpa only [List.append_assoc] using h))

def branchPrefix (x : Baire) (n : ℕ) : Node := List.ofFn (fun i : Fin n => x i)

@[simp] theorem length_branchPrefix (x : Baire) (n : ℕ) : (branchPrefix x n).length = n := by
  simp [branchPrefix]

@[simp] theorem branchPrefix_zero (x : Baire) : branchPrefix x 0 = [] := rfl

theorem branchPrefix_succ (x : Baire) (n : ℕ) : branchPrefix x (n+1) = branchPrefix x n ++ [x n] := by
  simpa [branchPrefix,List.concat_eq_append] using List.ofFn_succ' (fun i : Fin (n+1) => x i)

theorem continuous_branchPrefix (n : ℕ) : Continuous (fun x : Baire => branchPrefix x n) := by
  exact (continuous_of_discreteTopology : Continuous (List.ofFn : (Fin n → ℕ) → Node)).comp
    (continuous_pi (fun i => continuous_apply (i : ℕ)))

theorem continuous_eval (s : Node) : Continuous (fun T : TreeSpace => T s) :=
  (continuous_apply s).comp continuous_subtype_val

theorem mem_take (T : TreeSpace) (s : Node) (k : ℕ) (hs : T s = true) :
    T (s.take k) = true :=
  mem_of_append T (s.take k) (s.drop k) (by simpa using hs)

@[simp] theorem take_branchPrefix (x : Baire) (n k : ℕ) :
    (branchPrefix x n).take k = branchPrefix x (min k n) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [branchPrefix]

theorem mem_branchPrefix_of_le (T : TreeSpace) (x : Baire) {k n : ℕ}
    (hkn : k ≤ n) (hn : T (branchPrefix x n) = true) : T (branchPrefix x k) = true := by
  simpa only [take_branchPrefix,Nat.min_eq_left hkn] using mem_take T (branchPrefix x n) k hn

def HasBranch (T : TreeSpace) : Prop := ∃ x : Baire, ∀ n, T (branchPrefix x n) = true

theorem tendsto_of_prefix_agreement (u : ℕ → Baire) (x : Baire)
    (h : ∀ n, branchPrefix (u n) n = branchPrefix x n) : Tendsto u atTop (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have heq : ∀ᶠ n in atTop, u n i = x i := by
    filter_upwards [eventually_ge_atTop (i+1)] with n hn
    exact congrFun (List.ofFn_injective (h n)) ⟨i,by omega⟩
  exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)

theorem wellFounded_of_acc_root (T : TreeSpace) (hroot : T [] = true)
    (hacc : Acc (@Child T) ⟨[],hroot⟩) : WellFounded (@Child T) := by
  have hall : ∀ s : Node, ∀ hs : T s = true, Acc (@Child T) ⟨s,hs⟩ := by
    intro s
    induction s using List.reverseRecOn with
    | nil => intro hs; exact hacc
    | append_singleton s n ih =>
      intro hs
      exact (ih (T.property s n hs)).inv ⟨n,rfl⟩
  exact ⟨fun s => hall s.val s.property⟩

theorem wellFounded_child_iff_no_branch (T : TreeSpace) :
    WellFounded (@Child T) ↔ ¬ HasBranch T := by
  constructor
  · intro hwf
    rintro ⟨x,hx⟩
    let f : ℕ → Nodes T := fun n => ⟨branchPrefix x n,hx n⟩
    have hstep (n : ℕ) : Child (f (n+1)) (f n) := ⟨x n,branchPrefix_succ x n⟩
    exact (not_acc_iff_exists_descending_chain.mpr ⟨f,rfl,hstep⟩) (hwf.apply (f 0))
  · intro hnb
    by_cases hroot : T [] = true
    · apply wellFounded_of_acc_root T hroot
      by_contra hbad
      obtain ⟨f,hf0,hstep⟩ := not_acc_iff_exists_descending_chain.mp hbad
      choose k hk using hstep
      have hp : ∀ n, (f n).val = branchPrefix k n := by
        intro n
        induction n with
        | zero => exact congrArg Subtype.val hf0
        | succ n ih => rw [hk n,ih,branchPrefix_succ]
      apply hnb
      exact ⟨k,fun n => hp n ▸ (f n).property⟩
    · refine ⟨fun s => False.elim (hroot ?_)⟩
      simpa using mem_of_append T [] s.val (by simpa using s.property)

end FSCofinality.RootedTrees

end
end

-- Original module: FSCofinalityProof.BorelPrunedBranch
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology TopologicalSpace

namespace FSCofinality.RootedTrees

local instance : MeasurableSpace Node := borel Node
local instance : BorelSpace Node := ⟨rfl⟩

def Pruned (T : TreeSpace) : Prop :=
  ∀ s : Node, T s = true → ∃ n : ℕ, T (s ++ [n]) = true

theorem continuous_child_bit (n : ℕ) :
    Continuous (fun p : TreeSpace × Node => p.1 (p.2 ++ [n])) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have heq : ∀ᶠ q : TreeSpace × Node in 𝓝 p, q.2 = p.2 :=
    (continuous_snd.tendsto p).eventually ((isOpen_discrete {p.2}).mem_nhds rfl)
  have hc : ContinuousAt (fun q : TreeSpace × Node => q.1 (p.2 ++ [n])) p :=
    ((continuous_eval (p.2 ++ [n])).comp continuous_fst).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [heq] with q hq
  rw [hq]

private theorem exists_child_candidate (T : TreeSpace) (s : Node) :
    ∃ n, T (s ++ [n]) = true ∨ ¬ ∃ k, T (s ++ [k]) = true := by
  by_cases h : ∃ k, T (s ++ [k]) = true
  · obtain ⟨k,hk⟩ := h
    exact ⟨k,Or.inl hk⟩
  · exact ⟨0,Or.inr h⟩

def childIndex (T : TreeSpace) (s : Node) : ℕ := Nat.find (exists_child_candidate T s)

theorem childIndex_spec (T : TreeSpace) (s : Node) (h : ∃ k, T (s ++ [k]) = true) :
    T (s ++ [childIndex T s]) = true :=
  (Nat.find_spec (exists_child_candidate T s)).resolve_right (not_not.mpr h)

theorem measurable_childIndex : Measurable (fun p : TreeSpace × Node => childIndex p.1 p.2) := by
  have hc (n : ℕ) : MeasurableSet {p : TreeSpace × Node | p.1 (p.2 ++ [n]) = true} :=
    (measurableSet_singleton true).preimage (continuous_child_bit n).measurable
  have he : MeasurableSet {p : TreeSpace × Node | ∃ n, p.1 (p.2 ++ [n]) = true} := by
    simpa only [setOf_exists] using MeasurableSet.iUnion hc
  exact measurable_find (fun p : TreeSpace × Node => exists_child_candidate p.1 p.2)
    (fun n => (hc n).union he.compl)

def chosenPrefix (T : TreeSpace) : ℕ → Node
  | 0 => []
  | n+1 => chosenPrefix T n ++ [childIndex T (chosenPrefix T n)]

theorem measurable_chosenPrefix (n : ℕ) : Measurable (fun T => chosenPrefix T n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hstep : Measurable (fun T => childIndex T (chosenPrefix T n)) :=
      measurable_childIndex.comp (measurable_id.prodMk ih)
    exact (measurable_of_countable (fun p : Node × ℕ => p.1 ++ [p.2])).comp (ih.prodMk hstep)

def branchChoice (T : TreeSpace) : Baire := fun n => childIndex T (chosenPrefix T n)

theorem measurable_branchChoice : Measurable branchChoice := by
  apply measurable_pi_lambda
  intro n
  exact measurable_childIndex.comp (measurable_id.prodMk (measurable_chosenPrefix n))

theorem chosenPrefix_eq_branchPrefix (T : TreeSpace) (n : ℕ) :
    chosenPrefix T n = branchPrefix (branchChoice T) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change chosenPrefix T n ++ [branchChoice T n] = branchPrefix (branchChoice T) (n+1)
    rw [branchPrefix_succ,ih]

theorem chosenPrefix_mem (T : TreeSpace) (hroot : T [] = true) (hpruned : Pruned T)
    (n : ℕ) : T (chosenPrefix T n) = true := by
  induction n with
  | zero => exact hroot
  | succ n ih => exact childIndex_spec T _ (hpruned _ ih)

/-- The total Borel choice function is a branch on rooted pruned trees.
No branch-selection assertion is made for arbitrary ill-founded trees. -/
theorem branchChoice_spec (T : TreeSpace) (hroot : T [] = true) (hpruned : Pruned T) :
    ∀ n, T (branchPrefix (branchChoice T) n) = true := by
  intro n
  rw [← chosenPrefix_eq_branchPrefix]
  exact chosenPrefix_mem T hroot hpruned n

end FSCofinality.RootedTrees

end
end

-- Original module: FSCofinalityProof.PaddingReflection
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.Padding

def TupleWordValid (φ : List ℕ → List ℕ) (s : List ℕ) : Prop :=
  ∀ k ≤ s.length, φ (sourceTuple (s.take k)) = targetTuple (s.take k)

theorem take_append_singleton_of_le (s : List ℕ) (n k : ℕ) (hk : k ≤ s.length) :
    (s ++ [n]).take k = s.take k := by
  simp [List.take_append,Nat.sub_eq_zero_of_le hk]

def tupleMatchTree (φ : List ℕ → List ℕ) : RootedTrees.TreeSpace where
  val := fun s => decide (TupleWordValid φ s)
  property := by
    intro s n h
    have hs := of_decide_eq_true h
    apply decide_eq_true
    intro k hk
    have hc := hs k (by simpa only [List.length_append,List.length_singleton] using (show k ≤ s.length+1 from by omega))
    simpa only [take_append_singleton_of_le s n k hk] using hc

theorem tupleWordValid_extend {φ : List ℕ → List ℕ} {s : List ℕ} {n : ℕ}
    (hs : TupleWordValid φ s)
    (hn : φ (sourceTuple (s ++ [n])) = targetTuple (s ++ [n])) :
    TupleWordValid φ (s ++ [n]) := by
  intro k hk
  by_cases hks : k ≤ s.length
  · rw [take_append_singleton_of_le s n k hks]
    exact hs k hks
  · have heq : k = (s ++ [n]).length := by
      simp only [List.length_append,List.length_singleton] at hk ⊢
      omega
    rw [heq,List.take_length]
    exact hn

theorem tupleMatchTree_pruned (φ : List ℕ → List ℕ)
    (hforth : ∀ s n, ∃ m, φ (s ++ [n]) = φ s ++ [m])
    (hback : ∀ s m, ∃ n, φ (s ++ [n]) = φ s ++ [m]) :
    RootedTrees.Pruned (tupleMatchTree φ) := by
  intro s hs
  have hvalid : TupleWordValid φ s := of_decide_eq_true hs
  have hcurrent : φ (sourceTuple s) = targetTuple s := by
    simpa only [List.take_length] using hvalid s.length le_rfl
  by_cases heven : s.length % 2 = 0
  · obtain ⟨n,hn⟩ := hforth (sourceTuple s) (s.length/2)
    refine ⟨n,decide_eq_true (tupleWordValid_extend hvalid ?_)⟩
    rw [sourceTuple_append,targetTuple_append]
    simpa only [PartialIso.scheduledPair,if_pos heven,hcurrent] using hn
  · obtain ⟨n,hn⟩ := hback (sourceTuple s) (s.length/2)
    refine ⟨n,decide_eq_true (tupleWordValid_extend hvalid ?_)⟩
    rw [sourceTuple_append,targetTuple_append]
    simpa only [PartialIso.scheduledPair,if_neg heven,hcurrent] using hn

theorem exists_scheduled_tuple_branch (φ : List ℕ → List ℕ) (hroot : φ [] = [])
    (hforth : ∀ s n, ∃ m, φ (s ++ [n]) = φ s ++ [m])
    (hback : ∀ s m, ∃ n, φ (s ++ [n]) = φ s ++ [m]) :
    ∃ b : ℕ → ℕ, ∀ n, φ (sourceTuple (PartialIso.initialSegment b n)) =
      targetTuple (PartialIso.initialSegment b n) := by
  have hr : tupleMatchTree φ [] = true := by
    apply decide_eq_true
    intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst k
    exact hroot
  let b := RootedTrees.branchChoice (tupleMatchTree φ)
  refine ⟨b,fun n => ?_⟩
  have hb := RootedTrees.branchChoice_spec (tupleMatchTree φ) hr
    (tupleMatchTree_pruned φ hforth hback) n
  have hv : TupleWordValid φ (PartialIso.initialSegment b n) := of_decide_eq_true hb
  simpa only [List.take_length] using hv (PartialIso.initialSegment b n).length le_rfl

/-- Padding reflects actual graph isomorphism. The original tuple tree
is recovered through its intrinsic infinite-branch vertices. -/
theorem graphIsomorphic_of_paddedGraphCode_isomorphic
    (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (G H : GraphSpace)
    (h : Isomorphic (paddedGraphCode a ha G) (paddedGraphCode a ha H)) : GraphIsomorphic G H := by
  obtain ⟨e⟩ := treeIso_of_code_isomorphic
    (PaddedNode.tree a (tupleColor G)) (PaddedNode.tree a (tupleColor H))
    (paddedEnumeration a ha) (paddedEnumeration a ha) h
  obtain ⟨b,hb⟩ := exists_scheduled_tuple_branch e.originalEquiv e.originalEquiv_root
    e.originalEquiv_extension e.originalEquiv_backextension
  apply graphIsomorphic_of_tuple_branch G H b
  intro n
  have hc := (e.originalEquiv_colors (sourceTuple (PartialIso.initialSegment b n))).symm
  rwa [hb n] at hc

end FSCofinality.Padding

end
end

-- Original module: FSCofinalityProof.PaddingForward
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality.Padding

theorem getD_map_equiv_of_lt (e : ℕ ≃ ℕ) (s : List ℕ) (i : ℕ) (hi : i < s.length) :
    (s.map e).getD i 0 = e (s.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_map,
    List.getD_eq_getElem _ _ hi]

theorem tupleColor_mapped {G H : GraphSpace} (e : ℕ ≃ ℕ)
    (he : ∀ m n, G.val (m,n) = H.val (e m,e n)) (s : List ℕ) :
    tupleColor H (s.map e) = tupleColor G s := by
  unfold tupleColor
  apply congrArg Encodable.encode
  unfold tupleData
  simp only [List.length_map]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    apply decide_eq_decide.mpr
    simp only [Fin.val_cast]
    rw [getD_map_equiv_of_lt e s i.val i.isLt,getD_map_equiv_of_lt e s j.val j.isLt]
    exact e.injective.eq_iff
  · apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext j
    simp only [Fin.val_cast]
    rw [getD_map_equiv_of_lt e s i.val i.isLt,getD_map_equiv_of_lt e s j.val j.isLt]
    exact (he _ _).symm

theorem map_dropLast (e : ℕ ≃ ℕ) (s : List ℕ) :
    s.dropLast.map e = (s.map e).dropLast := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s n IH => simp

/-- A graph isomorphism acts on original tuples coordinatewise and
extends over the identical attached reservoirs. -/
theorem paddedGraphCode_isomorphic_of_graphIsomorphic
    (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (G H : GraphSpace)
    (h : GraphIsomorphic G H) : Isomorphic (paddedGraphCode a ha G) (paddedGraphCode a ha H) := by
  obtain ⟨e,he⟩ := h
  let q : PaddedNode a ≃ PaddedNode a :=
    Equiv.sumCongr (Equiv.listEquivOfEquiv e)
      (Equiv.prodCongr (Equiv.listEquivOfEquiv e) (Equiv.refl _))
  have hqL (s : List ℕ) : q (Sum.inl s) = Sum.inl (s.map e) := rfl
  have hqR (s : List ℕ) (v : {v : FatNode a // v ≠ FatNode.root}) :
      q (Sum.inr (s,v)) = Sum.inr (s.map e,v) := rfl
  have htree : TreeIso (PaddedNode.tree a (tupleColor G)) (PaddedNode.tree a (tupleColor H)) := by
    refine ⟨q,rfl,?_,?_⟩
    · intro v
      cases v with
      | inl s =>
          change Sum.inl (s.dropLast.map e) = Sum.inl ((s.map e).dropLast)
          exact congrArg Sum.inl (map_dropLast e s)
      | inr v =>
          obtain ⟨s,v⟩ := v
          change q (PaddedNode.parent (Sum.inr (s,v))) = PaddedNode.parent (q (Sum.inr (s,v)))
          rw [hqR]
          dsimp only [PaddedNode.parent]
          split_ifs with hv
          · exact hqL s
          · exact hqR s ⟨FatNode.parent v.val,hv⟩
    · intro v
      cases v with
      | inl s => exact tupleColor_mapped e he s
      | inr v => rfl
  exact code_isomorphic_of_treeIso (PaddedNode.tree a (tupleColor G))
    (PaddedNode.tree a (tupleColor H)) (paddedEnumeration a ha) (paddedEnumeration a ha) htree

theorem graphIsomorphic_iff_paddedGraphCode_isomorphic
    (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) (G H : GraphSpace) :
    GraphIsomorphic G H ↔ Isomorphic (paddedGraphCode a ha G) (paddedGraphCode a ha H) :=
  ⟨paddedGraphCode_isomorphic_of_graphIsomorphic a ha G H,
    graphIsomorphic_of_paddedGraphCode_isomorphic a ha G H⟩

theorem graphs_reduces_padded (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    BorelReducible GraphIsomorphic (@Isomorphic treeLanguage) :=
  ⟨paddedGraphCode a ha,measurable_paddedGraphCode a ha,
    graphIsomorphic_iff_paddedGraphCode_isomorphic a ha⟩

end FSCofinality.Padding


end
end

-- Original module: FSCofinalityProof.TreeRanks
section


noncomputable section
open Set Order Ordinal

namespace FSCofinality.RootedTrees

instance (T : TreeSpace) : Countable (Nodes T) :=
  inferInstanceAs (Countable {s : List ℕ // T s = true})

theorem BoundedTree.wellFounded {T : TreeSpace} {a : Ordinal.{0}}
    (h : BoundedTree T a) : WellFounded (@Child T) := by
  obtain ⟨ρ,_,hρ⟩ := h
  exact (InvImage.wf ρ Ordinal.lt_wf).mono (fun s t hst => hρ s t hst)

theorem BoundedTree.no_branch {T : TreeSpace} {a : Ordinal.{0}}
    (h : BoundedTree T a) : ¬ HasBranch T :=
  (wellFounded_child_iff_no_branch T).mp h.wellFounded

/-- Every well-founded countable tree admits a countable ordinal bound on
its whole reverse-tree height, with the exact fixed mission definition. -/
theorem exists_countable_bound_of_wellFounded (T : TreeSpace)
    (hwf : WellFounded (@Child T)) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ BoundedTree T a := by
  letI : IsWellFounded (Nodes T) (@Child T) := ⟨hwf⟩
  let ρ : Nodes T → Ordinal.{0} := IsWellFounded.rank (@Child T)
  have hc : ∀ s : Nodes T, ρ s < Ordinal.omega 1 := by
    intro s
    induction s using hwf.induction with
    | h s ih =>
      change IsWellFounded.rank (@Child T) s < Ordinal.omega 1
      rw [IsWellFounded.rank_eq]
      apply Ordinal.iSup_lt_omega_one
      intro t
      exact (Cardinal.isSuccLimit_omega 1).succ_lt (ih t.val t.property)
  let a : Ordinal.{0} := ⨆ s : Nodes T, Order.succ (ρ s)
  refine ⟨a,Ordinal.iSup_lt_omega_one (fun s =>
    (Cardinal.isSuccLimit_omega 1).succ_lt (hc s)),ρ,?_,?_⟩
  · intro s
    exact (Order.lt_succ (ρ s)).trans_le (Ordinal.le_iSup _ s)
  · intro s t hst
    exact IsWellFounded.rank_lt_of_rel hst

theorem no_branch_iff_countable_bound (T : TreeSpace) :
    ¬ HasBranch T ↔ ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ BoundedTree T a := by
  constructor
  · intro h
    exact exists_countable_bound_of_wellFounded T
      ((wellFounded_child_iff_no_branch T).mpr h)
  · rintro ⟨a,_,ha⟩
    exact ha.no_branch

end FSCofinality.RootedTrees

end
end

-- Original module: FSCofinalityProof.Boundedness
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace FSCofinality.RootedTrees

def firstNode (s : Node) : Node := s.map (fun n => (Nat.unpair n).1)
def secondNode (s : Node) : Node := s.map (fun n => (Nat.unpair n).2)

/-- A countable tree records simultaneous finite approximations to a
parameter and to a node of its continuously parametrized tree. -/
def parameterTree (f : Baire → TreeSpace) : TreeSpace :=
  ⟨fun s => decide (∃ x : Baire, branchPrefix x s.length = firstNode s ∧
      f x (secondNode s) = true), by
    intro s k hs
    obtain ⟨x,hx,ht⟩ := of_decide_eq_true hs
    apply decide_eq_true
    refine ⟨x,?_,?_⟩
    · have h := congrArg (fun l : Node => l.take s.length) hx
      simpa [firstNode,List.map_append] using h
    · have ht' : f x (secondNode s ++ [(Nat.unpair k).2]) = true := by
        simpa [secondNode,List.map_append] using ht
      exact mem_parent (f x) (secondNode s) (Nat.unpair k).2 ht'⟩

theorem parameterTree_mem_iff (f : Baire → TreeSpace) (s : Node) :
    parameterTree f s = true ↔ ∃ x : Baire,
      branchPrefix x s.length = firstNode s ∧ f x (secondNode s) = true := by
  simp only [parameterTree,decide_eq_true_eq]

@[simp] theorem firstNode_branchPrefix (z : Baire) (n : ℕ) :
    firstNode (branchPrefix z n) = branchPrefix (fun i => (Nat.unpair (z i)).1) n := by
  simp [firstNode,branchPrefix,List.map_ofFn,Function.comp_def]

@[simp] theorem secondNode_branchPrefix (z : Baire) (n : ℕ) :
    secondNode (branchPrefix z n) = branchPrefix (fun i => (Nat.unpair (z i)).2) n := by
  simp [secondNode,branchPrefix,List.map_ofFn,Function.comp_def]

theorem branch_of_parameterTree (f : Baire → TreeSpace) (hf : Continuous f)
    (h : HasBranch (parameterTree f)) : ∃ x : Baire, HasBranch (f x) := by
  obtain ⟨z,hz⟩ := h
  let x : Baire := fun n => (Nat.unpair (z n)).1
  let y : Baire := fun n => (Nat.unpair (z n)).2
  have hex (n : ℕ) : ∃ u : Baire,
      branchPrefix u n = branchPrefix x n ∧ f u (branchPrefix y n) = true := by
    simpa only [parameterTree_mem_iff,length_branchPrefix,firstNode_branchPrefix,
      secondNode_branchPrefix] using hz n
  choose u hu ht using hex
  have hlim := tendsto_of_prefix_agreement u x hu
  refine ⟨x,y,fun k => ?_⟩
  have htrue : ∀ᶠ n in atTop, f (u n) (branchPrefix y k) = true := by
    filter_upwards [eventually_ge_atTop k] with n hn
    exact mem_branchPrefix_of_le (f (u n)) y hn (ht n)
  have hc := ((continuous_eval (branchPrefix y k)).comp hf).tendsto x |>.comp hlim
  have hconst : Tendsto (fun n => f (u n) (branchPrefix y k)) atTop (𝓝 true) :=
    tendsto_const_nhds.congr' (htrue.mono fun _ h => h.symm)
  exact tendsto_nhds_unique hc hconst

def zipNode (x : Baire) (s : Node) : Node :=
  s.mapIdx (fun i n => Nat.pair (x i) n)

@[simp] theorem length_zipNode (x : Baire) (s : Node) : (zipNode x s).length = s.length := by
  simp [zipNode]

@[simp] theorem firstNode_zipNode (x : Baire) (s : Node) :
    firstNode (zipNode x s) = branchPrefix x s.length := by
  simp [firstNode,zipNode,List.mapIdx_eq_ofFn,branchPrefix,List.map_ofFn,Function.comp_def]

@[simp] theorem secondNode_zipNode (x : Baire) (s : Node) :
    secondNode (zipNode x s) = s := by
  apply List.ext_getElem
  · simp [secondNode,zipNode]
  · intro i hi hi'
    simp [secondNode,zipNode,List.mapIdx_eq_ofFn]

theorem zipNode_append (x : Baire) (s : Node) (n : ℕ) :
    zipNode x (s ++ [n]) = zipNode x s ++ [Nat.pair (x s.length) n] := by
  simp only [zipNode,List.mapIdx_append_one]

def nodeIntoParameter (f : Baire → TreeSpace) (x : Baire)
    (s : Nodes (f x)) : Nodes (parameterTree f) :=
  ⟨zipNode x s.val,(parameterTree_mem_iff f _).mpr
    ⟨x,by simp,by simpa using s.property⟩⟩

theorem child_nodeIntoParameter (f : Baire → TreeSpace) (x : Baire)
    {s t : Nodes (f x)} (hst : Child s t) :
    Child (nodeIntoParameter f x s) (nodeIntoParameter f x t) := by
  obtain ⟨n,hn⟩ := hst
  refine ⟨Nat.pair (x t.val.length) n,?_⟩
  change zipNode x s.val = zipNode x t.val ++ [Nat.pair (x t.val.length) n]
  rw [hn,zipNode_append]

theorem bounded_of_parameterTree (f : Baire → TreeSpace) {a : Ordinal.{0}}
    (h : BoundedTree (parameterTree f) a) (x : Baire) : BoundedTree (f x) a := by
  obtain ⟨ρ,hρ,hchild⟩ := h
  exact ⟨fun s => ρ (nodeIntoParameter f x s),fun s => hρ _,
    fun s t hst => hchild _ _ (child_nodeIntoParameter f x hst)⟩

/-- Analytic boundedness for the exact native tree code and global height
bound used in the mission. No ordinal rank theorem is assumed here. -/
theorem analytic_wellFoundedTree_bounded (A : Set TreeSpace)
    (hA : AnalyticSet A) (hWF : ∀ T ∈ A, ¬ HasBranch T) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ ∀ T ∈ A, BoundedTree T a := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f,hf,hfA⟩
  · exact ⟨0,by exact (Cardinal.isSuccLimit_omega 1).bot_lt,fun T hT => False.elim hT⟩
  · have hnb : ¬ HasBranch (parameterTree f) := by
      intro h
      obtain ⟨x,hx⟩ := branch_of_parameterTree f hf h
      exact hWF (f x) (by rw [← hfA]; exact mem_range_self x) hx
    obtain ⟨a,ha,hab⟩ := exists_countable_bound_of_wellFounded (parameterTree f)
      ((wellFounded_child_iff_no_branch _).mpr hnb)
    refine ⟨a,ha,?_⟩
    intro T hT
    rw [← hfA] at hT
    obtain ⟨x,rfl⟩ := hT
    exact bounded_of_parameterTree f hab x

end FSCofinality.RootedTrees

end
end

-- Original module: FSCofinalityProof.GraphEncodingMarkers
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.GraphCoding

/-- Core vertices receive countably many leaves and one finite marker ring.
Unused ring positions are isolated, so the carrier is independent of colors. -/
inductive MarkerVertex (V : Type) where
  | core : V → MarkerVertex V
  | leaf : V → ℕ → MarkerVertex V
  | ring : V → ℕ → MarkerVertex V

variable {V : Type}

def vertexCode : MarkerVertex V → V ⊕ ((V × ℕ) ⊕ (V × ℕ))
  | .core v => .inl v
  | .leaf v n => .inr (.inl (v,n))
  | .ring v n => .inr (.inr (v,n))

theorem vertexCode_injective : Function.Injective (vertexCode (V := V)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [vertexCode]

instance [Countable V] : Countable (MarkerVertex V) :=
  vertexCode_injective.countable

instance [Infinite V] : Infinite (MarkerVertex V) :=
  Infinite.of_injective MarkerVertex.core (fun _ _ h => MarkerVertex.core.inj h)

def MarkerAdj (E : V → V → Prop) (c : V → ℕ) : MarkerVertex V → MarkerVertex V → Prop
  | .core v,.core w => E v w
  | .core v,.leaf w _ => v = w
  | .leaf v _,.core w => v = w
  | .core v,.ring w i => v = w ∧ i = 0
  | .ring v i,.core w => v = w ∧ i = 0
  | .ring v i,.ring w j => v = w ∧ i < c v + 3 ∧ j < c v + 3 ∧
      (i+1=j ∨ j+1=i ∨ (i=0 ∧ j+1=c v+3) ∨ (j=0 ∧ i+1=c v+3))
  | _,_ => False

theorem markerAdj_symm (E : V → V → Prop) (c : V → ℕ)
    (hE : Symmetric E) : Symmetric (MarkerAdj E c) := by
  intro x y h
  cases x with
  | core v =>
    cases y with
    | core w => exact hE h
    | leaf w n => exact h.symm
    | ring w i => exact ⟨h.1.symm,h.2⟩
  | leaf v n =>
    cases y with
    | core w => exact h.symm
    | leaf w m => exact h
    | ring w i => exact h
  | ring v i =>
    cases y with
    | core w => exact ⟨h.1.symm,h.2⟩
    | leaf w n => exact h
    | ring w j =>
      obtain ⟨rfl,hi,hj,hrel⟩ := h
      exact ⟨rfl,hj,hi,by omega⟩

theorem markerAdj_irrefl (E : V → V → Prop) (c : V → ℕ)
    (hE : Irreflexive E) : Irreflexive (MarkerAdj E c) := by
  intro x h
  cases x with
  | core v => exact hE v h
  | leaf v n => exact h
  | ring v i => simp only [MarkerAdj] at h; omega

theorem core_neighbors_infinite (E : V → V → Prop) (c : V → ℕ) (v : V) :
    {w | MarkerAdj E c (.core v) w}.Infinite := by
  have hi : Function.Injective (fun n : ℕ => MarkerVertex.leaf v n) := by
    intro m n h
    exact (MarkerVertex.leaf.inj h).2
  apply (Set.infinite_range_of_injective hi).mono
  rintro w ⟨n,rfl⟩
  exact rfl

theorem leaf_neighbors_finite (E : V → V → Prop) (c : V → ℕ) (v : V) (n : ℕ) :
    {w | MarkerAdj E c (.leaf v n) w}.Finite := by
  apply (Set.finite_singleton (.core v : MarkerVertex V)).subset
  intro w hw
  cases w <;> simp_all [MarkerAdj]

theorem ring_neighbors_finite (E : V → V → Prop) (c : V → ℕ) (v : V) (i : ℕ) :
    {w | MarkerAdj E c (.ring v i) w}.Finite := by
  have hf : ({MarkerVertex.core v} ∪
      (MarkerVertex.ring v '' {j : ℕ | j < c v+3})).Finite :=
    (Set.finite_singleton _).union ((Set.finite_Iio _).image _)
  apply hf.subset
  intro w hw
  cases w with
  | core u =>
    change v = u ∧ i = 0 at hw
    obtain ⟨rfl,_⟩ := hw
    exact Or.inl rfl
  | leaf u n => exact False.elim hw
  | ring u j =>
    obtain ⟨rfl,_,hj,_⟩ := hw
    exact Or.inr ⟨j,hj,rfl⟩

theorem infinite_neighbors_iff_core (E : V → V → Prop) (c : V → ℕ)
    (w : MarkerVertex V) : {u | MarkerAdj E c w u}.Infinite ↔ ∃ v, w = .core v := by
  cases w with
  | core v => exact ⟨fun _ => ⟨v,rfl⟩,fun _ => core_neighbors_infinite E c v⟩
  | leaf v n => simpa using (leaf_neighbors_finite E c v n).not_infinite
  | ring v i => simpa using (ring_neighbors_finite E c v i).not_infinite

def MarkerIsomorphism (E F : V → V → Prop) (c d : V → ℕ)
    (e : MarkerVertex V ≃ MarkerVertex V) : Prop :=
  ∀ x y, MarkerAdj E c x y ↔ MarkerAdj F d (e x) (e y)

theorem MarkerIsomorphism.symm {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) :
    MarkerIsomorphism F E d c e.symm := by
  intro x y
  simpa only [Equiv.apply_symm_apply] using (h (e.symm x) (e.symm y)).symm

theorem MarkerIsomorphism.infinite_neighbors {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e)
    (v : MarkerVertex V) :
    {u | MarkerAdj E c v u}.Infinite ↔ {u | MarkerAdj F d (e v) u}.Infinite := by
  have heq : {u | MarkerAdj F d (e v) u} = e '' {u | MarkerAdj E c v u} := by
    ext u
    constructor
    · intro hu
      exact ⟨e.symm u,(h v (e.symm u)).mpr (by simpa using hu),by simp⟩
    · rintro ⟨w,hw,rfl⟩
      exact (h v w).mp hw
  rw [heq]
  exact (Set.infinite_image_iff e.injective.injOn).symm

theorem MarkerIsomorphism.core_image {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e)
    (v : V) : ∃ w : V, e (.core v) = .core w :=
  (infinite_neighbors_iff_core F d _).mp
    ((h.infinite_neighbors _).mp (core_neighbors_infinite E c v))

def MarkerIsomorphism.coreMap {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) : V :=
  Classical.choose (h.core_image v)

theorem MarkerIsomorphism.coreMap_spec {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    e (.core v) = .core (h.coreMap v) := Classical.choose_spec (h.core_image v)

theorem MarkerIsomorphism.coreMap_bijective {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) :
    Function.Bijective h.coreMap := by
  constructor
  · intro v w hvw
    have : e (.core v) = e (.core w) := by rw [h.coreMap_spec,h.coreMap_spec,hvw]
    exact MarkerVertex.core.inj (e.injective this)
  · intro w
    refine ⟨h.symm.coreMap w,?_⟩
    have he : e (.core (h.symm.coreMap w)) = .core w := by
      rw [← h.symm.coreMap_spec]
      simp
    exact MarkerVertex.core.inj ((h.coreMap_spec _).symm.trans he)

def MarkerIsomorphism.coreEquiv {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) : V ≃ V :=
  Equiv.ofBijective h.coreMap h.coreMap_bijective

theorem MarkerIsomorphism.coreEquiv_spec {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    e (.core v) = .core (h.coreEquiv v) := h.coreMap_spec v

end FSCofinality.GraphCoding

end
end

-- Original module: FSCofinalityProof.GraphEncodingRecovery
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.GraphCoding

variable {V : Type}

theorem MarkerIsomorphism.is_core_iff {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e)
    (x : MarkerVertex V) : (∃ v, x = .core v) ↔ ∃ v, e x = .core v := by
  rw [← infinite_neighbors_iff_core E c x,← infinite_neighbors_iff_core F d (e x)]
  exact h.infinite_neighbors x

theorem MarkerIsomorphism.ring_image_not_core {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e)
    (v : V) (i : ℕ) (w : V) : e (.ring v i) ≠ .core w := by
  intro he
  obtain ⟨u,hu⟩ := (h.is_core_iff (.ring v i)).mpr ⟨w,he⟩
  cases hu

theorem leaf_adj_iff_core (E : V → V → Prop) (c : V → ℕ)
    (v : V) (n : ℕ) (x : MarkerVertex V) :
    MarkerAdj E c (.leaf v n) x ↔ x = .core v := by
  cases x <;> simp [MarkerAdj,eq_comm]

theorem ring_adj_noncore (E : V → V → Prop) (c : V → ℕ)
    (v : V) (i : ℕ) (x : MarkerVertex V)
    (h : MarkerAdj E c (.ring v i) x) (hn : ∀ w, x ≠ .core w) :
    ∃ j, j < c v+3 ∧ x = .ring v j := by
  cases x with
  | core w => exact False.elim (hn w rfl)
  | leaf w n => exact False.elim h
  | ring w j =>
    obtain ⟨rfl,_,hj,_⟩ := h
    exact ⟨j,hj,rfl⟩

theorem MarkerIsomorphism.ring_zero_image {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    e (.ring v 0) = .ring (h.coreEquiv v) 0 := by
  have hb : MarkerAdj F d (e (.ring v 0)) (.core (h.coreEquiv v)) := by
    rw [← h.coreEquiv_spec v]
    exact (h _ _).mp ⟨rfl,rfl⟩
  cases he : e (.ring v 0) with
  | core w => exact False.elim (h.ring_image_not_core v 0 w he)
  | leaf w n =>
    have he01 : MarkerAdj E c (.ring v 0) (.ring v 1) :=
      ⟨rfl,by omega,by omega,Or.inl rfl⟩
    have hi := (h _ _).mp he01
    rw [he] at hi
    have hc := (leaf_adj_iff_core F d w n _).mp hi
    exact False.elim (h.ring_image_not_core v 1 w hc)
  | ring w i =>
    rw [he] at hb
    obtain ⟨rfl,rfl⟩ := hb
    rfl

theorem MarkerIsomorphism.ring_image_exists {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    ∀ i, i < c v+3 → ∃ j, j < d (h.coreEquiv v)+3 ∧
      e (.ring v i) = .ring (h.coreEquiv v) j := by
  intro i
  induction i with
  | zero =>
    intro hi
    exact ⟨0,by omega,h.ring_zero_image v⟩
  | succ i ih =>
    intro hi
    obtain ⟨j,hj,he⟩ := ih (by omega)
    have hs : MarkerAdj E c (.ring v i) (.ring v (i+1)) :=
      ⟨rfl,by omega,hi,Or.inl rfl⟩
    have ht := (h _ _).mp hs
    rw [he] at ht
    exact ring_adj_noncore F d _ j _ ht (h.ring_image_not_core v (i+1))

theorem MarkerIsomorphism.ring_size_le {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    c v+3 ≤ d (h.coreEquiv v)+3 := by
  let f : Fin (c v+3) → Fin (d (h.coreEquiv v)+3) := fun i =>
    ⟨Classical.choose (h.ring_image_exists v i i.isLt),
      (Classical.choose_spec (h.ring_image_exists v i i.isLt)).1⟩
  have hf (i : Fin (c v+3)) : e (.ring v i) = .ring (h.coreEquiv v) (f i) :=
    (Classical.choose_spec (h.ring_image_exists v i i.isLt)).2
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have heq : e (.ring v i) = e (.ring v j) := by rw [hf i,hf j,hij]
    exact (MarkerVertex.ring.inj (e.injective heq)).2
  simpa using Fintype.card_le_of_injective f hinj

theorem MarkerIsomorphism.symm_coreEquiv_apply {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    h.symm.coreEquiv (h.coreEquiv v) = v := by
  have hh := h.symm.coreEquiv_spec (h.coreEquiv v)
  rw [← h.coreEquiv_spec v,Equiv.symm_apply_apply] at hh
  exact MarkerVertex.core.inj hh.symm

theorem MarkerIsomorphism.color_preserved {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v : V) :
    c v = d (h.coreEquiv v) := by
  have hle := h.ring_size_le v
  have hge := h.symm.ring_size_le (h.coreEquiv v)
  rw [h.symm_coreEquiv_apply] at hge
  omega

theorem MarkerIsomorphism.core_adj_preserved {E F : V → V → Prop} {c d : V → ℕ}
    {e : MarkerVertex V ≃ MarkerVertex V} (h : MarkerIsomorphism E F c d e) (v w : V) :
    E v w ↔ F (h.coreEquiv v) (h.coreEquiv w) := by
  have hh := h (.core v) (.core w)
  rw [h.coreEquiv_spec,h.coreEquiv_spec] at hh
  exact hh

def liftCoreEquiv (f : V ≃ V) : MarkerVertex V ≃ MarkerVertex V where
  toFun
    | .core v => .core (f v)
    | .leaf v n => .leaf (f v) n
    | .ring v n => .ring (f v) n
  invFun
    | .core v => .core (f.symm v)
    | .leaf v n => .leaf (f.symm v) n
    | .ring v n => .ring (f.symm v) n
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro x; cases x <;> simp

theorem liftCoreEquiv_isomorphism {E F : V → V → Prop} {c d : V → ℕ}
    (f : V ≃ V) (hc : ∀ v, c v = d (f v))
    (hE : ∀ v w, E v w ↔ F (f v) (f w)) :
    MarkerIsomorphism E F c d (liftCoreEquiv f) := by
  intro x y
  cases x with
  | core v =>
    cases y with
    | core w => exact hE v w
    | leaf w n => exact f.injective.eq_iff.symm
    | ring w i => exact and_congr f.injective.eq_iff.symm Iff.rfl
  | leaf v n =>
    cases y with
    | core w => exact f.injective.eq_iff.symm
    | leaf w m => exact Iff.rfl
    | ring w i => exact Iff.rfl
  | ring v i =>
    cases y with
    | core w => exact and_congr f.injective.eq_iff.symm Iff.rfl
    | leaf w n => exact Iff.rfl
    | ring w j =>
      change (v=w ∧ i<c v+3 ∧ j<c v+3 ∧ _) ↔
        (f v=f w ∧ i<d (f v)+3 ∧ j<d (f v)+3 ∧ _)
      rw [hc v]
      exact and_congr f.injective.eq_iff.symm Iff.rfl

/-- Finite marker rings preserve exactly the original colored-graph
isomorphism problem. This statement includes arbitrary underlying relations. -/
theorem marker_encoding_iff (E F : V → V → Prop) (c d : V → ℕ) :
    (∃ e : MarkerVertex V ≃ MarkerVertex V, MarkerIsomorphism E F c d e) ↔
      ∃ f : V ≃ V, (∀ v, c v = d (f v)) ∧
        ∀ v w, E v w ↔ F (f v) (f w) := by
  constructor
  · rintro ⟨e,h⟩
    exact ⟨h.coreEquiv,h.color_preserved,h.core_adj_preserved⟩
  · rintro ⟨f,hc,hE⟩
    exact ⟨liftCoreEquiv f,liftCoreEquiv_isomorphism f hc hE⟩

end FSCofinality.GraphCoding

end
end

-- Original module: FSCofinalityProof.GraphEncodingIncidence
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.GraphCoding

def symbolCode (L : CountableRelationalLanguage) : L.Symbol ↪ ℕ := by
  letI := Encodable.ofCountable L.Symbol
  exact ⟨Encodable.encode,Encodable.encode_injective⟩

inductive IncidenceVertex (L : CountableRelationalLanguage) where
  | element : ℕ → IncidenceVertex L
  | tuple : Coordinate L → IncidenceVertex L
  | occurrence : (c : Coordinate L) → Fin (L.arity c.1) → IncidenceVertex L

def incidenceVertexCode (L : CountableRelationalLanguage) : IncidenceVertex L →
    ℕ ⊕ (Coordinate L ⊕ (Σ c : Coordinate L, Fin (L.arity c.1)))
  | .element n => .inl n
  | .tuple c => .inr (.inl c)
  | .occurrence c i => .inr (.inr ⟨c,i⟩)

theorem incidenceVertexCode_injective (L : CountableRelationalLanguage) :
    Function.Injective (incidenceVertexCode L) := by
  intro x y h
  cases x <;> cases y <;> simp_all [incidenceVertexCode]

instance (L : CountableRelationalLanguage) : Countable (IncidenceVertex L) :=
  (incidenceVertexCode_injective L).countable

instance (L : CountableRelationalLanguage) : Infinite (IncidenceVertex L) :=
  Infinite.of_injective IncidenceVertex.element (fun _ _ h => IncidenceVertex.element.inj h)

def IncidenceAdj {L : CountableRelationalLanguage} :
    IncidenceVertex L → IncidenceVertex L → Prop
  | .element n,.occurrence c i => c.2 i = n
  | .occurrence c i,.element n => c.2 i = n
  | .tuple d,.occurrence c _ => c = d
  | .occurrence c _,.tuple d => c = d
  | _,_ => False

theorem incidenceAdj_symm {L : CountableRelationalLanguage} (x y : IncidenceVertex L) :
    IncidenceAdj x y ↔ IncidenceAdj y x := by
  cases x <;> cases y <;> exact Iff.rfl

theorem incidenceAdj_irrefl {L : CountableRelationalLanguage} (x : IncidenceVertex L) :
    ¬ IncidenceAdj x x := by
  cases x <;> exact not_false

def incidenceColor {L : CountableRelationalLanguage} (M : Structures L) :
    IncidenceVertex L → ℕ
  | .element _ => 0
  | .tuple c => 2 * Nat.pair (symbolCode L c.1) (M c).toNat + 1
  | .occurrence _ i => 2 * i.val + 2

theorem incidenceColor_eq_zero_iff {L : CountableRelationalLanguage}
    (M : Structures L) (v : IncidenceVertex L) :
    incidenceColor M v = 0 ↔ ∃ n, v = .element n := by
  cases v <;> simp only [incidenceColor]
  · simp
  · constructor <;> intro h
    · omega
    · obtain ⟨n,hn⟩ := h; cases hn
  · constructor <;> intro h
    · omega
    · obtain ⟨n,hn⟩ := h; cases hn

def coordinateMap {L : CountableRelationalLanguage} (e : ℕ ≃ ℕ)
    (c : Coordinate L) : Coordinate L := ⟨c.1,e ∘ c.2⟩

def coordinateEquiv (L : CountableRelationalLanguage) (e : ℕ ≃ ℕ) :
    Coordinate L ≃ Coordinate L where
  toFun := coordinateMap e
  invFun := coordinateMap e.symm
  left_inv := by intro c; rcases c with ⟨s,a⟩; simp [coordinateMap,Function.comp_def]
  right_inv := by intro c; rcases c with ⟨s,a⟩; simp [coordinateMap,Function.comp_def]

@[simp] theorem coordinateMap_eq_iff {L : CountableRelationalLanguage} (e : ℕ ≃ ℕ)
    (c d : Coordinate L) : coordinateMap e c = coordinateMap e d ↔ c = d :=
  (coordinateEquiv L e).injective.eq_iff

def relabelVertex {L : CountableRelationalLanguage} (e : ℕ ≃ ℕ) :
    IncidenceVertex L → IncidenceVertex L
  | .element n => .element (e n)
  | .tuple c => .tuple (coordinateMap e c)
  | .occurrence c i => .occurrence (coordinateMap e c) i

def incidenceEquiv (L : CountableRelationalLanguage) (e : ℕ ≃ ℕ) :
    IncidenceVertex L ≃ IncidenceVertex L where
  toFun := relabelVertex e
  invFun := relabelVertex e.symm
  left_inv := by
    intro v
    cases v with
    | element n => simp [relabelVertex]
    | tuple c => rcases c with ⟨s,a⟩; simp [relabelVertex,coordinateMap,Function.comp_def]
    | occurrence c i => rcases c with ⟨s,a⟩; simp [relabelVertex,coordinateMap,Function.comp_def]
  right_inv := by
    intro v
    cases v with
    | element n => simp [relabelVertex]
    | tuple c => rcases c with ⟨s,a⟩; simp [relabelVertex,coordinateMap,Function.comp_def]
    | occurrence c i => rcases c with ⟨s,a⟩; simp [relabelVertex,coordinateMap,Function.comp_def]

theorem incidenceEquiv_adj (L : CountableRelationalLanguage) (e : ℕ ≃ ℕ)
    (v w : IncidenceVertex L) : IncidenceAdj v w ↔
      IncidenceAdj (incidenceEquiv L e v) (incidenceEquiv L e w) := by
  cases v <;> cases w <;>
    simp only [incidenceEquiv,Equiv.coe_fn_mk,relabelVertex,IncidenceAdj,coordinateMap_eq_iff]
  all_goals first | exact Iff.rfl | exact e.injective.eq_iff.symm

theorem isomorphic_incidenceColor {L : CountableRelationalLanguage} {M N : Structures L}
    (e : ℕ ≃ ℕ) (he : ∀ s a, M ⟨s,a⟩ = N ⟨s,e ∘ a⟩) (v : IncidenceVertex L) :
    incidenceColor M v = incidenceColor N (incidenceEquiv L e v) := by
  cases v with
  | element n => rfl
  | tuple c =>
    rcases c with ⟨s,a⟩
    simp only [incidenceColor,incidenceEquiv,Equiv.coe_fn_mk,relabelVertex,coordinateMap]
    rw [he s a]
  | occurrence c i => rfl

theorem Isomorphic.incidence {L : CountableRelationalLanguage} {M N : Structures L}
    (h : Isomorphic M N) :
    ∃ e : IncidenceVertex L ≃ IncidenceVertex L,
      (∀ v, incidenceColor M v = incidenceColor N (e v)) ∧
      ∀ v w, IncidenceAdj v w ↔ IncidenceAdj (e v) (e w) := by
  obtain ⟨e,he⟩ := h
  exact ⟨incidenceEquiv L e,isomorphic_incidenceColor e he,incidenceEquiv_adj L e⟩

end FSCofinality.GraphCoding

end
end

-- Original module: FSCofinalityProof.GraphEncodingReflection
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.GraphCoding

theorem element_range_iff {L : CountableRelationalLanguage} (M : Structures L)
    (v : IncidenceVertex L) :
    v ∈ Set.range (IncidenceVertex.element (L := L)) ↔ incidenceColor M v = 0 := by
  constructor
  · rintro ⟨n,rfl⟩
    rfl
  · intro h
    obtain ⟨n,hn⟩ := (incidenceColor_eq_zero_iff M v).mp h
    exact ⟨n,hn.symm⟩

def elementRangeEquiv (L : CountableRelationalLanguage) :
    ℕ ≃ Set.range (IncidenceVertex.element (L := L)) :=
  Equiv.ofInjective IncidenceVertex.element (fun _ _ h => IncidenceVertex.element.inj h)

def elementSubtypeEquiv {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v)) :
    Set.range (IncidenceVertex.element (L := L)) ≃
      Set.range (IncidenceVertex.element (L := L)) :=
  e.subtypeEquiv (fun v => by rw [element_range_iff M,element_range_iff N,hc v])

def elementPermutation {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v)) : ℕ ≃ ℕ :=
  ((elementRangeEquiv L).trans (elementSubtypeEquiv e hc)).trans (elementRangeEquiv L).symm

theorem elementPermutation_spec {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v)) (n : ℕ) :
    e (.element n) = .element (elementPermutation e hc n) := by
  have h := congrArg Subtype.val ((elementRangeEquiv L).apply_symm_apply
    (elementSubtypeEquiv e hc (elementRangeEquiv L n)))
  exact h.symm

theorem tuple_image {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v)) (c : Coordinate L) :
    ∃ b : Coordinate L, e (.tuple c) = .tuple b ∧ b.1 = c.1 ∧ M c = N b := by
  have hh := hc (.tuple c)
  cases he : e (.tuple c) with
  | element n =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    omega
  | occurrence b i =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    omega
  | tuple b =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    have hp : Nat.pair (symbolCode L c.1) (M c).toNat =
        Nat.pair (symbolCode L b.1) (N b).toNat := by omega
    obtain ⟨hs,hb⟩ := Nat.pair_eq_pair.mp hp
    refine ⟨b,rfl,(symbolCode L).injective hs.symm,?_⟩
    cases hm : M c <;> cases hn : N b <;> simp_all

theorem occurrence_image {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v))
    (c : Coordinate L) (i : Fin (L.arity c.1)) :
    ∃ (b : Coordinate L) (j : Fin (L.arity b.1)),
      e (.occurrence c i) = .occurrence b j ∧ j.val = i.val := by
  have hh := hc (.occurrence c i)
  cases he : e (.occurrence c i) with
  | element n =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    omega
  | tuple b =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    omega
  | occurrence b j =>
    rw [he] at hh
    simp only [incidenceColor] at hh
    exact ⟨b,j,rfl,by omega⟩

theorem isomorphic_of_incidence {L : CountableRelationalLanguage} {M N : Structures L}
    (e : IncidenceVertex L ≃ IncidenceVertex L)
    (hc : ∀ v, incidenceColor M v = incidenceColor N (e v))
    (hE : ∀ v w, IncidenceAdj v w ↔ IncidenceAdj (e v) (e w)) : Isomorphic M N := by
  let f := elementPermutation e hc
  refine ⟨f,fun s a => ?_⟩
  obtain ⟨⟨t,b⟩,ht,hsym,htruth⟩ := tuple_image e hc (⟨s,a⟩ : Coordinate L)
  dsimp at hsym
  subst t
  have hb : b = f ∘ a := by
    funext i
    obtain ⟨c,j,hj,hji⟩ := occurrence_image e hc (⟨s,a⟩ : Coordinate L) i
    have htu : IncidenceAdj (.occurrence (⟨s,a⟩ : Coordinate L) i) (.tuple ⟨s,a⟩) := rfl
    have htu' := (hE _ _).mp htu
    rw [hj,ht] at htu'
    change c = (⟨s,b⟩ : Coordinate L) at htu'
    subst c
    have hji' : j = i := Fin.ext hji
    subst j
    have hel : IncidenceAdj (.occurrence (⟨s,a⟩ : Coordinate L) i) (.element (a i)) := rfl
    have hel' := (hE _ _).mp hel
    rw [hj,elementPermutation_spec e hc (a i)] at hel'
    exact hel'
  simpa only [hb] using htruth

theorem incidence_encoding_iff {L : CountableRelationalLanguage} (M N : Structures L) :
    Isomorphic M N ↔ ∃ e : IncidenceVertex L ≃ IncidenceVertex L,
      (∀ v, incidenceColor M v = incidenceColor N (e v)) ∧
      ∀ v w, IncidenceAdj v w ↔ IncidenceAdj (e v) (e w) := by
  constructor
  · exact Isomorphic.incidence
  · rintro ⟨e,hc,hE⟩
    exact isomorphic_of_incidence e hc hE

end FSCofinality.GraphCoding

end
end

-- Original module: FSCofinalityProof.GraphEncoding
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set TopologicalSpace

namespace FSCofinality.GraphCoding

theorem continuous_incidenceColor {L : CountableRelationalLanguage} (v : IncidenceVertex L) :
    Continuous (fun M : Structures L => incidenceColor M v) := by
  cases v with
  | element n => exact continuous_const
  | occurrence c i => exact continuous_const
  | tuple c =>
    have hc : Continuous (fun M : Structures L => M c) := continuous_apply c
    exact (continuous_of_discreteTopology : Continuous (fun b : Bool =>
      2 * Nat.pair (symbolCode L c.1) b.toNat + 1)).comp hc

theorem continuous_markerAdj {P V : Type} [TopologicalSpace P]
    (E : V → V → Prop) (c : P → V → ℕ) (hc : ∀ v, Continuous (fun p => c p v))
    (x y : MarkerVertex V) :
    Continuous (fun p => decide (MarkerAdj E (c p) x y)) := by
  have hconst (q : P → Prop) (r : Prop) (h : ∀ p, q p ↔ r) :
      Continuous (fun p => decide (q p)) := by
    have heq : (fun p => decide (q p)) = (fun _ : P => decide r) :=
      funext (fun p => decide_eq_decide.mpr (h p))
    rw [heq]
    exact continuous_const
  cases x with
  | core v =>
    cases y with
    | core w => exact hconst _ (E v w) (fun _ => Iff.rfl)
    | leaf w n => exact hconst _ (v=w) (fun _ => Iff.rfl)
    | ring w i => exact hconst _ (v=w ∧ i=0) (fun _ => Iff.rfl)
  | leaf v n =>
    cases y with
    | core w => exact hconst _ (v=w) (fun _ => Iff.rfl)
    | leaf w m => exact hconst _ False (fun _ => Iff.rfl)
    | ring w i => exact hconst _ False (fun _ => Iff.rfl)
  | ring v i =>
    cases y with
    | core w => exact hconst _ (v=w ∧ i=0) (fun _ => Iff.rfl)
    | leaf w n => exact hconst _ False (fun _ => Iff.rfl)
    | ring w j =>
      have hc' := (continuous_of_discreteTopology : Continuous (fun k : ℕ =>
        decide (v=w ∧ i<k+3 ∧ j<k+3 ∧
          (i+1=j ∨ j+1=i ∨ (i=0 ∧ j+1=k+3) ∨ (j=0 ∧ i+1=k+3))))).comp (hc v)
      convert hc' using 1
      funext p
      exact decide_eq_decide.mpr Iff.rfl

def vertexEnumeration (L : CountableRelationalLanguage) :
    ℕ ≃ MarkerVertex (IncidenceVertex L) := Classical.choice inferInstance

def graphCode {L : CountableRelationalLanguage} (M : Structures L) (p : ℕ × ℕ) : Bool :=
  decide (MarkerAdj (@IncidenceAdj L) (incidenceColor M)
    (vertexEnumeration L p.1) (vertexEnumeration L p.2))

theorem graphCode_condition {L : CountableRelationalLanguage} (M : Structures L) :
    GraphCondition (graphCode M) := by
  constructor
  · intro n
    exact decide_eq_false_iff_not.mpr
      (markerAdj_irrefl (@IncidenceAdj L) (incidenceColor M) incidenceAdj_irrefl _)
  · intro m n
    apply decide_eq_decide.mpr
    have hs : Symmetric (@IncidenceAdj L) := fun _ _ h => (incidenceAdj_symm _ _).mp h
    exact ⟨fun h => markerAdj_symm (@IncidenceAdj L) (incidenceColor M) hs h,
      fun h => markerAdj_symm (@IncidenceAdj L) (incidenceColor M) hs h⟩

def encodeStructure {L : CountableRelationalLanguage} (M : Structures L) : GraphSpace :=
  ⟨graphCode M,graphCode_condition M⟩

theorem continuous_encodeStructure (L : CountableRelationalLanguage) :
    Continuous (encodeStructure (L := L)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro p
  exact continuous_markerAdj (@IncidenceAdj L) incidenceColor continuous_incidenceColor
    (vertexEnumeration L p.1) (vertexEnumeration L p.2)

theorem measurable_encodeStructure (L : CountableRelationalLanguage) :
    Measurable (encodeStructure (L := L)) := (continuous_encodeStructure L).measurable

/-- Uniform graph coding for every fixed countable relational language.
The map is continuous, and its graph isomorphisms reflect actual structure
isomorphism, including all nullary relation truth values. -/
theorem isomorphic_iff_graphIsomorphic {L : CountableRelationalLanguage}
    (M N : Structures L) :
    Isomorphic M N ↔ GraphIsomorphic (encodeStructure M) (encodeStructure N) := by
  rw [incidence_encoding_iff]
  constructor
  · rintro ⟨e,hc,hE⟩
    let q := liftCoreEquiv e
    have hq : MarkerIsomorphism (@IncidenceAdj L) (@IncidenceAdj L)
        (incidenceColor M) (incidenceColor N) q := liftCoreEquiv_isomorphism e hc hE
    let p : ℕ ≃ ℕ := ((vertexEnumeration L).trans q).trans (vertexEnumeration L).symm
    refine ⟨p,fun m n => ?_⟩
    change decide (MarkerAdj _ _ _ _) = decide (MarkerAdj _ _ _ _)
    apply decide_eq_decide.mpr
    simpa only [p,Equiv.trans_apply,Equiv.apply_symm_apply] using
      hq (vertexEnumeration L m) (vertexEnumeration L n)
  · rintro ⟨p,hp⟩
    let q : MarkerVertex (IncidenceVertex L) ≃ MarkerVertex (IncidenceVertex L) :=
      (((vertexEnumeration L).symm).trans p).trans (vertexEnumeration L)
    have hq : MarkerIsomorphism (@IncidenceAdj L) (@IncidenceAdj L)
        (incidenceColor M) (incidenceColor N) q := by
      intro x y
      have h := hp ((vertexEnumeration L).symm x) ((vertexEnumeration L).symm y)
      change decide (MarkerAdj _ _ _ _) = decide (MarkerAdj _ _ _ _) at h
      have h' := decide_eq_decide.mp h
      simpa only [q,Equiv.trans_apply,Equiv.apply_symm_apply] using h'
    exact (marker_encoding_iff (@IncidenceAdj L) (@IncidenceAdj L)
      (incidenceColor M) (incidenceColor N)).mp ⟨q,hq⟩

theorem structures_reduces_graphs (L : CountableRelationalLanguage) :
    BorelReducible (@Isomorphic L) GraphIsomorphic :=
  ⟨encodeStructure,measurable_encodeStructure L,isomorphic_iff_graphIsomorphic⟩

end FSCofinality.GraphCoding

end
end

-- Original module: FSCofinalityProof.NoncompleteGraphs
section


set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace FSCofinality

theorem exists_positive_countable_padding_bound (b : Ordinal.{0}) (hb : b < Ordinal.omega 1) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ 0 < a ∧ Padding.cutoff b ≤ a := by
  let a := Padding.cutoff (Order.succ b)
  have hω : Ordinal.omega0 < Ordinal.omega 1 := by
    apply Cardinal.lt_omega_iff_card_lt.mpr
    simpa only [Ordinal.card_omega0] using Cardinal.aleph0_lt_aleph_one
  have hs : Order.succ b < Ordinal.omega 1 := (Cardinal.isSuccLimit_omega 1).succ_lt hb
  refine ⟨a,Ordinal.isPrincipal_mul_omega 1 hω hs,?_,?_⟩
  · change 0 < Padding.cutoff (Order.succ b)
    simpa [Padding.cutoff] using
      Padding.cutoff_add_nat_lt (Ordinal.succ_pos b) 0
  · exact Padding.cutoff_mono (Order.le_succ b)

theorem Padding.not_isomorphic_padded_fat
    (a : Ordinal.{0}) (C : List ℕ → ℕ) (eP : ℕ ≃ Padding.PaddedNode a)
    (eF : ℕ ≃ Padding.FatNode a) :
    ¬ Isomorphic (Padding.code (Padding.PaddedNode.tree a C) eP)
      (Padding.code (Padding.FatNode.tree a (C [])) eF) := by
  intro h
  obtain ⟨e⟩ := Padding.treeIso_of_code_isomorphic
    (Padding.PaddedNode.tree a C) (Padding.FatNode.tree a (C [])) eP eF h
  have hp := Padding.PaddedNode.branch_from_original a C []
  have hf := e.map_branch hp
  rw [show (Sum.inl [] : Padding.PaddedNode a) = (Padding.PaddedNode.tree a C).root from rfl,
    e.roots] at hf
  exact Padding.no_branch_of_finite_rank (Padding.FatNode.tree a (C []))
    (Padding.FatNode.tree a (C [])).root WithTop.coe_ne_top hf

/-- Graph isomorphism is non-Borel, derived here from analytic boundedness,
the fully constructed fat trees, and the faithful native graph encoding. -/
theorem graphIsomorphic_not_measurableSet :
    ¬ MeasurableSet {p : GraphSpace × GraphSpace | GraphIsomorphic p.1 p.2} := by
  intro hGraph
  let L := Padding.treeLanguage
  have hIso : MeasurableSet {p : Structures L × Structures L | Isomorphic p.1 p.2} := by
    have hpre := hGraph.preimage
      (((GraphCoding.measurable_encodeStructure L).comp measurable_fst).prodMk
        ((GraphCoding.measurable_encodeStructure L).comp measurable_snd))
    convert hpre using 1
    ext p
    exact GraphCoding.isomorphic_iff_graphIsomorphic p.1 p.2
  let S : Set (Structures L × Structures L) := {p | ¬ Isomorphic p.1 p.2}
  let treeMap : Structures L × Structures L → RootedTrees.TreeSpace :=
    fun p => PartialIso.attemptTree p.1 p.2
  have hS : MeasurableSet S := hIso.compl
  have hA : AnalyticSet (treeMap '' S) := hS.analyticSet_image PartialIso.measurable_attemptTree
  have hWF : ∀ T ∈ treeMap '' S, ¬ RootedTrees.HasBranch T := by
    rintro T ⟨⟨M,N⟩,hMN,rfl⟩ hbranch
    exact hMN ((PartialIso.branch_iff_isomorphic M N).mp hbranch)
  obtain ⟨b,hb,hbound⟩ := RootedTrees.analytic_wellFoundedTree_bounded (treeMap '' S) hA hWF
  obtain ⟨a,ha,hpos,hba⟩ := exists_positive_countable_padding_bound b hb
  let M := Padding.code (Padding.PaddedNode.tree a (fun _ => 0)) (Padding.paddedEnumeration a ha)
  let N := Padding.code (Padding.FatNode.tree a 0) (Padding.fatEnumeration a ha hpos)
  have hBF : PartialIso.BackAndForth M N b [] :=
    Padding.fat_padding_on_nat a b ha hpos hba (fun _ => 0)
  have hnon : ¬ Isomorphic M N := Padding.not_isomorphic_padded_fat a (fun _ => 0) _ _
  have hT : RootedTrees.BoundedTree (PartialIso.attemptTree M N) b :=
    hbound _ ⟨(M,N),hnon,rfl⟩
  exact PartialIso.not_bounded_attemptTree_of_backAndForth b hBF hT

end FSCofinality

end
end

-- Original module: FSCofinalityProof.NoncompleteBoundedInvariant
section


set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace FSCofinality

/-- Every Borel invariant real is constant on sufficiently high
back-and-forth equivalence. The countable ordinal bound follows from
analytic boundedness applied to the actual partial-isomorphism trees
of pairs with different parameter values. -/
theorem exists_backAndForth_bound_for_invariant
    (L : CountableRelationalLanguage)
    (parameter : Structures L → (ℕ → Bool)) (hp : Measurable parameter)
    (hinv : ∀ M N, Isomorphic M N → parameter M = parameter N) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧
      ∀ M N : Structures L, PartialIso.BackAndForth M N a [] → parameter M = parameter N := by
  let S : Set (Structures L × Structures L) := {p | parameter p.1 ≠ parameter p.2}
  have hS : MeasurableSet S :=
    (measurableSet_eq_fun (hp.comp measurable_fst) (hp.comp measurable_snd)).compl
  let treeMap : Structures L × Structures L → RootedTrees.TreeSpace :=
    fun p => PartialIso.attemptTree p.1 p.2
  have hA : AnalyticSet (treeMap '' S) := hS.analyticSet_image PartialIso.measurable_attemptTree
  have hWF : ∀ T ∈ treeMap '' S, ¬ RootedTrees.HasBranch T := by
    rintro T ⟨⟨M,N⟩,hMN,rfl⟩ hbranch
    apply hMN
    apply hinv M N
    apply (PartialIso.branch_iff_isomorphic M N).mp
    exact hbranch
  obtain ⟨a,ha,hbound⟩ := RootedTrees.analytic_wellFoundedTree_bounded (treeMap '' S) hA hWF
  refine ⟨a,ha,fun M N hBF => ?_⟩
  by_contra hMN
  have hT : RootedTrees.BoundedTree (PartialIso.attemptTree M N) a :=
    hbound _ ⟨(M,N),hMN,rfl⟩
  exact PartialIso.not_bounded_attemptTree_of_backAndForth a hBF hT

end FSCofinality

end
end

-- Original module: FSCofinalityProof.NoncompletePrinciple
section


set_option autoImplicit false
noncomputable section
open Set

namespace FSCofinality

/-- The precise conclusion needed from the invariant-real-parameter
argument: every Borel invariant real has a fiber containing a full copy
of the original classification problem. -/
def InvariantRealFiberProperty {X : Type} [MeasurableSpace X]
    (E : X → X → Prop) : Prop :=
  ∀ h : X → (ℕ → Bool), Measurable h →
    (∀ x y, E x y → h x = h y) →
    ∃ (r : ℕ → Bool) (g : X → X), Measurable g ∧
      (∀ x y, E x y ↔ E (g x) (g y)) ∧ ∀ x, h (g x) = r

/-- The noncompleteness implication is purely measurable once the
invariant-real-fiber theorem and non-Borelness of the source relation
have been established. Both substantive source facts remain explicit. -/
theorem not_borelReducible_of_invariant_parameter
    {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop)
    (hE : ¬ MeasurableSet {p : X × X | E p.1 p.2})
    (hprime : InvariantRealFiberProperty E)
    (parameter : Y → (ℕ → Bool)) (hp : Measurable parameter)
    (hinv : ∀ y z, F y z → parameter y = parameter z)
    (hfiber : ∀ r : ℕ → Bool,
      MeasurableSet {p : {y : Y // parameter y = r} × {y : Y // parameter y = r} |
        F p.1.val p.2.val}) :
    ¬ BorelReducible E F := by
  rintro ⟨f,hf,hred⟩
  obtain ⟨r,g,hg,hredg,hconstant⟩ := hprime (parameter ∘ f) (hp.comp hf)
    (fun x y hxy => hinv (f x) (f y) ((hred x y).mp hxy))
  let q : X → {y : Y // parameter y = r} := fun x => ⟨f (g x),hconstant x⟩
  have hq : Measurable q := (hf.comp hg).subtype_mk
  have htest : MeasurableSet {p : X × X | F (f (g p.1)) (f (g p.2))} := by
    exact (hfiber r).preimage ((hq.comp measurable_fst).prodMk (hq.comp measurable_snd))
  apply hE
  convert htest using 1
  ext p
  exact (hredg p.1 p.2).trans (hred (g p.1) (g p.2))

/-- The manuscript's noncompleteness theorem, with its two source
foundations isolated for later discharge. -/
theorem not_graph_reducible_of_invariant_parameter
    {L : CountableRelationalLanguage} (K : Set (Structures L))
    (graph_nonBorel : ¬ MeasurableSet {p : GraphSpace × GraphSpace |
      GraphIsomorphic p.1 p.2})
    (graph_parameter_fiber : InvariantRealFiberProperty GraphIsomorphic)
    (parameter : K → (ℕ → Bool)) (hp : Measurable parameter)
    (hinv : ∀ M N : K, IsomorphismOn K M N → parameter M = parameter N)
    (hfiber : ∀ r : ℕ → Bool,
      MeasurableSet {p : {M : K // parameter M = r} × {M : K // parameter M = r} |
        IsomorphismOn K p.1.val p.2.val}) :
    ¬ graphRelation.Reduces (classRelation L K) :=
  not_borelReducible_of_invariant_parameter GraphIsomorphic (IsomorphismOn K)
    graph_nonBorel graph_parameter_fiber parameter hp hinv hfiber

end FSCofinality

end
end

-- Original module: FSCofinalityProof.NoncompleteInvariantReal
section


set_option autoImplicit false
noncomputable section

namespace FSCofinality

/-- The manuscript's invariant-real-parameter proposition, proved from
analytic boundedness and the explicit faithful fat-padding reduction. -/
theorem graph_invariantRealFiberProperty : InvariantRealFiberProperty GraphIsomorphic := by
  intro h hh hinv
  let parameter : Structures Padding.treeLanguage → (ℕ → Bool) :=
    h ∘ GraphCoding.encodeStructure
  have hp : Measurable parameter := hh.comp (GraphCoding.measurable_encodeStructure _)
  have hpinv : ∀ M N : Structures Padding.treeLanguage,
      Isomorphic M N → parameter M = parameter N := by
    intro M N hMN
    exact hinv _ _ ((GraphCoding.isomorphic_iff_graphIsomorphic M N).mp hMN)
  obtain ⟨b,hb,hconstant⟩ := exists_backAndForth_bound_for_invariant Padding.treeLanguage parameter hp hpinv
  obtain ⟨a,ha,hpos,hba⟩ := exists_positive_countable_padding_bound b hb
  let G₀ : GraphSpace := ⟨fun _ => false,⟨fun _ => rfl,fun _ _ => rfl⟩⟩
  let N : Structures Padding.treeLanguage :=
    Padding.code (Padding.FatNode.tree a (Padding.tupleColor G₀ []))
      (Padding.fatEnumeration a ha hpos)
  let g : GraphSpace → GraphSpace :=
    GraphCoding.encodeStructure ∘ Padding.paddedGraphCode a ha
  have hg : Measurable g := (GraphCoding.measurable_encodeStructure _).comp
    (Padding.measurable_paddedGraphCode a ha)
  have hred : ∀ G H : GraphSpace, GraphIsomorphic G H ↔ GraphIsomorphic (g G) (g H) := by
    intro G H
    exact (Padding.graphIsomorphic_iff_paddedGraphCode_isomorphic a ha G H).trans
      (GraphCoding.isomorphic_iff_graphIsomorphic _ _)
  refine ⟨parameter N,g,hg,hred,fun G => ?_⟩
  change parameter (Padding.paddedGraphCode a ha G) = parameter N
  have hBF := Padding.fat_padding_on_nat a b ha hpos hba (Padding.tupleColor G)
  have heq := hconstant _ _ hBF
  simpa only [Padding.tupleColor_nil G G₀] using heq

end FSCofinality

end
end

-- Original module: Solutions.InvariantRealParameters
section


set_option autoImplicit false

theorem solution
    (h : FSCofinality.GraphSpace → (ℕ → Bool)) (h_borel : Measurable h)
    (h_invariant : ∀ G H, FSCofinality.GraphIsomorphic G H → h G = h H) :
    ∃ r : ℕ → Bool, ∃ g : FSCofinality.GraphSpace → FSCofinality.GraphSpace,
      Measurable g ∧
      (∀ G H, FSCofinality.GraphIsomorphic G H ↔
        FSCofinality.GraphIsomorphic (g G) (g H)) ∧
      ∀ G, h (g G) = r := by
  exact FSCofinality.graph_invariantRealFiberProperty h h_borel h_invariant

end

#print axioms solution
