-- Prove2me | solution 1 for FSCofinality.original_tree_comparison
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-11-02T15:31:59.445878+00:00
-- url     : https://prove2.me/submissions/9f2620e0-6b8b-4e09-801e-b2c73a37a137

import Definitions.Def_FSCofinalityHierarchy20261102
import Definitions.Def_FSCofinalityStructures20261102
import Definitions.Def_FSCofinalityTrees20261102
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Nth
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Tactic
import Mathlib.Topology.List
import Mathlib.Topology.MetricSpace.PiNat

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

-- Original module: FSCofinalityProof.HierarchyBasics
section


noncomputable section
open Set MeasureTheory TopologicalSpace

namespace FSCofinality

/-- Regularity of a concrete code space; its actual given sigma algebra is used. -/
structure RegularRelation (E : CodedRelation) : Prop where
  equivalence : Equivalence E.rel
  nonempty : Nonempty E.Carrier
  standardBorel : @StandardBorelSpace E.Carrier E.measurableSpace
  measurable_graph : @MeasurableSet (E.Carrier × E.Carrier)
    (E.measurableSpace.prod E.measurableSpace) {p | E.rel p.1 p.2}

def optionSumEquiv (X : Type) : Option X ≃ Unit ⊕ X where
  toFun x := match x with | none => Sum.inl () | some x => Sum.inr x
  invFun x := match x with | Sum.inl _ => none | Sum.inr x => some x
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨⟨⟩⟩ | x <;> rfl

theorem setJump_measurableSpace_eq (E : CodedRelation) :
    (setJump E).measurableSpace =
      MeasurableSpace.comap (optionSumEquiv (ℕ → E.Carrier))
        (inferInstance : MeasurableSpace (Unit ⊕ (ℕ → E.Carrier))) := by
  change MeasurableSpace.comap
    (fun x : Option (ℕ → E.Carrier) => match x with
      | none => (Sum.inl () : Unit ⊕ (ℕ → E.Carrier)) | some u => Sum.inr u)
    (inferInstance : MeasurableSpace (Unit ⊕ (ℕ → E.Carrier))) = _
  apply congrArg (fun f : Option (ℕ → E.Carrier) → Unit ⊕ (ℕ → E.Carrier) =>
    MeasurableSpace.comap f (inferInstance : MeasurableSpace (Unit ⊕ (ℕ → E.Carrier))))
  funext x
  cases x <;> rfl

theorem standardBorel_comap_equiv {X Y : Type} [MeasurableSpace Y]
    [StandardBorelSpace Y] (e : X ≃ Y) :
    @StandardBorelSpace X (MeasurableSpace.comap e inferInstance) := by
  obtain ⟨t,ht,hp⟩ := StandardBorelSpace.polish (α := Y)
  letI : TopologicalSpace Y := t
  letI : BorelSpace Y := ht
  letI : PolishSpace Y := hp
  letI : TopologicalSpace X := TopologicalSpace.induced e inferInstance
  letI : MeasurableSpace X := MeasurableSpace.comap e inferInstance
  letI : PolishSpace X := e.polishSpace_induced
  letI : BorelSpace X := ⟨by
    change MeasurableSpace.comap e _ = @borel X (TopologicalSpace.induced e _)
    rw [borel_comap,← BorelSpace.measurable_eq]⟩
  infer_instance

theorem standardBorel_sum {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] : StandardBorelSpace (X ⊕ Y) := by
  obtain ⟨tX,hbX,hpX⟩ := StandardBorelSpace.polish (α := X)
  obtain ⟨tY,hbY,hpY⟩ := StandardBorelSpace.polish (α := Y)
  letI : TopologicalSpace X := tX
  letI : TopologicalSpace Y := tY
  letI : BorelSpace X := hbX
  letI : BorelSpace Y := hbY
  letI : PolishSpace X := hpX
  letI : PolishSpace Y := hpY
  have hb : (inferInstance : MeasurableSpace (X ⊕ Y)) = borel (X ⊕ Y) := by
    apply le_antisymm
    · intro s hs
      obtain ⟨hsX,hsY⟩ := measurableSet_sum_iff.mp hs
      letI : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
      letI : BorelSpace (X ⊕ Y) := ⟨rfl⟩
      exact MeasurableSet.of_union_range_cover
        Topology.IsOpenEmbedding.inl.measurableEmbedding Topology.IsOpenEmbedding.inr.measurableEmbedding
        (by intro z _; cases z <;> simp) hsX hsY
    · have hL : @Measurable X (X ⊕ Y) inferInstance (borel (X ⊕ Y)) Sum.inl := by
        rw [BorelSpace.measurable_eq (α := X)]
        exact continuous_inl.borel_measurable
      have hR : @Measurable Y (X ⊕ Y) inferInstance (borel (X ⊕ Y)) Sum.inr := by
        rw [BorelSpace.measurable_eq (α := Y)]
        exact continuous_inr.borel_measurable
      have hi : @Measurable (X ⊕ Y) (X ⊕ Y) inferInstance (borel (X ⊕ Y)) id :=
        measurable_fun_sum (f := id) hL hR
      simpa only [MeasurableSpace.comap_id] using hi.comap_le
  letI : BorelSpace (X ⊕ Y) := ⟨hb⟩
  letI : PolishSpace (X ⊕ Y) :=
    { toSecondCountableTopology := inferInstance
      toIsCompletelyMetrizableSpace := inferInstance }
  infer_instance

theorem regular_cantorEquality : RegularRelation cantorEquality := by
  refine ⟨⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩,
    ⟨fun _ => false⟩,?_,?_⟩
  · change StandardBorelSpace (ℕ → Bool)
    infer_instance
  · change MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | p.1 = p.2}
    exact measurableSet_eq_fun measurable_fst measurable_snd

theorem equivalence_countableSetJump {X : Type} {E : X → X → Prop}
    (hE : Equivalence E) : Equivalence (CountableSetJumpRelation E) := by
  constructor
  · intro x
    cases x with
    | none => trivial
    | some u => exact ⟨fun i => ⟨i,hE.refl _⟩,fun i => ⟨i,hE.refl _⟩⟩
  · intro x y h
    cases x <;> cases y
    · trivial
    · exact False.elim h
    · exact False.elim h
    · exact ⟨fun j => by obtain ⟨i,hi⟩ := h.2 j; exact ⟨i,hE.symm hi⟩,
        fun i => by obtain ⟨j,hj⟩ := h.1 i; exact ⟨j,hE.symm hj⟩⟩
  · intro x y z hxy hyz
    cases x <;> cases y <;> cases z
    · trivial
    · exact False.elim hyz
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hyz
    · exact ⟨fun i => by
        obtain ⟨j,hj⟩ := hxy.1 i
        obtain ⟨k,hk⟩ := hyz.1 j
        exact ⟨k,hE.trans hj hk⟩,
        fun k => by
        obtain ⟨j,hj⟩ := hyz.2 k
        obtain ⟨i,hi⟩ := hxy.2 j
        exact ⟨i,hE.trans hi hj⟩⟩

theorem regular_countableProduct (E : ℕ → CodedRelation)
    (hE : ∀ n, RegularRelation (E n)) : RegularRelation (countableProduct E) := by
  letI : ∀ n, StandardBorelSpace (E n).Carrier := fun n => (hE n).standardBorel
  refine ⟨?_,⟨fun n => Classical.choice (hE n).nonempty⟩,?_,?_⟩
  · exact ⟨fun _ n => (hE n).equivalence.refl _,
      fun h n => (hE n).equivalence.symm (h n),
      fun h k n => (hE n).equivalence.trans (h n) (k n)⟩
  · change StandardBorelSpace (∀ n, (E n).Carrier)
    infer_instance
  · change MeasurableSet {p : (∀ n, (E n).Carrier) × (∀ n, (E n).Carrier) |
      ∀ n, (E n).rel (p.1 n) (p.2 n)}
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro n
    exact (hE n).measurable_graph.preimage
      (f := fun p : (∀ n, (E n).Carrier) × (∀ n, (E n).Carrier) => (p.1 n,p.2 n))
      (((measurable_pi_apply n).comp measurable_fst).prodMk
        ((measurable_pi_apply n).comp measurable_snd))

theorem regular_setJump (E : CodedRelation) (hE : RegularRelation E) :
    RegularRelation (setJump E) := by
  letI : StandardBorelSpace E.Carrier := hE.standardBorel
  letI : StandardBorelSpace (Unit ⊕ (ℕ → E.Carrier)) := standardBorel_sum
  letI : MeasurableSpace (Option (ℕ → E.Carrier)) := (setJump E).measurableSpace
  have hc : Measurable (optionSumEquiv (ℕ → E.Carrier)) := by
    change @Measurable (Option (ℕ → E.Carrier)) (Unit ⊕ (ℕ → E.Carrier))
      (setJump E).measurableSpace
      inferInstance (optionSumEquiv (ℕ → E.Carrier))
    rw [setJump_measurableSpace_eq]
    exact comap_measurable _
  refine ⟨equivalence_countableSetJump hE.equivalence,⟨none⟩,?_,?_⟩
  · change @StandardBorelSpace (Option (ℕ → E.Carrier))
      (setJump E).measurableSpace
    rw [setJump_measurableSpace_eq]
    exact standardBorel_comap_equiv (optionSumEquiv (ℕ → E.Carrier))
  change MeasurableSet {p : Option (ℕ → E.Carrier) × Option (ℕ → E.Carrier) |
    CountableSetJumpRelation E.rel p.1 p.2}
  let x₀ : ℕ → E.Carrier := fun _ => Classical.choice hE.nonempty
  let get : Option (ℕ → E.Carrier) → (ℕ → E.Carrier) :=
    fun x => (Sum.elim (fun _ : Unit => x₀) id) (optionSumEquiv _ x)
  have hg : Measurable get := (measurable_const.sumElim measurable_id).comp hc
  have hn : MeasurableSet {x : Option (ℕ → E.Carrier) | x = none} := by
    convert (measurableSet_singleton (Sum.inl () : Unit ⊕ (ℕ → E.Carrier))).preimage hc using 1
    ext x
    cases x <;> simp [optionSumEquiv]
  have hseq : MeasurableSet {p : (ℕ → E.Carrier) × (ℕ → E.Carrier) |
      (∀ i, ∃ j, E.rel (p.1 i) (p.2 j)) ∧ (∀ j, ∃ i, E.rel (p.1 i) (p.2 j))} := by
    have hcoord (i j : ℕ) : MeasurableSet {p : (ℕ → E.Carrier) × (ℕ → E.Carrier) |
        E.rel (p.1 i) (p.2 j)} := hE.measurable_graph.preimage
      (f := fun p : (ℕ → E.Carrier) × (ℕ → E.Carrier) => (p.1 i,p.2 j))
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd))
    simpa only [setOf_and,setOf_forall,setOf_exists] using
      (MeasurableSet.iInter (fun i => MeasurableSet.iUnion (hcoord i))).inter
        (MeasurableSet.iInter (fun j => MeasurableSet.iUnion (fun i => hcoord i j)))
  have hpair := hseq.preimage ((hg.comp measurable_fst).prodMk (hg.comp measurable_snd))
  have hnone := (hn.preimage measurable_fst).inter (hn.preimage measurable_snd)
  have hsome := ((hn.preimage measurable_fst).compl.inter
    (hn.preimage measurable_snd).compl).inter hpair
  convert hnone.union hsome using 1
  ext p
  rcases p with ⟨x,y⟩
  cases x <;> cases y <;> simp [CountableSetJumpRelation,get,optionSumEquiv]

/-- Every tower code, with the fixed sigma algebra in the definitions, is a
nonempty standard Borel space and carries a Borel equivalence relation. -/
theorem regular_fsTower (a : Ordinal.{0}) : RegularRelation (fsTower a) := by
  induction a using Ordinal.limitRecOn with
  | zero => simpa only [fsTower_zero] using regular_cantorEquality
  | add_one a ih => simpa only [fsTower_add_one] using regular_setJump (fsTower a) ih
  | limit a ha ih =>
    rw [fsTower_limit a ha]
    exact regular_countableProduct _ (fun n =>
      ih (fundamentalSequence a ha n) (fundamentalSequence_lt a ha n))

end FSCofinality

end
end

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

-- Original module: FSCofinalityProof.HierarchyEmbeddings
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality

theorem measurable_some_setJump (E : CodedRelation) :
    @Measurable (ℕ → E.Carrier) (setJump E).Carrier inferInstance
      (setJump E).measurableSpace some := by
  rw [setJump_measurableSpace_eq]
  apply measurable_comap_iff.mpr
  exact measurable_inr

theorem reduces_setJump_singleton (E : CodedRelation) : E.Reduces (setJump E) := by
  refine ⟨fun x => some (fun _ => x),?_,?_⟩
  · exact (measurable_some_setJump E).comp (measurable_pi_lambda _ (fun _ => measurable_id))
  · intro x y
    change E.rel x y ↔
      (∀ _ : ℕ, ∃ _ : ℕ, E.rel x y) ∧ (∀ _ : ℕ, ∃ _ : ℕ, E.rel x y)
    exact ⟨fun h => ⟨fun _ => ⟨0,h⟩,fun _ => ⟨0,h⟩⟩,fun h => (h.1 0).choose_spec⟩

theorem reduces_countableProduct_coordinate (E : ℕ → CodedRelation)
    (hE : ∀ n, RegularRelation (E n)) (k : ℕ) :
    (E k).Reduces (countableProduct E) := by
  let f (x : (E k).Carrier) (n : ℕ) : (E n).Carrier :=
    if h : n = k then h.symm ▸ x else Classical.choice (hE n).nonempty
  refine ⟨f,?_,?_⟩
  · apply measurable_pi_lambda
    intro n
    by_cases hn : n = k
    · subst n
      simpa only [f,dif_pos rfl] using (measurable_id : Measurable (id : (E k).Carrier → _))
    · simpa only [f,dif_neg hn] using
        (measurable_const : Measurable (fun _ : (E k).Carrier => Classical.choice (hE n).nonempty))
  · intro x y
    constructor
    · intro h n
      by_cases hn : n = k
      · subst n
        simpa only [f,dif_pos rfl] using h
      · simpa only [f,dif_neg hn] using (hE n).equivalence.refl (Classical.choice (hE n).nonempty)
    · intro h
      simpa only [f,dif_pos rfl] using h k

theorem reduces_setJump_map {E F : CodedRelation} (hEF : E.Reduces F) :
    (setJump E).Reduces (setJump F) := by
  obtain ⟨f,hf,hred⟩ := hEF
  let g : Option (ℕ → E.Carrier) → Option (ℕ → F.Carrier) :=
    Option.map (fun x n => f (x n))
  refine ⟨g,?_,?_⟩
  · change @Measurable (Option (ℕ → E.Carrier)) (Option (ℕ → F.Carrier))
      (setJump E).measurableSpace (setJump F).measurableSpace g
    rw [setJump_measurableSpace_eq,setJump_measurableSpace_eq]
    apply measurable_comap_iff.mpr
    have hm : Measurable (fun u : ℕ → E.Carrier => fun n => f (u n)) :=
      measurable_pi_lambda _ (fun n => hf.comp (measurable_pi_apply n))
    have hs : Measurable (Sum.elim (fun _ : Unit => (Sum.inl () : Unit ⊕ (ℕ → F.Carrier)))
        (fun u : ℕ → E.Carrier => Sum.inr (fun n => f (u n)))) :=
      measurable_const.sumElim (measurable_inr.comp hm)
    have hc := hs.comp (comap_measurable (optionSumEquiv (ℕ → E.Carrier)))
    convert hc using 1
    funext x
    cases x <;> rfl
  · intro x y
    cases x <;> cases y
    · trivial
    · exact Iff.rfl
    · exact Iff.rfl
    · simp only [setJump,CountableSetJumpRelation,g,Option.map_some]
      exact and_congr (forall_congr' (fun i => exists_congr (fun j => hred _ _)))
        (forall_congr' (fun j => exists_congr (fun i => hred _ _)))

/-- The concrete product-limit tower is increasing under actual Borel
reductions. This statement uses its fixed cofinal sequences only below omega one. -/
theorem fsTower_reduces_mono (a b : Ordinal.{0}) (hab : a ≤ b)
    (hb : b < Ordinal.omega 1) : (fsTower a).Reduces (fsTower b) := by
  induction b using Ordinal.limitRecOn generalizing a with
  | zero =>
    have ha : a = 0 := le_antisymm hab zero_le
    subst a
    exact CodedRelation.Reduces.refl _
  | add_one b ih =>
    rcases hab.eq_or_lt with h | h
    · subst a
      exact CodedRelation.Reduces.refl _
    · have hab' : a ≤ b := lt_add_one_iff.mp h
      have hbb : b < Ordinal.omega 1 := lt_trans (lt_add_one b) hb
      have hi := ih a hab' hbb
      rw [fsTower_add_one]
      exact hi.trans (reduces_setJump_singleton _)
  | limit b hlim ih =>
    rcases hab.eq_or_lt with h | h
    · subst a
      exact CodedRelation.Reduces.refl _
    · obtain ⟨n,hn⟩ := fundamentalSequence_cofinal b hlim hb a h
      have hqn := fundamentalSequence_lt b hlim n
      have hi := ih (fundamentalSequence b hlim n) hqn a hn (lt_trans hqn hb)
      rw [fsTower_limit b hlim]
      exact hi.trans (reduces_countableProduct_coordinate _
        (fun _ => regular_fsTower _) n)

end FSCofinality

end
end

-- Original module: FSCofinalityProof.HierarchySums
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality

/-- The actual disjoint union of countably many code spaces, retaining its index. -/
def countableSum (E : ℕ → CodedRelation) : CodedRelation where
  Carrier := Σ n, (E n).Carrier
  measurableSpace := inferInstance
  rel := fun x y => ∃ h : x.1 = y.1, (E y.1).rel (h ▸ x.2) y.2

theorem measurable_sigma_cases {X : ℕ → Type} [∀ n, MeasurableSpace (X n)]
    {Y : Type} [MeasurableSpace Y] (f : (Σ n, X n) → Y)
    (hf : ∀ n, Measurable (fun x => f ⟨n,x⟩)) : Measurable f := by
  intro s hs
  change @MeasurableSet _ (⨅ n, (inferInstance : MeasurableSpace (X n)).map (Sigma.mk n))
    (f ⁻¹' s)
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact hf n hs

def indexAtom (n : ℕ) : ℕ → Bool := fun k => decide (k = n)

theorem indexAtom_injective : Function.Injective indexAtom := by
  intro n m h
  have hk := congrFun h n
  simpa [indexAtom] using hk

/-- A single countable limit stage absorbs any countable disjoint sum of
relations already reducing to countable tower stages. The index is recorded
in coordinate zero; the input uses a separate cofinal coordinate. -/
theorem countableSum_reduces_fsTower (E : ℕ → CodedRelation)
    (b : ℕ → Ordinal.{0}) (hb : ∀ n, b n < Ordinal.omega 1)
    (hE : ∀ n, (E n).Reduces (fsTower (b n))) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ (countableSum E).Reduces (fsTower a) := by
  let s := ⨆ n, b n
  let a := s + Ordinal.omega0
  have hs : s < Ordinal.omega 1 := Ordinal.iSup_lt_omega_one hb
  have ha : a < Ordinal.omega 1 :=
    (Ordinal.isPrincipal_add_omega 1) hs Ordinal.omega0_lt_omega_one
  have halim : IsSuccLimit a := Ordinal.isSuccLimit_add s Ordinal.isSuccLimit_omega0
  have hba (n : ℕ) : b n < a :=
    lt_of_le_of_lt (Ordinal.le_iSup b n) (lt_add_of_pos_right s Ordinal.omega0_pos)
  have hq (n : ℕ) : ∃ k : ℕ, k ≠ 0 ∧ b n ≤ fundamentalSequence a halim k := by
    obtain ⟨k,hk⟩ := fundamentalSequence_cofinal a halim ha (b n) (hba n)
    exact ⟨k+1,by omega,hk.trans
      ((fundamentalSequence_strictMono a halim ha) (Nat.lt_succ_self k)).le⟩
  choose k hk0 hk using hq
  have hmarkTower := fsTower_reduces_mono 0 (fundamentalSequence a halim 0) zero_le
      (lt_trans (fundamentalSequence_lt a halim 0) ha)
  rw [fsTower_zero] at hmarkTower
  obtain ⟨mark,hmark,hmarkred⟩ := hmarkTower
  have hd (n : ℕ) : (E n).Reduces (fsTower (fundamentalSequence a halim (k n))) :=
    (hE n).trans (fsTower_reduces_mono _ _ (hk n)
      (lt_trans (fundamentalSequence_lt a halim (k n)) ha))
  choose data hdata hdatared using hd
  let marker (n : ℕ) := mark (indexAtom n)
  have marker_iff (n m : ℕ) :
      (fsTower (fundamentalSequence a halim 0)).rel (marker n) (marker m) ↔ n = m := by
    apply (hmarkred (indexAtom n) (indexAtom m)).symm.trans
    change indexAtom n = indexAtom m ↔ n = m
    exact ⟨fun h => indexAtom_injective h,fun h => congrArg indexAtom h⟩
  let d (i : ℕ) := Classical.choice (regular_fsTower (fundamentalSequence a halim i)).nonempty
  let f (n : ℕ) (x : (E n).Carrier) (i : ℕ) :
      (fsTower (fundamentalSequence a halim i)).Carrier :=
    if hi : i = 0 then hi.symm ▸ marker n
    else if hi : i = k n then hi.symm ▸ data n x else d i
  have f_zero (n : ℕ) (x : (E n).Carrier) : f n x 0 = marker n := by simp [f]
  have f_data (n : ℕ) (x : (E n).Carrier) : f n x (k n) = data n x := by
    simp [f,hk0 n]
  have hf (n : ℕ) : Measurable (f n) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = 0
    · subst i
      simpa only [f,dif_pos rfl] using
        (measurable_const : Measurable (fun _ : (E n).Carrier => marker n))
    · by_cases hik : i = k n
      · subst i
        simpa only [f,dif_neg hi,dif_pos rfl] using hdata n
      · simpa only [f,dif_neg hi,dif_neg hik] using
          (measurable_const : Measurable (fun _ : (E n).Carrier => d i))
  refine ⟨a,ha,?_⟩
  rw [fsTower_limit a halim]
  refine ⟨fun x => f x.1 x.2,measurable_sigma_cases _ hf,?_⟩
  rintro ⟨n,x⟩ ⟨m,y⟩
  constructor
  · rintro ⟨h,hxy⟩
    dsimp at h
    subst m
    change (E n).rel x y at hxy
    change ∀ i, (fsTower (fundamentalSequence a halim i)).rel (f n x i) (f n y i)
    intro i
    by_cases hi : i = 0
    · subst i
      rw [f_zero,f_zero]
      exact (marker_iff n n).mpr rfl
    · by_cases hik : i = k n
      · subst i
        rw [f_data,f_data]
        exact (hdatared n x y).mp hxy
      · simpa only [f,dif_neg hi,dif_neg hik] using
          (regular_fsTower (fundamentalSequence a halim i)).equivalence.refl (d i)
  · intro h
    change ∀ i, (fsTower (fundamentalSequence a halim i)).rel (f n x i) (f m y i) at h
    have hnm : n = m := (marker_iff n m).mp (by simpa only [f_zero] using h 0)
    subst m
    refine ⟨rfl,?_⟩
    apply (hdatared n x y).mpr
    simpa only [f_data] using h (k n)

theorem measurable_sigma_mk {X : ℕ → Type} [∀ n, MeasurableSpace (X n)] (n : ℕ) :
    Measurable (Sigma.mk n : X n → Σ n, X n) :=
  Measurable.of_le_map (iInf_le _ n)

/-- A sequence of invariants is represented by the set of its index-tagged
entries. Index tags force coordinatewise matching. -/
theorem countableProduct_reduces_setJump_countableSum (E : ℕ → CodedRelation) :
    (countableProduct E).Reduces (setJump (countableSum E)) := by
  refine ⟨fun x => some (fun n => (⟨n,x n⟩ : Σ n, (E n).Carrier)),?_,?_⟩
  · exact (measurable_some_setJump (countableSum E)).comp
      (measurable_pi_lambda _ (fun n => (measurable_sigma_mk n).comp (measurable_pi_apply n)))
  · intro x y
    constructor
    · intro h
      exact ⟨fun n => ⟨n,rfl,h n⟩,fun n => ⟨n,rfl,h n⟩⟩
    · intro h n
      obtain ⟨m,heq,hm⟩ := h.1 n
      dsimp at heq
      subst m
      exact hm

theorem countableProduct_reduces_fsTower (E : ℕ → CodedRelation)
    (b : ℕ → Ordinal.{0}) (hb : ∀ n, b n < Ordinal.omega 1)
    (hE : ∀ n, (E n).Reduces (fsTower (b n))) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ (countableProduct E).Reduces (fsTower a) := by
  obtain ⟨a,ha,hsum⟩ := countableSum_reduces_fsTower E b hb hE
  refine ⟨a+1,?_,?_⟩
  · simpa only [succ_eq_add_one] using (Cardinal.isSuccLimit_omega 1).succ_lt ha
  · rw [fsTower_add_one]
    exact (countableProduct_reduces_setJump_countableSum E).trans (reduces_setJump_map hsum)

end FSCofinality

end
end

-- Original module: FSCofinalityProof.TreeSubtrees
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RootedTrees

def childTree (T : TreeSpace) (n : ℕ) : TreeSpace :=
  ⟨fun s => T (n::s),fun s k h => T.property (n::s) k h⟩

theorem continuous_childTree (n : ℕ) : Continuous (fun T => childTree T n) :=
  (continuous_pi (fun s => continuous_eval (n::s))).subtype_mk _

def childNode (T : TreeSpace) (n : ℕ) (s : Nodes (childTree T n)) : Nodes T :=
  ⟨n::s.val,s.property⟩

theorem childNode_child {T : TreeSpace} (n : ℕ) (s t : Nodes (childTree T n)) :
    Child s t ↔ Child (childNode T n s) (childNode T n t) := by
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,congrArg (List.cons n) hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,List.cons.inj hk |>.2⟩

theorem BoundedTree.mono {T : TreeSpace} {a b : Ordinal.{0}}
    (h : BoundedTree T a) (hab : a ≤ b) : BoundedTree T b := by
  obtain ⟨rho,hrho,hdec⟩ := h
  exact ⟨rho,fun s => (hrho s).trans_le hab,hdec⟩

theorem rank_le_prefix {T : TreeSpace} (rho : Nodes T → Ordinal.{0})
    (hdec : ∀ s t, Child s t → rho s < rho t) (s t : Node)
    (hst : T (s++t) = true) :
    rho ⟨s++t,hst⟩ ≤ rho ⟨s,mem_of_append T s t hst⟩ := by
  induction t using List.reverseRecOn with
  | nil => simp only [List.append_nil]; exact le_refl _
  | append_singleton t n ih =>
    have hp : T (s++t) = true := mem_parent T (s++t) n (by simpa using hst)
    have hd : rho ⟨s++(t++[n]),hst⟩ < rho ⟨s++t,hp⟩ :=
      hdec _ _ ⟨n,by simp only [List.append_assoc]⟩
    exact hd.le.trans (ih hp)

theorem BoundedTree.child_of_succ {T : TreeSpace} {a : Ordinal.{0}}
    (h : BoundedTree T (a+1)) (n : ℕ) : BoundedTree (childTree T n) a := by
  obtain ⟨rho,hrho,hdec⟩ := h
  refine ⟨fun s => rho (childNode T n s),?_,?_⟩
  · intro s
    have hn : T [n] = true := mem_of_append T [n] s.val s.property
    have hroot : T [] = true := mem_parent T [] n hn
    have hd : rho ⟨[n],hn⟩ < rho ⟨[],hroot⟩ := hdec _ _ ⟨n,rfl⟩
    have hle := rank_le_prefix rho hdec [n] s.val s.property
    exact hle.trans_lt (hd.trans_le (Order.lt_succ_iff.mp (hrho ⟨[],hroot⟩)))
  · intro s t hst
    exact hdec _ _ ((childNode_child n s t).mp hst)

theorem BoundedTree.exists_smaller_of_limit {T : TreeSpace} {a : Ordinal.{0}}
    (h : BoundedTree T a) (ha : IsSuccLimit a) :
    ∃ b < a, BoundedTree T b := by
  by_cases hroot : T [] = true
  · obtain ⟨rho,hrho,hdec⟩ := h
    refine ⟨rho ⟨[],hroot⟩+1,ha.succ_lt (hrho _),rho,?_,hdec⟩
    intro s
    have hle := rank_le_prefix rho hdec [] s.val s.property
    exact Order.lt_succ_iff.mpr hle
  · have he : T = emptyTree := by
      apply Subtype.ext
      funext s
      have hn : T s ≠ true := fun hs => hroot (mem_of_append T [] s hs)
      exact Bool.eq_false_iff.mpr hn
    exact ⟨0,ha.pos,he ▸ bounded_emptyTree 0⟩

end FSCofinality.RootedTrees

end
end

-- Original module: FSCofinalityProof.Multiset
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory

namespace FSCofinality

def CountableMultisetRelation {X : Type} (E : X → X → Prop) (x y : ℕ → X) : Prop :=
  ∃ σ : ℕ ≃ ℕ, ∀ i, E (x i) (y (σ i))

def multisetJump (E : CodedRelation) : CodedRelation where
  Carrier := ℕ → E.Carrier
  measurableSpace := inferInstance
  rel := CountableMultisetRelation E.rel

def naturalTagged (E : CodedRelation) : CodedRelation where
  Carrier := E.Carrier × ℕ
  measurableSpace := inferInstance
  rel := fun x y => E.rel x.1 y.1 ∧ x.2 = y.2

/-- The zero-based number of earlier occurrences in the same equivalence class. -/
def occurrenceCount {X : Type} (E : X → X → Prop) (x : ℕ → X) (i : ℕ) : ℕ :=
  Nat.count (fun j => E (x j) (x i)) i

def occurrenceCode {X : Type} (E : X → X → Prop) (x : ℕ → X) : ℕ → X × ℕ :=
  fun i => (x i,occurrenceCount E x i)

theorem sameClass_predicate {X : Type} {E : X → X → Prop} (hE : Equivalence E)
    {a b : X} (hab : E a b) (x : ℕ → X) :
    (fun j => E (x j) a) = (fun j => E (x j) b) := by
  funext j
  exact propext ⟨fun h => hE.trans h hab,fun h => hE.trans h (hE.symm hab)⟩

theorem occurrenceCount_injective_sameClass {X : Type} {E : X → X → Prop}
    (hE : Equivalence E) (x : ℕ → X) {i j : ℕ} (hij : E (x i) (x j))
    (hc : occurrenceCount E x i = occurrenceCount E x j) : i = j := by
  unfold occurrenceCount at hc
  simp only [sameClass_predicate hE hij x] at hc
  exact Nat.count_injective hij (hE.refl _) hc

theorem occurrenceCount_measurable (E : CodedRelation)
    (hE : @MeasurableSet (E.Carrier × E.Carrier)
      (E.measurableSpace.prod E.measurableSpace) {p | E.rel p.1 p.2}) (i : ℕ) :
    Measurable (fun x : ℕ → E.Carrier => occurrenceCount E.rel x i) := by
  have hcount (n : ℕ) : Measurable (fun x : ℕ → E.Carrier =>
      Nat.count (fun j => E.rel (x j) (x i)) n) := by
    induction n with
    | zero => simpa only [Nat.count_zero] using (measurable_const :
        Measurable (fun _ : ℕ → E.Carrier => (0 : ℕ)))
    | succ n ih =>
      simp only [Nat.count_succ]
      exact ih.add (Measurable.ite
        (hE.preimage (f := fun x : ℕ → E.Carrier => (x n,x i))
          ((measurable_pi_apply n).prodMk (measurable_pi_apply i)))
        measurable_const measurable_const)
  exact hcount i

theorem occurrenceCode_measurable (E : CodedRelation)
    (hE : @MeasurableSet (E.Carrier × E.Carrier)
      (E.measurableSpace.prod E.measurableSpace) {p | E.rel p.1 p.2}) :
    Measurable (occurrenceCode E.rel) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i).prodMk (occurrenceCount_measurable E hE i)

/-- A permutation preserving classes supplies an occurrence of every tag
present in the input, regardless of its enumeration order. -/
theorem tagged_match_of_permutation {X : Type} {E : X → X → Prop}
    (hE : Equivalence E) {x y : ℕ → X} (σ : ℕ ≃ ℕ)
    (hσ : ∀ i, E (x i) (y (σ i))) (i : ℕ) :
    ∃ j, E (x i) (y j) ∧ occurrenceCount E x i = occurrenceCount E y j := by
  let p : ℕ → Prop := fun j => E (y j) (x i)
  let k := occurrenceCount E x i
  have hk : ∀ hf : (setOf p).Finite, k < hf.toFinset.card := by
    intro hf
    let s := (Finset.range (i+1)).filter (fun j => E (x j) (x i))
    have hsub : s.image σ ⊆ hf.toFinset := by
      intro j hj
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hj
      exact hf.mem_toFinset.mpr (hE.trans (hE.symm (hσ l)) (Finset.mem_filter.mp hl).2)
    have hcard : (s.image σ).card = s.card := Finset.card_image_iff.mpr σ.injective.injOn
    have hlt : k < s.card := by
      change Nat.count (fun j => E (x j) (x i)) i < s.card
      change Nat.count (fun j => E (x j) (x i)) i <
        ((Finset.range (i+1)).filter (fun j => E (x j) (x i))).card
      rw [← Nat.count_eq_card_filter_range]
      exact Nat.count_lt_count_succ_iff.mpr (hE.refl _)
    exact hlt.trans_le (hcard ▸ Finset.card_le_card hsub)
  let j := Nat.nth p k
  have hpj : p j := Nat.nth_mem k hk
  refine ⟨j,hE.symm hpj,?_⟩
  unfold occurrenceCount
  simp only [sameClass_predicate hE hpj y]
  exact (Nat.count_nth hk).symm

theorem occurrenceCode_reduction {X : Type} {E : X → X → Prop}
    (hE : Equivalence E) (x y : ℕ → X) :
    CountableMultisetRelation E x y ↔
      CountableSetJumpRelation (fun a b : X × ℕ => E a.1 b.1 ∧ a.2 = b.2)
        (some (occurrenceCode E x)) (some (occurrenceCode E y)) := by
  constructor
  · rintro ⟨σ,hσ⟩
    refine ⟨tagged_match_of_permutation hE σ hσ,?_⟩
    intro j
    obtain ⟨i,hi,hc⟩ := tagged_match_of_permutation hE σ.symm
      (fun j => by simpa using hE.symm (hσ (σ.symm j))) j
    exact ⟨i,hE.symm hi,hc.symm⟩
  · rintro ⟨hxy,hyx⟩
    change (∀ i, ∃ j, E (x i) (y j) ∧ occurrenceCount E x i = occurrenceCount E y j) at hxy
    change (∀ j, ∃ i, E (x i) (y j) ∧ occurrenceCount E x i = occurrenceCount E y j) at hyx
    choose f hf using hxy
    have hfinj : Function.Injective f := by
      intro i j hij
      apply occurrenceCount_injective_sameClass hE x
        (hE.trans (hf i).1 (hE.symm (by rw [hij]; exact (hf j).1)))
      exact (hf i).2.trans (by rw [hij]; exact (hf j).2.symm)
    have hfsurj : Function.Surjective f := by
      intro j
      obtain ⟨i,hi,hc⟩ := hyx j
      refine ⟨i,?_⟩
      exact occurrenceCount_injective_sameClass hE y
        (hE.trans (hE.symm (hf i).1) hi) ((hf i).2.symm.trans hc)
    exact ⟨Equiv.ofBijective f ⟨hfinj,hfsurj⟩,fun i => (hf i).1⟩

/-- Occurrence tags give the source manuscript's multiset-to-set-jump
reduction on actual sequence code spaces. -/
theorem multisetJump_reduces_setJump_naturalTagged (E : CodedRelation)
    (hE : Equivalence E.rel)
    (hgraph : @MeasurableSet (E.Carrier × E.Carrier)
      (E.measurableSpace.prod E.measurableSpace) {p | E.rel p.1 p.2}) :
    (multisetJump E).Reduces (setJump (naturalTagged E)) := by
  refine ⟨fun x => some (occurrenceCode E.rel x),?_,?_⟩
  · change @Measurable (ℕ → E.Carrier) (Option (ℕ → E.Carrier × ℕ))
      inferInstance (setJump (naturalTagged E)).measurableSpace
      (fun x => some (occurrenceCode E.rel x))
    rw [setJump_measurableSpace_eq]
    apply measurable_comap_iff.mpr
    exact measurable_inr.comp (occurrenceCode_measurable E hgraph)
  · exact occurrenceCode_reduction hE

end FSCofinality

end
end

-- Original module: FSCofinalityProof.MultisetClosure
section


noncomputable section
open Set MeasureTheory Ordinal Order

namespace FSCofinality

theorem naturalTagged_reduces_countableSum (E : CodedRelation) :
    (naturalTagged E).Reduces (countableSum (fun _ => E)) := by
  refine ⟨fun x => ⟨x.2,x.1⟩,?_,?_⟩
  · exact measurable_from_prod_countable_left (fun n => measurable_sigma_mk n)
  · rintro ⟨x,n⟩ ⟨y,m⟩
    constructor
    · rintro ⟨hxy,h⟩
      change n = m at h
      subst m
      exact ⟨rfl,hxy⟩
    · rintro ⟨h,hxy⟩
      change n = m at h
      subst m
      exact ⟨hxy,rfl⟩

theorem equivalence_of_reduces {E F : CodedRelation} (hEF : E.Reduces F)
    (hF : Equivalence F.rel) : Equivalence E.rel := by
  obtain ⟨f,hf,hred⟩ := hEF
  exact ⟨fun x => (hred x x).mpr (hF.refl _),
    fun h => (hred _ _).mpr (hF.symm ((hred _ _).mp h)),
    fun h k => (hred _ _).mpr (hF.trans ((hred _ _).mp h) ((hred _ _).mp k))⟩

theorem measurable_graph_of_reduces {E F : CodedRelation} (hEF : E.Reduces F)
    (hF : @MeasurableSet (F.Carrier × F.Carrier)
      (F.measurableSpace.prod F.measurableSpace) {p | F.rel p.1 p.2}) :
    @MeasurableSet (E.Carrier × E.Carrier)
      (E.measurableSpace.prod E.measurableSpace) {p | E.rel p.1 p.2} := by
  obtain ⟨f,hf,hred⟩ := hEF
  have hm : Measurable (fun p : E.Carrier × E.Carrier => (f p.1,f p.2)) :=
    (hf.comp measurable_fst).prodMk (hf.comp measurable_snd)
  have hpre := hF.preimage hm
  convert hpre using 1
  ext p
  exact hred p.1 p.2

/-- Cofinality is preserved by the multiplicity-sensitive countable jump.
Borelness and equivalence of the input follow from its reduction to a tower stage. -/
theorem multisetJump_reduces_fsTower (E : CodedRelation) (b : Ordinal.{0})
    (hb : b < Ordinal.omega 1) (hE : E.Reduces (fsTower b)) :
    ∃ a : Ordinal.{0}, a < Ordinal.omega 1 ∧ (multisetJump E).Reduces (fsTower a) := by
  obtain ⟨a,ha,hsum⟩ := countableSum_reduces_fsTower (fun _ => E) (fun _ => b)
    (fun _ => hb) (fun _ => hE)
  have htag := (naturalTagged_reduces_countableSum E).trans hsum
  have hmult := multisetJump_reduces_setJump_naturalTagged E
    (equivalence_of_reduces hE (regular_fsTower b).equivalence)
    (measurable_graph_of_reduces hE (regular_fsTower b).measurable_graph)
  refine ⟨a+1,?_,?_⟩
  · simpa only [succ_eq_add_one] using (Cardinal.isSuccLimit_omega 1).succ_lt ha
  · rw [fsTower_add_one]
    exact hmult.trans (reduces_setJump_map htag)

end FSCofinality

end
end

-- Original module: FSCofinalityProof.TreeIsomorphisms
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.RootedTrees

theorem isomorphic_refl (T : TreeSpace) : Isomorphic T T := ⟨Equiv.refl _,fun _ _ => Iff.rfl⟩

theorem isomorphic_symm {T U : TreeSpace} (h : Isomorphic T U) : Isomorphic U T := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,fun s t => ?_⟩
  simpa only [Equiv.apply_symm_apply] using (he (e.symm s) (e.symm t)).symm

theorem isomorphic_trans {T U V : TreeSpace} (h : Isomorphic T U) (k : Isomorphic U V) :
    Isomorphic T V := by
  obtain ⟨e,he⟩ := h
  obtain ⟨f,hf⟩ := k
  exact ⟨e.trans f,fun s t => (he s t).trans (hf (e s) (e t))⟩

theorem isomorphic_equivalence : Equivalence Isomorphic :=
  ⟨isomorphic_refl,fun h => isomorphic_symm h,fun h k => isomorphic_trans h k⟩

theorem noRoot_iff_eq_empty (T : TreeSpace) : T [] ≠ true ↔ T = emptyTree := by
  constructor
  · intro h
    apply Subtype.ext
    funext s
    apply Bool.eq_false_iff.mpr
    intro hs
    exact h (mem_of_append T [] s hs)
  · rintro rfl
    decide

theorem isomorphic_root_iff {T U : TreeSpace} (h : Isomorphic T U) :
    T [] = true ↔ U [] = true := by
  obtain ⟨e,he⟩ := h
  constructor
  · intro ht
    exact mem_of_append U [] (e ⟨[],ht⟩).val (e ⟨[],ht⟩).property
  · intro hu
    exact mem_of_append T [] (e.symm ⟨[],hu⟩).val (e.symm ⟨[],hu⟩).property

theorem map_prefix {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (s : Nodes T)
    (v : Node) (hv : T (s.val++v) = true) :
    ∃ w, (e ⟨s.val++v,hv⟩).val = (e s).val ++ w := by
  induction v using List.reverseRecOn with
  | nil => exact ⟨[],by simp only [List.append_nil]; rfl⟩
  | append_singleton v n ih =>
    have hp : T (s.val++v) = true := mem_parent T (s.val++v) n (by simpa using hv)
    obtain ⟨w,hw⟩ := ih hp
    obtain ⟨k,hk⟩ := (he ⟨s.val++(v++[n]),hv⟩ ⟨s.val++v,hp⟩).mp
      ⟨n,by simp only [List.append_assoc]⟩
    exact ⟨w++[k],by rw [hk,hw,List.append_assoc]⟩

theorem root_image {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t))
    (ht : T [] = true) (hu : U [] = true) : (e ⟨[],ht⟩).val = [] := by
  let s := e.symm ⟨[],hu⟩
  obtain ⟨w,hw⟩ := map_prefix e he ⟨[],ht⟩ s.val s.property
  have hs : (e ⟨s.val,s.property⟩).val = [] := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨[],hu⟩)
  change (e ⟨s.val,s.property⟩).val = (e ⟨[],ht⟩).val ++ w at hw
  rw [hs] at hw
  exact (List.append_eq_nil_iff.mp hw.symm).1

abbrev ChildLabels (T : TreeSpace) := {n : ℕ // T [n] = true}

theorem child_image {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T) :
    ∃ m : ChildLabels U, (e ⟨[n.val],n.property⟩).val = [m.val] := by
  have ht : T [] = true := mem_parent T [] n.val n.property
  have hu : U [] = true := (isomorphic_root_iff ⟨e,he⟩).mp ht
  obtain ⟨m,hm⟩ := (he ⟨[n.val],n.property⟩ ⟨[],ht⟩).mp ⟨n.val,rfl⟩
  rw [root_image e he ht hu] at hm
  exact ⟨⟨m,by simpa only [hm,List.nil_append] using (e ⟨[n.val],n.property⟩).property⟩,
    by simpa only [List.nil_append] using hm⟩

def childLabelMap {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) : ChildLabels T → ChildLabels U :=
  fun n => (child_image e he n).choose

theorem childLabelMap_spec {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T) :
    (e ⟨[n.val],n.property⟩).val = [(childLabelMap e he n).val] :=
  (child_image e he n).choose_spec

theorem childLabelMap_leftInverse {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) :
    Function.LeftInverse
      (childLabelMap e.symm (fun s t => by simpa using (he (e.symm s) (e.symm t)).symm))
      (childLabelMap e he) := by
  intro n
  apply Subtype.ext
  have h := childLabelMap_spec e.symm
    (fun s t => by simpa using (he (e.symm s) (e.symm t)).symm) (childLabelMap e he n)
  have hn : e ⟨[n.val],n.property⟩ =
      ⟨[(childLabelMap e he n).val],(childLabelMap e he n).property⟩ :=
    Subtype.ext (childLabelMap_spec e he n)
  rw [← hn,e.symm_apply_apply] at h
  exact List.singleton_injective h.symm

def childLabelEquiv {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) : ChildLabels T ≃ ChildLabels U where
  toFun := childLabelMap e he
  invFun := childLabelMap e.symm (fun s t => by simpa using (he (e.symm s) (e.symm t)).symm)
  left_inv := childLabelMap_leftInverse e he
  right_inv := by
    intro n
    exact childLabelMap_leftInverse e.symm
      (fun s t => by simpa using (he (e.symm s) (e.symm t)).symm) n

theorem map_prefix_iff {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (s t : Nodes T) :
    (∃ v, t.val = s.val ++ v) ↔ ∃ v, (e t).val = (e s).val ++ v := by
  constructor
  · rintro ⟨v,hv⟩
    have hmem : T (s.val++v) = true := hv ▸ t.property
    have ht : (⟨s.val++v,hmem⟩ : Nodes T) = t := Subtype.ext hv.symm
    simpa only [ht] using map_prefix e he s v hmem
  · rintro ⟨v,hv⟩
    have hmem : U ((e s).val++v) = true := hv ▸ (e t).property
    have ht : (⟨(e s).val++v,hmem⟩ : Nodes U) = e t := Subtype.ext hv.symm
    have h := map_prefix e.symm
      (fun s t => by simpa using (he (e.symm s) (e.symm t)).symm) (e s) v hmem
    simpa only [ht,Equiv.symm_apply_apply] using h

abbrev Descendants (T : TreeSpace) (n : ℕ) :=
  {s : Nodes T // ∃ v, s.val = n::v}

theorem descendant_eq_cons_tail {T : TreeSpace} {n : ℕ} (s : Descendants T n) :
    s.val.val = n::s.val.val.tail := by
  obtain ⟨v,hv⟩ := s.property
  rw [hv]
  rfl

def childDescendantEquiv (T : TreeSpace) (n : ℕ) :
    Nodes (childTree T n) ≃ Descendants T n where
  toFun s := ⟨childNode T n s,s.val,rfl⟩
  invFun s := ⟨s.val.val.tail,by
    change T (n::s.val.val.tail) = true
    rw [← descendant_eq_cons_tail s]
    exact s.val.property⟩
  left_inv s := rfl
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    exact (descendant_eq_cons_tail s).symm

theorem map_descendants_iff {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T) (s : Nodes T) :
    (∃ v, s.val = n.val::v) ↔
      ∃ v, (e s).val = (childLabelEquiv e he n).val::v := by
  have h := map_prefix_iff e he ⟨[n.val],n.property⟩ s
  rw [childLabelMap_spec e he n] at h
  simpa only [List.singleton_append] using h

def childSubtreeEquiv {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T) :
    Nodes (childTree T n.val) ≃ Nodes (childTree U (childLabelEquiv e he n).val) :=
  ((childDescendantEquiv T n.val).trans
    (e.subtypeEquiv (map_descendants_iff e he n))).trans
      (childDescendantEquiv U (childLabelEquiv e he n).val).symm

theorem childSubtreeEquiv_lift {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T)
    (s : Nodes (childTree T n.val)) :
    childNode U (childLabelEquiv e he n).val (childSubtreeEquiv e he n s) =
      e (childNode T n.val s) := by
  apply Subtype.ext
  exact (descendant_eq_cons_tail
    ((e.subtypeEquiv (map_descendants_iff e he n)) (childDescendantEquiv T n.val s))).symm

theorem child_isomorphic {T U : TreeSpace} (e : Nodes T ≃ Nodes U)
    (he : ∀ s t, Child s t ↔ Child (e s) (e t)) (n : ChildLabels T) :
    Isomorphic (childTree T n.val) (childTree U (childLabelEquiv e he n).val) := by
  refine ⟨childSubtreeEquiv e he n,fun s t => ?_⟩
  rw [childNode_child n.val s t,he,
    childNode_child (childLabelEquiv e he n).val,
    childSubtreeEquiv_lift,childSubtreeEquiv_lift]

end FSCofinality.RootedTrees

end
end

-- Original module: FSCofinalityProof.TreeAssembly
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.RootedTrees

abbrev TreeParts (T : TreeSpace) := Unit ⊕ Σ n : ChildLabels T, Nodes (childTree T n.val)

def joinParts (T : TreeSpace) (hroot : T [] = true) : TreeParts T → Nodes T
  | Sum.inl _ => ⟨[],hroot⟩
  | Sum.inr ⟨n,s⟩ => childNode T n.val s

theorem joinParts_injective (T : TreeSpace) (hroot : T [] = true) :
    Function.Injective (joinParts T hroot) := by
  rintro (u | ⟨n,s⟩) (v | ⟨m,t⟩) h
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · have hv := congrArg Subtype.val h
    simp [joinParts,childNode] at hv
  · have hv := congrArg Subtype.val h
    simp [joinParts,childNode] at hv
  · have hv := List.cons.inj (congrArg Subtype.val h)
    have hnm : n = m := Subtype.ext hv.1
    subst m
    have hst : s = t := Subtype.ext hv.2
    subst t
    rfl

theorem joinParts_surjective (T : TreeSpace) (hroot : T [] = true) :
    Function.Surjective (joinParts T hroot) := by
  rintro ⟨s,hs⟩
  cases s with
  | nil => exact ⟨Sum.inl (),rfl⟩
  | cons n s =>
    have hn : T [n] = true := mem_of_append T [n] s hs
    exact ⟨Sum.inr ⟨⟨n,hn⟩,⟨s,hs⟩⟩,rfl⟩

def partsEquiv (T : TreeSpace) (hroot : T [] = true) : TreeParts T ≃ Nodes T :=
  Equiv.ofBijective (joinParts T hroot) ⟨joinParts_injective T hroot,joinParts_surjective T hroot⟩

def PartsChild (T : TreeSpace) : TreeParts T → TreeParts T → Prop
  | Sum.inl _, _ => False
  | Sum.inr ⟨_,s⟩, Sum.inl _ => s.val = []
  | Sum.inr ⟨n,s⟩, Sum.inr ⟨m,t⟩ => ∃ h : n=m, Child (h ▸ s) t

theorem joinParts_child (T : TreeSpace) (hroot : T [] = true) (s t : TreeParts T) :
    PartsChild T s t ↔ Child (joinParts T hroot s) (joinParts T hroot t) := by
  cases s with
  | inl u =>
    cases t with
    | inl v => simp [PartsChild,Child,joinParts]
    | inr v =>
      rcases v with ⟨m,t⟩
      simp [PartsChild,Child,joinParts,childNode]
  | inr u =>
    rcases u with ⟨n,s⟩
    cases t with
    | inl v =>
      simp only [PartsChild,Child,joinParts,childNode,List.nil_append]
      constructor
      · intro hs
        exact ⟨n.val,by simp [hs]⟩
      · rintro ⟨k,hk⟩
        exact (List.cons.inj hk).2
    | inr v =>
      rcases v with ⟨m,t⟩
      constructor
      · rintro ⟨h,hchild⟩
        subst m
        exact (childNode_child n.val s t).mp hchild
      · rintro ⟨k,hk⟩
        have hnm : n = m := Subtype.ext (List.cons.inj hk).1
        subst m
        exact ⟨rfl,k,(List.cons.inj hk).2⟩

def assembleParts {T U : TreeSpace} (e : ChildLabels T ≃ ChildLabels U)
    (f : ∀ n, Nodes (childTree T n.val) ≃ Nodes (childTree U (e n).val)) :
    TreeParts T ≃ TreeParts U :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sigmaCongr e f)

theorem assembleParts_child {T U : TreeSpace} (e : ChildLabels T ≃ ChildLabels U)
    (f : ∀ n, Nodes (childTree T n.val) ≃ Nodes (childTree U (e n).val))
    (hf : ∀ n s t, Child s t ↔ Child (f n s) (f n t))
    (s t : TreeParts T) :
    PartsChild T s t ↔ PartsChild U (assembleParts e f s) (assembleParts e f t) := by
  cases s with
  | inl u => cases t <;> exact Iff.rfl
  | inr u =>
    rcases u with ⟨n,s⟩
    cases t with
    | inl v =>
      change s.val = [] ↔ (f n s).val = []
      have hs := isomorphic_root_iff (show Isomorphic (childTree T n.val)
        (childTree U (e n).val) from ⟨f n,hf n⟩)
      constructor
      · intro hsroot
        have htroot : childTree T n.val [] = true := n.property
        have huroot := hs.mp htroot
        have hsn : s = ⟨[],htroot⟩ := Subtype.ext hsroot
        rw [hsn]
        exact root_image (f n) (hf n) htroot huroot
      · intro hsroot
        have huroot : childTree U (e n).val [] = true := (e n).property
        have htroot := hs.mpr huroot
        have hsn : f n s = ⟨[],huroot⟩ := Subtype.ext hsroot
        have h := root_image (f n).symm
          (fun s t => by simpa using (hf n ((f n).symm s) ((f n).symm t)).symm)
          huroot htroot
        rw [← hsn,Equiv.symm_apply_apply] at h
        exact h
    | inr v =>
      rcases v with ⟨m,t⟩
      change (∃ h : n=m, Child (h ▸ s) t) ↔
        ∃ h : e n = e m, Child (h ▸ f n s) (f m t)
      constructor
      · rintro ⟨h,hst⟩
        subst m
        exact ⟨rfl,(hf n s t).mp hst⟩
      · rintro ⟨h,hst⟩
        have hnm := e.injective h
        subst m
        exact ⟨rfl,(hf n s t).mpr hst⟩

theorem isomorphic_of_child_equiv {T U : TreeSpace}
    (ht : T [] = true) (hu : U [] = true) (e : ChildLabels T ≃ ChildLabels U)
    (hchildren : ∀ n, Isomorphic (childTree T n.val) (childTree U (e n).val)) :
    Isomorphic T U := by
  choose f hf using hchildren
  let q := ((partsEquiv T ht).symm.trans (assembleParts e f)).trans (partsEquiv U hu)
  refine ⟨q,fun s t => ?_⟩
  have hs : joinParts T ht ((partsEquiv T ht).symm s) = s := (partsEquiv T ht).apply_symm_apply s
  have ht' : joinParts T ht ((partsEquiv T ht).symm t) = t := (partsEquiv T ht).apply_symm_apply t
  have h1 := joinParts_child T ht ((partsEquiv T ht).symm s) ((partsEquiv T ht).symm t)
  rw [hs,ht'] at h1
  exact h1.symm.trans ((assembleParts_child e f hf _ _).trans (joinParts_child U hu _ _))

end FSCofinality.RootedTrees

end
end

-- Original module: FSCofinalityProof.TreePaddedChildren
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.RootedTrees

/-- Infinitely many empty padding entries make absent child labels irrelevant. -/
def paddedChildren (T : TreeSpace) (i : ℕ) : TreeSpace :=
  if i % 2 = 0 then childTree T (i/2) else emptyTree

@[simp] theorem paddedChildren_even (T : TreeSpace) (n : ℕ) :
    paddedChildren T (2*n) = childTree T n := by simp [paddedChildren]

@[simp] theorem paddedChildren_odd (T : TreeSpace) (n : ℕ) :
    paddedChildren T (2*n+1) = emptyTree := by simp [paddedChildren,Nat.add_mod]

theorem continuous_paddedChildren : Continuous paddedChildren := by
  apply continuous_pi
  intro i
  by_cases hi : i%2=0
  · simpa only [paddedChildren,if_pos hi] using continuous_childTree (i/2)
  · simpa only [paddedChildren,if_neg hi] using
      (continuous_const : Continuous (fun _ : TreeSpace => emptyTree))

theorem measurable_paddedChildren : Measurable paddedChildren := continuous_paddedChildren.measurable

theorem BoundedTree.paddedChildren_of_succ {T : TreeSpace} {a : Ordinal.{0}}
    (h : BoundedTree T (a+1)) (i : ℕ) : BoundedTree (paddedChildren T i) a := by
  by_cases hi : i%2=0
  · simpa only [paddedChildren,if_pos hi] using h.child_of_succ (i/2)
  · simpa only [paddedChildren,if_neg hi] using bounded_emptyTree a

abbrev PresentChildren (T : TreeSpace) := {i : ℕ // paddedChildren T i [] = true}
abbrev AbsentChildren (T : TreeSpace) := {i : ℕ // ¬ paddedChildren T i [] = true}

theorem present_even {T : TreeSpace} (i : PresentChildren T) : i.val % 2 = 0 := by
  by_contra h
  have hp := i.property
  simp only [paddedChildren,if_neg h,emptyTree] at hp
  contradiction

def labelPresentEquiv (T : TreeSpace) : ChildLabels T ≃ PresentChildren T where
  toFun n := ⟨2*n.val,by simpa using n.property⟩
  invFun i := ⟨i.val/2,by
    have h := i.property
    simpa only [paddedChildren,if_pos (present_even i)] using h⟩
  left_inv n := by apply Subtype.ext; simp
  right_inv i := by
    apply Subtype.ext
    change 2*(i.val/2) = i.val
    have h := present_even i
    omega

@[simp] theorem labelPresentEquiv_val (T : TreeSpace) (n : ChildLabels T) :
    (labelPresentEquiv T n).val = 2*n.val := rfl

theorem labelPresentEquiv_tree (T : TreeSpace) (n : ChildLabels T) :
    paddedChildren T (labelPresentEquiv T n).val = childTree T n.val := by simp

instance absentChildren_infinite (T : TreeSpace) : Infinite (AbsentChildren T) := by
  let f : ℕ → AbsentChildren T := fun n => ⟨2*n+1,by simp [emptyTree]⟩
  apply Infinite.of_injective f
  intro n m h
  have hv := congrArg Subtype.val h
  dsimp only [f] at hv
  omega

def absentEquiv (T U : TreeSpace) : AbsentChildren T ≃ AbsentChildren U :=
  (Classical.choice (inferInstance : Nonempty (ℕ ≃ AbsentChildren T))).symm.trans
    (Classical.choice (inferInstance : Nonempty (ℕ ≃ AbsentChildren U)))

end FSCofinality.RootedTrees

end
end

-- Original module: FSCofinalityProof.TreeChildClassification
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.RootedTrees

theorem multiset_paddedChildren_of_isomorphic {T U : TreeSpace} (h : Isomorphic T U) :
    CountableMultisetRelation Isomorphic (paddedChildren T) (paddedChildren U) := by
  obtain ⟨e,he⟩ := h
  let ep : PresentChildren T ≃ PresentChildren U :=
    (((labelPresentEquiv T).symm).trans (childLabelEquiv e he)).trans (labelPresentEquiv U)
  let ec := absentEquiv T U
  let sigma : ℕ ≃ ℕ := Equiv.subtypeCongr ep ec
  have hleft (i : PresentChildren T) : sigma i.val = (ep i).val := by
    simp only [sigma,Equiv.subtypeCongr,Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_pos,Equiv.sumCongr_apply,Sum.map_inl,Equiv.sumCompl_apply_inl]
  have hright (i : AbsentChildren T) : sigma i.val = (ec i).val := by
    simp only [sigma,Equiv.subtypeCongr,Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_neg,Equiv.sumCongr_apply,Sum.map_inr,Equiv.sumCompl_apply_inr]
  refine ⟨sigma,fun i => ?_⟩
  by_cases hi : paddedChildren T i [] = true
  · let j : PresentChildren T := ⟨i,hi⟩
    let n := (labelPresentEquiv T).symm j
    have hj : labelPresentEquiv T n = j := (labelPresentEquiv T).apply_symm_apply j
    have hx : paddedChildren T i = childTree T n.val := by
      rw [← show (labelPresentEquiv T n).val = i from congrArg Subtype.val hj]
      exact labelPresentEquiv_tree T n
    have hy : paddedChildren U (sigma i) = childTree U (childLabelEquiv e he n).val := by
      rw [show sigma i = (ep j).val from hleft j]
      change paddedChildren U (labelPresentEquiv U (childLabelEquiv e he n)).val = _
      exact labelPresentEquiv_tree U _
    rw [hx,hy]
    exact child_isomorphic e he n
  · have hj : ¬ paddedChildren U (sigma i) [] = true := by
      rw [show sigma i = (ec ⟨i,hi⟩).val from hright ⟨i,hi⟩]
      exact (ec ⟨i,hi⟩).property
    rw [(noRoot_iff_eq_empty _).mp hi,(noRoot_iff_eq_empty _).mp hj]
    exact isomorphic_refl emptyTree

theorem isomorphic_of_multiset_paddedChildren {T U : TreeSpace}
    (ht : T [] = true) (hu : U [] = true)
    (h : CountableMultisetRelation Isomorphic (paddedChildren T) (paddedChildren U)) :
    Isomorphic T U := by
  obtain ⟨sigma,hsigma⟩ := h
  have hpres (i : ℕ) : paddedChildren T i [] = true ↔
      paddedChildren U (sigma i) [] = true := isomorphic_root_iff (hsigma i)
  let ep : PresentChildren T ≃ PresentChildren U := sigma.subtypeEquiv hpres
  let e : ChildLabels T ≃ ChildLabels U :=
    ((labelPresentEquiv T).trans ep).trans (labelPresentEquiv U).symm
  apply isomorphic_of_child_equiv ht hu e
  intro n
  have hmatch := hsigma (labelPresentEquiv T n).val
  rw [labelPresentEquiv_tree] at hmatch
  have heval : sigma (labelPresentEquiv T n).val = (labelPresentEquiv U (e n)).val := by
    have hh := (labelPresentEquiv U).apply_symm_apply (ep (labelPresentEquiv T n))
    exact (congrArg Subtype.val hh).symm
  rw [heval,labelPresentEquiv_tree] at hmatch
  exact hmatch

theorem isomorphic_iff_paddedChildren (T U : TreeSpace) :
    Isomorphic T U ↔ T [] = U [] ∧
      CountableMultisetRelation Isomorphic (paddedChildren T) (paddedChildren U) := by
  constructor
  · intro h
    refine ⟨?_,multiset_paddedChildren_of_isomorphic h⟩
    have hh := isomorphic_root_iff h
    cases ht : T [] <;> cases hu : U [] <;> simp_all
  · rintro ⟨hroot,hchildren⟩
    by_cases ht : T [] = true
    · exact isomorphic_of_multiset_paddedChildren ht (hroot ▸ ht) hchildren
    · have hu : U [] ≠ true := hroot ▸ ht
      rw [(noRoot_iff_eq_empty T).mp ht,(noRoot_iff_eq_empty U).mp hu]
      exact isomorphic_refl emptyTree

end FSCofinality.RootedTrees

end
end

-- Original module: FSCofinalityProof.HierarchyProducts
section


noncomputable section
open MeasureTheory

namespace FSCofinality

def binaryProduct (E F : CodedRelation) : CodedRelation where
  Carrier := E.Carrier × F.Carrier
  measurableSpace := inferInstance
  rel := fun x y => E.rel x.1 y.1 ∧ F.rel x.2 y.2

def pairFamily (E F : CodedRelation) : ℕ → CodedRelation
  | 0 => E
  | _+1 => F

theorem binaryProduct_reduces_fsTower {E F : CodedRelation} (a b : Ordinal.{0})
    (ha : a < Ordinal.omega 1) (hb : b < Ordinal.omega 1)
    (hE : E.Reduces (fsTower a)) (hF : F.Reduces (fsTower b)) :
    ∃ c : Ordinal.{0}, c < Ordinal.omega 1 ∧ (binaryProduct E F).Reduces (fsTower c) := by
  let stage : ℕ → Ordinal.{0} | 0 => a | _+1 => b
  have hc n : stage n < Ordinal.omega 1 := by cases n <;> assumption
  have hr n : (pairFamily E F n).Reduces (fsTower (stage n)) := by cases n <;> assumption
  obtain ⟨c,hc,hprod⟩ := countableProduct_reduces_fsTower (pairFamily E F) stage hc hr
  refine ⟨c,hc,?_⟩
  apply CodedRelation.Reduces.trans (R := fsTower c) (F := countableProduct (pairFamily E F)) ?_ hprod
  let f (p : E.Carrier × F.Carrier) : ∀ n, (pairFamily E F n).Carrier
    | 0 => p.1
    | _+1 => p.2
  refine ⟨f,?_,?_⟩
  · apply measurable_pi_lambda
    intro n
    cases n
    · exact measurable_fst
    · exact measurable_snd
  · intro x y
    change (E.rel x.1 y.1 ∧ F.rel x.2 y.2) ↔ ∀ n, (pairFamily E F n).rel (f x n) (f y n)
    constructor
    · intro h n
      cases n
      · exact h.1
      · exact h.2
    · intro h
      exact ⟨h 0,h 1⟩

def boolEquality : CodedRelation where
  Carrier := Bool
  measurableSpace := inferInstance
  rel := Eq

theorem boolEquality_reduces_fsTower_zero : boolEquality.Reduces (fsTower 0) := by
  rw [fsTower_zero]
  refine ⟨fun b : Bool => fun _ : ℕ => b,measurable_pi_lambda _ (fun _ => measurable_id),?_⟩
  intro b c
  change b = c ↔ (fun _ : ℕ => b) = (fun _ : ℕ => c)
  exact ⟨fun h => congrArg (fun b : Bool => fun _ : ℕ => b) h,fun h => congrFun h 0⟩

end FSCofinality

end
end

-- Original module: FSCofinalityProof.TreeClassifiers
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order MeasureTheory

namespace FSCofinality.RootedTrees

/-- A total Borel invariant on all trees which is complete on one bounded
well-founded domain. Its definition uses no test for belonging to that domain. -/
structure Classifier (a : Ordinal.{0}) where
  stage : Ordinal.{0}
  countable : stage < Ordinal.omega 1
  code : TreeSpace → (fsTower stage).Carrier
  measurable_code : Measurable code
  invariant : ∀ T U, Isomorphic T U → (fsTower stage).rel (code T) (code U)
  reflects : ∀ T U, BoundedTree T a → BoundedTree U a →
    (fsTower stage).rel (code T) (code U) → Isomorphic T U

def Classifier.relation {a : Ordinal.{0}} (C : Classifier a) : CodedRelation where
  Carrier := TreeSpace
  measurableSpace := inferInstance
  rel := fun T U => (fsTower C.stage).rel (C.code T) (C.code U)

theorem Classifier.relation_reduces {a : Ordinal.{0}} (C : Classifier a) :
    C.relation.Reduces (fsTower C.stage) :=
  ⟨C.code,C.measurable_code,fun _ _ => Iff.rfl⟩

theorem bounded_zero_eq_empty {T : TreeSpace} (h : BoundedTree T 0) : T = emptyTree := by
  apply (noRoot_iff_eq_empty T).mp
  intro hr
  obtain ⟨rho,hrho,hdec⟩ := h
  exact (not_lt_of_ge zero_le) (hrho ⟨[],hr⟩)

def classifier_zero : Classifier 0 where
  stage := 0
  countable := (Cardinal.isSuccLimit_omega 1).pos
  code := fun _ => Classical.choice (regular_fsTower 0).nonempty
  measurable_code := measurable_const
  invariant := fun _ _ _ => (regular_fsTower 0).equivalence.refl _
  reflects := by
    intro T U hT hU h
    rw [bounded_zero_eq_empty hT,bounded_zero_eq_empty hU]
    exact isomorphic_refl _

/-- Successor construction from the exact rooted-tree multiset decomposition.
The caller supplies the separately proved padded-child decomposition. -/
theorem classifier_successor_of_decomposition {a : Ordinal.{0}} (C : Classifier a)
    (children : TreeSpace → ℕ → TreeSpace)
    (hchildren : ∀ i, Measurable (fun T => children T i))
    (hdecomp : ∀ T U, Isomorphic T U ↔ T [] = U [] ∧
      CountableMultisetRelation Isomorphic (children T) (children U))
    (hbound : ∀ T, BoundedTree T (a+1) → ∀ i, BoundedTree (children T i) a) :
    Nonempty (Classifier (a+1)) := by
  obtain ⟨b,hb,hmult⟩ := multisetJump_reduces_fsTower C.relation C.stage C.countable C.relation_reduces
  obtain ⟨f,hf,hfred⟩ := hmult
  obtain ⟨c,hc,hpair⟩ := binaryProduct_reduces_fsTower 0 b
    (Cardinal.isSuccLimit_omega 1).pos hb boolEquality_reduces_fsTower_zero (CodedRelation.Reduces.refl _)
  obtain ⟨g,hg,hgred⟩ := hpair
  refine ⟨⟨c,hc,fun T => g (T [],f (children T)),?_,?_,?_⟩⟩
  · exact hg.comp (((continuous_eval []).measurable).prodMk
      (hf.comp (measurable_pi_lambda _ hchildren)))
  · intro T U hTU
    obtain ⟨hroot,σ,hσ⟩ := (hdecomp T U).mp hTU
    apply (hgred _ _).mp
    refine ⟨hroot,?_⟩
    apply (hfred _ _).mp
    exact ⟨σ,fun i => C.invariant _ _ (hσ i)⟩
  · intro T U hT hU hTU
    have hp := (hgred _ _).mpr hTU
    obtain ⟨σ,hσ⟩ := (hfred _ _).mpr hp.2
    apply (hdecomp T U).mpr
    refine ⟨hp.1,σ,?_⟩
    intro i
    exact C.reflects _ _ (hbound T hT i) (hbound U hU (σ i)) (hσ i)

theorem classifier_limit (a : Ordinal.{0}) (ha : IsSuccLimit a) (hc : a < Ordinal.omega 1)
    (C : ∀ n, Classifier (fundamentalSequence a ha n)) : Nonempty (Classifier a) := by
  obtain ⟨b,hb,hprod⟩ := countableProduct_reduces_fsTower (fun n => fsTower (C n).stage)
    (fun n => (C n).stage) (fun n => (C n).countable) (fun _ => CodedRelation.Reduces.refl _)
  obtain ⟨f,hf,hfred⟩ := hprod
  refine ⟨⟨b,hb,fun T => f (fun n => (C n).code T),?_,?_,?_⟩⟩
  · exact hf.comp (measurable_pi_lambda _ (fun n => (C n).measurable_code))
  · intro T U hTU
    apply (hfred _ _).mp
    exact fun n => (C n).invariant T U hTU
  · intro T U hT hU hTU
    have hcoords := (hfred _ _).mpr hTU
    obtain ⟨t,ht,hTt⟩ := hT.exists_smaller_of_limit ha
    obtain ⟨u,hu,hUu⟩ := hU.exists_smaller_of_limit ha
    obtain ⟨n,hn⟩ := fundamentalSequence_cofinal a ha hc (max t u) (max_lt ht hu)
    exact (C n).reflects T U
      (hTt.mono ((le_max_left _ _).trans hn))
      (hUu.mono ((le_max_right _ _).trans hn)) (hcoords n)

theorem Classifier.treeRelation_reduces {a : Ordinal.{0}} (C : Classifier a) :
    (treeRelation a).Reduces (fsTower C.stage) := by
  refine ⟨fun T => C.code T.val,C.measurable_code.comp measurable_subtype_coe,?_⟩
  intro T U
  exact ⟨C.invariant _ _,C.reflects _ _ T.property U.property⟩

theorem classifier_successor {a : Ordinal.{0}} (C : Classifier a) :
    Nonempty (Classifier (a+1)) :=
  classifier_successor_of_decomposition C paddedChildren
    (fun i => (measurable_pi_apply i).comp measurable_paddedChildren)
    isomorphic_iff_paddedChildren (fun T hT i => hT.paddedChildren_of_succ i)

/-- Total classifiers exist at every countable bound. The limit step takes
all earlier invariants and uses no Borel test of well-founded rank. -/
theorem classifier_exists (a : Ordinal.{0}) : a < Ordinal.omega 1 → Nonempty (Classifier a) := by
  induction a using Ordinal.limitRecOn with
  | zero => intro _; exact ⟨classifier_zero⟩
  | add_one a ih =>
    intro ha
    exact classifier_successor (Classical.choice (ih (lt_trans (lt_add_one a) ha)))
  | limit a ha ih =>
    intro hc
    exact classifier_limit a ha hc (fun n => Classical.choice
      (ih (fundamentalSequence a ha n) (fundamentalSequence_lt a ha n)
        (lt_trans (fundamentalSequence_lt a ha n) hc)))

/-- The bounded rooted-tree hierarchy is cofinal below the concrete
product-limit Friedman--Stanley tower, with no ordinal-index identification. -/
theorem treeRelation_reduces_some_fsTower (a : Ordinal.{0}) (ha : a < Ordinal.omega 1) :
    ∃ b : Ordinal.{0}, b < Ordinal.omega 1 ∧ (treeRelation a).Reduces (fsTower b) := by
  obtain ⟨C⟩ := classifier_exists a ha
  exact ⟨C.stage,C.countable,C.treeRelation_reduces⟩

end FSCofinality.RootedTrees

end
end

-- Original module: Solutions.OriginalTreeComparison
section


set_option autoImplicit false

theorem solution
    (a : Ordinal.{0}) (ha_pos : 0 < a) (ha_countable : a < Ordinal.omega 1) :
    ∃ b : Ordinal.{0}, b < Ordinal.omega 1 ∧
      (FSCofinality.RootedTrees.treeRelation a).Reduces (FSCofinality.fsTower b) := by
  exact FSCofinality.RootedTrees.treeRelation_reduces_some_fsTower a ha_countable

end

#print axioms solution
