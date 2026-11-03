-- Prove2me | solution 1 for FSCofinality.coset_cofinality
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-11-02T15:44:11.937237+00:00
-- url     : https://prove2.me/submissions/e3d98e2e-abfd-47c2-8063-f4cc71ed5441

import Definitions.Def_FSCofinalityCosets20261102
import Definitions.Def_FSCofinalityHierarchy20261102
import Definitions.Def_FSCofinalityStructures20261102
import Definitions.Def_FSCofinalityTrees20261102
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.W.Basic
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.List
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.List
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.Polish

set_option autoImplicit false

-- Original module: FSCofinalityProof.RawObjectsUniverse
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.RawObjects

/-- Small, distinct set-theoretic tags. These need not be von Neumann ordinals. -/
def natTag : ℕ → ZFSet.{0}
  | 0 => ∅
  | n+1 => {natTag n}

theorem natTag_injective : Function.Injective natTag := by
  intro n
  induction n with
  | zero =>
    intro m h
    cases m with
    | zero => rfl
    | succ m =>
      have hm : natTag m ∈ (∅ : ZFSet.{0}) := by
        change natTag m ∈ natTag 0
        rw [h]
        exact ZFSet.mem_singleton.mpr rfl
      exact False.elim (ZFSet.notMem_empty _ hm)
  | succ n ih =>
    intro m h
    cases m with
    | zero =>
      have hn : natTag n ∈ (∅ : ZFSet.{0}) := by
        change natTag n ∈ natTag 0
        rw [← h]
        exact ZFSet.mem_singleton.mpr rfl
      exact False.elim (ZFSet.notMem_empty _ hn)
    | succ m => exact congrArg Nat.succ (ih (ZFSet.singleton_inj.mp h))

def graph (f : ℕ → ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.range (fun n => ZFSet.pair (natTag n) (f n))

theorem graph_injective : Function.Injective graph := by
  intro f g h
  funext n
  have hn : ZFSet.pair (natTag n) (f n) ∈ graph g := by
    rw [← h]
    exact ZFSet.mem_range_self n
  obtain ⟨m,hm⟩ := ZFSet.mem_range.mp hn
  obtain ⟨hidx,hval⟩ := ZFSet.pair_injective hm
  have hmn : m = n := natTag_injective hidx
  subst m
  exact hval.symm

def boolTag (b : Bool) : ZFSet.{0} := natTag (if b then 1 else 0)

theorem boolTag_injective : Function.Injective boolTag := by
  intro b c h
  have hnat := natTag_injective h
  cases b <;> cases c <;> simp_all [boolTag]

def record (kind layer : ℕ) (payload : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.pair (natTag kind) (ZFSet.pair (natTag layer) payload)

@[simp] theorem record_eq_iff {k l k' l' : ℕ} {x y : ZFSet.{0}} :
    record k l x = record k' l' y ↔ k = k' ∧ l = l' ∧ x = y := by
  simp only [record,ZFSet.pair_inj,natTag_injective.eq_iff]

/-- The branching positions are always finite or countably infinite.
Thus raw codes, unlike the auxiliary ZFC semantic universe, live in Type 0. -/
inductive Shape (Layer : Type) where
  | sourceAtom : (ℕ → Bool) → Shape Layer
  | extraAtom : ℕ → Shape Layer
  | empty : Layer → Shape Layer
  | collection : Layer → Shape Layer
  | source : Layer → Shape Layer
  | filler : Layer → (n : ℕ) → (Fin n → ℕ) → Shape Layer

def Positions {Layer : Type} : Shape Layer → Type
  | .sourceAtom _ => Empty
  | .extraAtom _ => Empty
  | .empty _ => Empty
  | .collection _ => ℕ
  | .source _ => ℕ
  | .filler _ n _ => Fin n

abbrev RawCode (Layer : Type) := WType (@Positions Layer)

def semanticAlgebra {Layer : Type} (layerCode : Layer ↪ ℕ)
    (s : Σ a : Shape Layer, Positions a → ZFSet.{0}) : ZFSet.{0} :=
  match s with
  | ⟨.sourceAtom r,_⟩ => record 0 0 (graph (fun n => boolTag (r n)))
  | ⟨.extraAtom n,_⟩ => record 1 0 (natTag n)
  | ⟨.empty l,_⟩ => record 2 (layerCode l) ∅
  | ⟨.collection l,f⟩ => record 2 (layerCode l) (ZFSet.range f)
  | ⟨.source l,f⟩ => record 3 (layerCode l) (graph f)
  | ⟨.filler l n tags,f⟩ => record 4 (layerCode l)
      (ZFSet.range (fun i : Fin n => ZFSet.pair (natTag (tags i)) (f i)))

def evalCode {Layer : Type} (layerCode : Layer ↪ ℕ) : RawCode Layer → ZFSet.{0} :=
  WType.elim _ (semanticAlgebra layerCode)

def codeSetoid {Layer : Type} (layerCode : Layer ↪ ℕ) : Setoid (RawCode Layer) :=
  Setoid.ker (evalCode layerCode)

/-- Semantic names are quotients of actual small codes. No standard Borel
structure is asserted on this semantic quotient. -/
def Object {Layer : Type} (layerCode : Layer ↪ ℕ) := Quotient (codeSetoid layerCode)

def eval {Layer : Type} {layerCode : Layer ↪ ℕ} : Object layerCode → ZFSet.{0} :=
  Quotient.lift (evalCode layerCode) (fun _ _ h => h)

theorem eval_injective {Layer : Type} {layerCode : Layer ↪ ℕ} :
    Function.Injective (eval (layerCode := layerCode)) := by
  intro x y h
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound h

@[simp] theorem eval_out {Layer : Type} {layerCode : Layer ↪ ℕ} (x : Object layerCode) :
    evalCode layerCode (Quotient.out x) = eval x := by
  exact congrArg eval (Quotient.out_eq x)

def make {Layer : Type} {layerCode : Layer ↪ ℕ} (a : Shape Layer)
    (f : Positions a → Object layerCode) : Object layerCode :=
  Quotient.mk _ (WType.mk a (fun i => Quotient.out (f i)))

theorem eval_make {Layer : Type} {layerCode : Layer ↪ ℕ} (a : Shape Layer)
    (f : Positions a → Object layerCode) :
    eval (make a f) = semanticAlgebra layerCode ⟨a,fun i => eval (f i)⟩ := by
  change semanticAlgebra layerCode ⟨a,fun i => evalCode layerCode (Quotient.out (f i))⟩ = _
  simp only [eval_out]

section Constructors
variable {Layer : Type} {layerCode : Layer ↪ ℕ}

def sourceAtom (r : ℕ → Bool) : Object layerCode := make (.sourceAtom r) Empty.elim
def extraAtom (n : ℕ) : Object layerCode := make (.extraAtom n) Empty.elim

def collection (l : Layer) (x : Option (ℕ → Object layerCode)) : Object layerCode :=
  match x with | none => make (.empty l) Empty.elim | some f => make (.collection l) f

def sourceSequence (l : Layer) (x : ℕ → Object layerCode) : Object layerCode :=
  make (.source l) x

def finiteFiller (l : Layer) (A : Finset (ℕ × Object layerCode)) : Object layerCode := by
  classical
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  exact make (.filler l (Fintype.card A) (fun i => (e i).val.1))
    (fun i => (e i).val.2)

@[simp] theorem eval_sourceAtom (r : ℕ → Bool) :
    eval (sourceAtom (layerCode := layerCode) r) = record 0 0 (graph (fun n => boolTag (r n))) := by
  exact eval_make _ _

@[simp] theorem eval_extraAtom (n : ℕ) :
    eval (extraAtom (layerCode := layerCode) n) = record 1 0 (natTag n) := by
  exact eval_make _ _

@[simp] theorem eval_collection_none (l : Layer) :
    eval (collection (layerCode := layerCode) l none) = record 2 (layerCode l) ∅ := by
  exact eval_make _ _

@[simp] theorem eval_collection_some (l : Layer) (f : ℕ → Object layerCode) :
    eval (collection l (some f)) = record 2 (layerCode l) (ZFSet.range (fun i => eval (f i))) := by
  exact eval_make _ _

@[simp] theorem eval_sourceSequence (l : Layer) (f : ℕ → Object layerCode) :
    eval (sourceSequence l f) = record 3 (layerCode l) (graph (fun i => eval (f i))) := by
  exact eval_make _ _

@[simp] theorem eval_finiteFiller (l : Layer) (A : Finset (ℕ × Object layerCode)) :
    eval (finiteFiller l A) = record 4 (layerCode l)
      (ZFSet.range (fun p : A => ZFSet.pair (natTag p.val.1) (eval p.val.2))) := by
  classical
  unfold finiteFiller
  rw [eval_make]
  change record 4 (layerCode l) (ZFSet.range _) = _
  congr 1
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_range]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨(Fintype.equivFin A).symm i,rfl⟩
  · rintro ⟨p,rfl⟩
    exact ⟨Fintype.equivFin A p,by simp⟩

theorem sourceAtom_injective : Function.Injective (sourceAtom (layerCode := layerCode)) := by
  intro r s h
  have hp := congrArg eval h
  simp only [eval_sourceAtom,record_eq_iff,true_and] at hp
  have hfun := graph_injective hp
  funext n
  exact boolTag_injective (congrFun hfun n)

theorem extraAtom_injective : Function.Injective (extraAtom (layerCode := layerCode)) := by
  intro n m h
  have hp := congrArg eval h
  simp only [eval_extraAtom,record_eq_iff,true_and] at hp
  exact natTag_injective hp

theorem sourceAtom_ne_extraAtom (r : ℕ → Bool) (n : ℕ) :
    sourceAtom (layerCode := layerCode) r ≠ extraAtom n := by
  intro h
  have hp := congrArg eval h
  simp only [eval_sourceAtom,eval_extraAtom,record_eq_iff] at hp
  exact Nat.zero_ne_add_one 0 hp.1

theorem sourceSequence_injective (l : Layer) :
    Function.Injective (sourceSequence (layerCode := layerCode) l) := by
  intro f g h
  have hp := congrArg eval h
  simp only [eval_sourceSequence,record_eq_iff,true_and] at hp
  have hfun := graph_injective hp
  funext n
  exact eval_injective (congrFun hfun n)

theorem finiteFiller_injective (l : Layer) :
    Function.Injective (finiteFiller (layerCode := layerCode) l) := by
  intro A B h
  have hp := congrArg eval h
  simp only [eval_finiteFiller,record_eq_iff,true_and] at hp
  ext p
  constructor
  · intro hpA
    have hm : ZFSet.pair (natTag p.1) (eval p.2) ∈
        ZFSet.range (fun q : B => ZFSet.pair (natTag q.val.1) (eval q.val.2)) := by
      rw [← hp]
      exact ZFSet.mem_range_self (⟨p,hpA⟩ : A)
    obtain ⟨q,hq⟩ := ZFSet.mem_range.mp hm
    obtain ⟨hidx,hobj⟩ := ZFSet.pair_injective hq
    have hqp : q.val = p := Prod.ext (natTag_injective hidx) (eval_injective hobj)
    exact hqp ▸ q.property
  · intro hpB
    have hm : ZFSet.pair (natTag p.1) (eval p.2) ∈
        ZFSet.range (fun q : A => ZFSet.pair (natTag q.val.1) (eval q.val.2)) := by
      rw [hp]
      exact ZFSet.mem_range_self (⟨p,hpB⟩ : B)
    obtain ⟨q,hq⟩ := ZFSet.mem_range.mp hm
    obtain ⟨hidx,hobj⟩ := ZFSet.pair_injective hq
    have hqp : q.val = p := Prod.ext (natTag_injective hidx) (eval_injective hobj)
    exact hqp ▸ q.property

theorem sourceSequence_ne_finiteFiller (l m : Layer)
    (f : ℕ → Object layerCode) (A : Finset (ℕ × Object layerCode)) :
    sourceSequence l f ≠ finiteFiller m A := by
  intro h
  have hp := congrArg eval h
  simp only [eval_sourceSequence,eval_finiteFiller,record_eq_iff] at hp
  exact (by decide : (3 : ℕ) ≠ 4) hp.1

/-- Ordinary membership in the countable-set payload of a successor object. -/
def Member (u x : Object layerCode) : Prop :=
  ∃ l : Layer, ∃ p : ZFSet.{0}, eval x = record 2 (layerCode l) p ∧ eval u ∈ p

@[simp] theorem member_collection_none (l : Layer) (u : Object layerCode) :
    ¬ Member u (collection l none) := by
  rintro ⟨m,p,hp,hm⟩
  rw [eval_collection_none] at hp
  have he : (∅ : ZFSet.{0}) = p := (record_eq_iff.mp hp).2.2
  exact ZFSet.notMem_empty _ (he ▸ hm)

@[simp] theorem member_collection_some (l : Layer) (f : ℕ → Object layerCode)
    (u : Object layerCode) : Member u (collection l (some f)) ↔ ∃ i, f i = u := by
  constructor
  · rintro ⟨m,p,hp,hm⟩
    rw [eval_collection_some] at hp
    have he := (record_eq_iff.mp hp).2.2
    rw [← he] at hm
    obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hm
    exact ⟨i,eval_injective hi⟩
  · rintro ⟨i,rfl⟩
    exact ⟨l,_,eval_collection_some l f,ZFSet.mem_range_self i⟩

def singleton (l : Layer) (u : Object layerCode) : Object layerCode :=
  collection l (some (fun _ => u))

def doubleton (l : Layer) (u v : Object layerCode) : Object layerCode :=
  collection l (some (fun n => if n = 0 then u else v))

def finiteCollection (l : Layer) (A : Finset (Object layerCode)) : Object layerCode := by
  classical
  exact if h : A.Nonempty then
    letI : Nonempty A := ⟨⟨h.choose,h.choose_spec⟩⟩
    collection l (some (fun n => ((exists_surjective_nat A).choose n).val))
  else collection l none

@[simp] theorem member_finiteCollection (l : Layer) (A : Finset (Object layerCode))
    (u : Object layerCode) : Member u (finiteCollection l A) ↔ u ∈ A := by
  classical
  by_cases h : A.Nonempty
  · letI : Nonempty A := ⟨⟨h.choose,h.choose_spec⟩⟩
    rw [finiteCollection,dif_pos h,member_collection_some]
    constructor
    · rintro ⟨i,rfl⟩
      exact ((exists_surjective_nat A).choose i).property
    · intro hu
      obtain ⟨i,hi⟩ := (exists_surjective_nat A).choose_spec (⟨u,hu⟩ : A)
      exact ⟨i,congrArg Subtype.val hi⟩
  · rw [finiteCollection,dif_neg h]
    simp only [member_collection_none,false_iff]
    intro hu
    exact h ⟨u,hu⟩

theorem finiteCollection_injective (l : Layer) :
    Function.Injective (finiteCollection (layerCode := layerCode) l) := by
  intro A B h
  ext u
  have hm : Member u (finiteCollection l A) ↔ Member u (finiteCollection l B) := by rw [h]
  simpa only [member_finiteCollection] using hm

theorem finiteCollection_is_collection (l : Layer) (A : Finset (Object layerCode)) :
    ∃ x, finiteCollection l A = collection l x := by
  classical
  unfold finiteCollection
  split <;> exact ⟨_,rfl⟩

@[simp] theorem member_singleton (l : Layer) (u v : Object layerCode) :
    Member u (singleton l v) ↔ u = v := by
  simp only [singleton,member_collection_some,exists_const,eq_comm]

@[simp] theorem member_doubleton (l : Layer) (u v w : Object layerCode) :
    Member u (doubleton l v w) ↔ u = v ∨ u = w := by
  rw [doubleton,member_collection_some]
  constructor
  · rintro ⟨n,hn⟩
    by_cases h : n = 0
    · exact Or.inl (by simpa only [if_pos h] using hn.symm)
    · exact Or.inr (by simpa only [if_neg h] using hn.symm)
  · rintro (h | h)
    · exact ⟨0,by simpa only [if_pos rfl] using h.symm⟩
    · exact ⟨1,by simpa using h.symm⟩

@[simp] theorem eval_singleton (l : Layer) (u : Object layerCode) :
    eval (singleton l u) = record 2 (layerCode l) {eval u} := by
  rw [singleton,eval_collection_some]
  apply congrArg (record 2 (layerCode l))
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_range,ZFSet.mem_singleton,exists_const,eq_comm]

@[simp] theorem eval_doubleton (l : Layer) (u v : Object layerCode) :
    eval (doubleton l u v) = record 2 (layerCode l) {eval u,eval v} := by
  rw [doubleton,eval_collection_some]
  apply congrArg (record 2 (layerCode l))
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_range,ZFSet.mem_pair]
  constructor
  · rintro ⟨n,rfl⟩
    by_cases h : n = 0 <;> simp [h]
  · rintro (h | h)
    · exact ⟨0,by simpa only [if_pos rfl] using h.symm⟩
    · exact ⟨1,by simpa using h.symm⟩

@[simp] theorem singleton_eq_iff (l : Layer) (u v : Object layerCode) :
    singleton l u = singleton l v ↔ u = v := by
  constructor
  · intro h
    have hp := congrArg eval h
    simp only [eval_singleton,record_eq_iff,true_and,ZFSet.singleton_inj] at hp
    exact eval_injective hp
  · exact congrArg (singleton l)

theorem doubleton_comm (l : Layer) (u v : Object layerCode) :
    doubleton l u v = doubleton l v u := by
  apply eval_injective
  rw [eval_doubleton,eval_doubleton]
  apply congrArg (record 2 (layerCode l))
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_pair,or_comm]

theorem doubleton_eq_iff (l : Layer) (a b c d : Object layerCode) :
    doubleton l a b = doubleton l c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a = c ∨ a = d := (member_doubleton l a c d).mp (by rw [← h]; simp)
    have hb : b = c ∨ b = d := (member_doubleton l b c d).mp (by rw [← h]; simp)
    have hc : c = a ∨ c = b := (member_doubleton l c a b).mp (by rw [h]; simp)
    have hd : d = a ∨ d = b := (member_doubleton l d a b).mp (by rw [h]; simp)
    aesop
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact doubleton_comm l _ _

theorem singleton_ne_doubleton (l : Layer) (a b u : Object layerCode) (hab : a ≠ b) :
    singleton l a ≠ doubleton l b u := by
  intro h
  have hm : Member b (singleton l a) := by rw [h]; simp
  exact hab ((member_singleton l b a).mp hm).symm

/-- The manuscript's two-member tag code, using the next two successor layers. -/
def Enc (inner outer : Layer) (tag base u : Object layerCode) : Object layerCode :=
  doubleton outer (singleton inner tag) (doubleton inner base u)

theorem Enc_injective (inner outer : Layer) (tag base : Object layerCode) (ht : tag ≠ base) :
    Function.Injective (Enc inner outer tag base) := by
  intro u v h
  rcases (doubleton_eq_iff outer _ _ _ _).mp h with ⟨hs,hp⟩ | ⟨hcross,_⟩
  · rcases (doubleton_eq_iff inner _ _ _ _).mp hp with ⟨_,huv⟩ | ⟨hbv,hub⟩
    · exact huv
    · exact hub.trans hbv
  · exact False.elim (singleton_ne_doubleton inner tag base v ht hcross)

theorem Enc_ne (inner outer : Layer) (tag tag' base u v : Object layerCode)
    (ht : tag ≠ base) (htt : tag ≠ tag') :
    Enc inner outer tag base u ≠ Enc inner outer tag' base v := by
  intro h
  rcases (doubleton_eq_iff outer _ _ _ _).mp h with ⟨hs,_⟩ | ⟨hcross,_⟩
  · exact htt ((singleton_eq_iff inner tag tag').mp hs)
  · exact singleton_ne_doubleton inner tag base v ht hcross

theorem Enc_member_iff (inner outer : Layer) (tag base u c : Object layerCode) :
    Member c (Enc inner outer tag base u) ↔
      c = singleton inner tag ∨ c = doubleton inner base u := member_doubleton _ _ _ _

theorem collection_ext (l : Layer) (x y : Option (ℕ → Object layerCode))
    (h : ∀ u, Member u (collection l x) ↔ Member u (collection l y)) :
    collection l x = collection l y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some g =>
      have hg : Member (g 0) (collection l (some g)) := (member_collection_some _ _ _).mpr ⟨0,rfl⟩
      exact False.elim (member_collection_none _ _ ((h _).mpr hg))
  | some f =>
    cases y with
    | none =>
      have hf : Member (f 0) (collection l (some f)) := (member_collection_some _ _ _).mpr ⟨0,rfl⟩
      exact False.elim (member_collection_none _ _ ((h _).mp hf))
    | some g =>
      apply eval_injective
      rw [eval_collection_some,eval_collection_some]
      apply congrArg (record 2 (layerCode l))
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_range]
      constructor
      · rintro ⟨i,rfl⟩
        have hf : Member (f i) (collection l (some f)) := (member_collection_some _ _ _).mpr ⟨i,rfl⟩
        obtain ⟨j,hj⟩ := (member_collection_some _ _ _).mp ((h _).mp hf)
        exact ⟨j,congrArg eval hj⟩
      · rintro ⟨j,rfl⟩
        have hg : Member (g j) (collection l (some g)) := (member_collection_some _ _ _).mpr ⟨j,rfl⟩
        obtain ⟨i,hi⟩ := (member_collection_some _ _ _).mp ((h _).mpr hg)
        exact ⟨i,congrArg eval hi⟩

theorem collection_some_eq_iff (l : Layer) (f g : ℕ → Object layerCode) :
    collection l (some f) = collection l (some g) ↔
      (∀ i, ∃ j, f i = g j) ∧ (∀ j, ∃ i, f i = g j) := by
  constructor
  · intro h
    constructor
    · intro i
      have hm : Member (f i) (collection l (some g)) := by rw [← h]; simp
      obtain ⟨j,hj⟩ := (member_collection_some _ _ _).mp hm
      exact ⟨j,hj.symm⟩
    · intro j
      have hm : Member (g j) (collection l (some f)) := by rw [h]; simp
      exact (member_collection_some _ _ _).mp hm
  · rintro ⟨hfg,hgf⟩
    apply collection_ext
    intro u
    simp only [member_collection_some]
    constructor
    · rintro ⟨i,rfl⟩
      obtain ⟨j,hj⟩ := hfg i
      exact ⟨j,hj.symm⟩
    · rintro ⟨j,rfl⟩
      exact hgf j

theorem Enc_ne_singleton (inner outer : Layer) (tag base u v : Object layerCode)
    (ht : tag ≠ base) : Enc inner outer tag base u ≠ singleton outer v := by
  intro h
  have hs : singleton inner tag = v := (member_singleton _ _ _).mp (by rw [← h]; simp [Enc])
  have hp : doubleton inner base u = v := (member_singleton _ _ _).mp (by rw [← h]; simp [Enc])
  exact singleton_ne_doubleton inner tag base u ht (hs.trans hp.symm)

@[simp] theorem finiteCollection_singleton (l : Layer) (u : Object layerCode) :
    finiteCollection l {u} = singleton l u := by
  classical
  obtain ⟨x,hx⟩ := finiteCollection_is_collection l {u}
  rw [hx]
  apply collection_ext
  intro z
  rw [← hx,member_finiteCollection]
  simp only [singleton,member_collection_some,Finset.mem_singleton,exists_const,eq_comm]

@[simp] theorem finiteCollection_doubleton (l : Layer) (u v : Object layerCode) :
    finiteCollection l {u,v} = doubleton l u v := by
  classical
  obtain ⟨x,hx⟩ := finiteCollection_is_collection l {u,v}
  rw [hx]
  apply collection_ext
  intro z
  rw [← hx,member_finiteCollection]
  change z ∈ ({u,v} : Finset (Object layerCode)) ↔ Member z (doubleton l u v)
  rw [member_doubleton]
  simp only [Finset.mem_insert,Finset.mem_singleton]

end Constructors

end FSCofinality.RawObjects

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

-- Original module: FSCofinalityProof.RawObjectsFrame
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects.Frame

def top (η : Ordinal.{0}) : Ordinal.{0} := η + Ordinal.omega0

theorem lt_top (η : Ordinal.{0}) : η < top η :=
  lt_add_of_pos_right η Ordinal.omega0_pos

theorem top_isSuccLimit (η : Ordinal.{0}) : IsSuccLimit (top η) :=
  Ordinal.isSuccLimit_add η Ordinal.isSuccLimit_omega0

theorem top_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) :
    top η < Ordinal.omega 1 :=
  (Ordinal.isPrincipal_add_omega 1) hη Ordinal.omega0_lt_omega_one

/-- The top fundamental sequence is prescribed; all lower source stages
keep the fundamental sequences in the fixed hierarchy definitions. -/
def q (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) : ℕ → Ordinal.{0} :=
  if lam = top η then fun n => η + n else fundamentalSequence lam hlam

@[simp] theorem q_top (η : Ordinal.{0}) (n : ℕ) :
    q η (top η) (top_isSuccLimit η) n = η + n := by simp [q]

theorem q_of_le_source (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (h : lam ≤ η) :
    q η lam hlam = fundamentalSequence lam hlam := by
  have hne : lam ≠ top η := ne_of_lt (lt_of_le_of_lt h (lt_top η))
  simp only [q,if_neg hne]

theorem q_lt (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) : q η lam hlam n < lam := by
  by_cases h : lam = top η
  · subst lam
    simp only [q,if_pos rfl]
    exact (add_lt_add_iff_left η).mpr (Ordinal.natCast_lt_omega0 n)
  · simpa only [q,if_neg h] using fundamentalSequence_lt lam hlam n

theorem q_strictMono (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (hc : lam < Ordinal.omega 1) : StrictMono (q η lam hlam) := by
  by_cases h : lam = top η
  · subst lam
    intro n m hnm
    simp only [q,if_pos rfl]
    exact (add_lt_add_iff_left η).mpr (by exact_mod_cast hnm)
  · simpa only [q,if_neg h] using fundamentalSequence_strictMono lam hlam hc

theorem q_cofinal (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (hc : lam < Ordinal.omega 1) (b : Ordinal.{0}) (hb : b < lam) :
    ∃ n, b ≤ q η lam hlam n := by
  by_cases h : lam = top η
  · subst lam
    obtain ⟨d,hd,hbd⟩ := (Ordinal.lt_add_iff Ordinal.omega0_ne_zero).mp hb
    obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp hd
    exact ⟨n,by simpa only [q,if_pos rfl,hn] using hbd⟩
  · simpa only [q,if_neg h] using fundamentalSequence_cofinal lam hlam hc b hb

def sigma (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) : ℕ → Ordinal.{0}
  | 0 => q η lam hlam 0
  | n+1 => max (q η lam hlam (n+1)) (sigma η lam hlam n + 2)

def rho (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) : Ordinal.{0} :=
  sigma η lam hlam n + 1

def delta (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) : Ordinal.{0} :=
  sigma η lam hlam n + 2

theorem q_le_sigma (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) :
    q η lam hlam n ≤ sigma η lam hlam n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

theorem delta_le_sigma_next (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) :
    delta η lam hlam n ≤ sigma η lam hlam (n+1) := le_max_right _ _

theorem sigma_lt (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) :
    sigma η lam hlam n < lam := by
  induction n with
  | zero => exact q_lt η lam hlam 0
  | succ n ih =>
    apply max_lt (q_lt η lam hlam (n+1))
    simpa only [succ_eq_add_one,add_assoc,one_add_one_eq_two] using
      hlam.succ_lt (hlam.succ_lt ih)

theorem rho_lt (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) :
    rho η lam hlam n < lam := hlam.succ_lt (sigma_lt η lam hlam n)

theorem delta_lt (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) :
    delta η lam hlam n < lam := by
  simpa only [delta,succ_eq_add_one,add_assoc,one_add_one_eq_two] using
    hlam.succ_lt (hlam.succ_lt (sigma_lt η lam hlam n))

theorem delta_strictMono (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam) :
    StrictMono (delta η lam hlam) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact lt_of_le_of_lt (delta_le_sigma_next η lam hlam n)
    (lt_add_of_pos_right _ (by norm_num : (0 : Ordinal.{0}) < 2))

theorem delta_cofinal (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (hc : lam < Ordinal.omega 1) (b : Ordinal.{0}) (hb : b < lam) :
    ∃ n, b ≤ delta η lam hlam n := by
  obtain ⟨n,hn⟩ := q_cofinal η lam hlam hc b hb
  exact ⟨n,hn.trans ((q_le_sigma η lam hlam n).trans le_self_add)⟩

theorem exists_le_rho (η lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (hc : lam < Ordinal.omega 1) (b : Ordinal.{0}) (hb : b < lam) :
    ∃ n, b ≤ rho η lam hlam n := by
  obtain ⟨n,hn⟩ := q_cofinal η lam hlam hc b hb
  exact ⟨n,hn.trans ((q_le_sigma η lam hlam n).trans le_self_add)⟩

/-- Small codes for exactly the layers at or below the top ordinal. -/
abbrev Layer (η : Ordinal.{0}) := (top η + 1).ToType

def rank {η : Ordinal.{0}} (l : Layer η) : Ordinal.{0} := l.toOrd.val

theorem rank_le_top {η : Ordinal.{0}} (l : Layer η) : rank l ≤ top η :=
  lt_add_one_iff.mp l.toOrd.property

def ofOrdinal (η a : Ordinal.{0}) (ha : a ≤ top η) : Layer η :=
  Ordinal.ToType.mk ⟨a,lt_add_one_iff.mpr ha⟩

@[simp] theorem rank_ofOrdinal (η a : Ordinal.{0}) (ha : a ≤ top η) :
    rank (ofOrdinal η a ha) = a := by
  exact congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)

@[simp] theorem ofOrdinal_rank {η : Ordinal.{0}} (l : Layer η) :
    ofOrdinal η (rank l) (rank_le_top l) = l := Ordinal.ToType.mk.apply_symm_apply l

theorem layer_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) : Countable (Layer η) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType]
  apply Cardinal.lt_aleph_one_iff.mp
  apply Cardinal.lt_omega_iff_card_lt.mp
  exact (Cardinal.isSuccLimit_omega 1).succ_lt (top_countable η hη)

def layerCode (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) : Layer η ↪ ℕ := by
  letI := layer_countable η hη
  letI := Encodable.ofCountable (Layer η)
  exact ⟨Encodable.encode,Encodable.encode_injective⟩

end FSCofinality.RawObjects.Frame

end
end

-- Original module: FSCofinalityProof.RawObjectsLifts
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

abbrev Ambient (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) := Object (Frame.layerCode η hη)

/-- Outside the intended bounded range this is a harmless default layer. -/
def level (η a : Ordinal.{0}) : Frame.Layer η :=
  if h : a ≤ Frame.top η then Frame.ofOrdinal η a h else Frame.ofOrdinal η 0 zero_le

@[simp] theorem level_rank (η a : Ordinal.{0}) (h : a ≤ Frame.top η) :
    Frame.rank (level η a) = a := by simp only [level,dif_pos h,Frame.rank_ofOrdinal]

def liftIndex (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (hle : lam ≤ Frame.top η)
    (b : Ordinal.{0}) (hb : b < lam) : ℕ :=
  Nat.find (Frame.exists_le_rho η lam hlam (lt_of_le_of_lt hle (Frame.top_countable η hη)) b hb)

theorem liftIndex_spec (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (hle : lam ≤ Frame.top η)
    (b : Ordinal.{0}) (hb : b < lam) :
    b ≤ Frame.rho η lam hlam (liftIndex η hη lam hlam hle b hb) := by
  unfold liftIndex
  exact Nat.find_spec (Frame.exists_le_rho η lam hlam
    (lt_of_le_of_lt hle (Frame.top_countable η hη)) b hb)

/-- Canonical lifts recurse on the target layer. A limit lift is a finite
support at a new singleton column. No composition identity is imposed. -/
def lift (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (b a : Ordinal.{0}) :
    Ambient η hη → Ambient η hη :=
  Ordinal.limitRecOn a id
    (fun c rec => if b = c+1 then id else fun u => singleton (level η (c+1)) (rec u))
    (fun lam hlam rec =>
      if hle : lam ≤ Frame.top η then
        if hb : b < lam then
          let n := liftIndex η hη lam hlam hle b hb
          fun u => finiteFiller (level η lam)
            {(n,singleton (level η (Frame.delta η lam hlam n))
              (rec (Frame.rho η lam hlam n) (Frame.rho_lt η lam hlam n) u))}
        else id
      else id)

@[simp] theorem lift_zero (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (b : Ordinal.{0}) :
    lift η hη b 0 = id := by unfold lift; rw [Ordinal.limitRecOn_zero]

theorem lift_add_one (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (b a : Ordinal.{0}) :
    lift η hη b (a+1) =
      if b = a+1 then id else fun u => singleton (level η (a+1)) (lift η hη b a u) := by
  unfold lift
  rw [Ordinal.limitRecOn_add_one]

theorem lift_limit (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (hle : lam ≤ Frame.top η)
    (b : Ordinal.{0}) (hb : b < lam) :
    lift η hη b lam =
      let n := liftIndex η hη lam hlam hle b hb
      fun u => finiteFiller (level η lam)
        {(n,singleton (level η (Frame.delta η lam hlam n))
          (lift η hη b (Frame.rho η lam hlam n) u))} := by
  unfold lift
  rw [Ordinal.limitRecOn_limit _ _ _ _ hlam]
  simp only [dif_pos hle,dif_pos hb]

@[simp] theorem lift_self (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (a : Ordinal.{0}) :
    lift η hη a a = id := by
  induction a using Ordinal.limitRecOn with
  | zero => exact lift_zero η hη 0
  | add_one a _ => rw [lift_add_one,if_pos rfl]
  | limit a ha _ =>
    unfold lift
    rw [Ordinal.limitRecOn_limit _ _ _ _ ha]
    split <;> simp

theorem lift_injective (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (b a : Ordinal.{0}) (hba : b ≤ a) (ha : a ≤ Frame.top η) :
    Function.Injective (lift η hη b a) := by
  induction a using Ordinal.limitRecOn generalizing b with
  | zero => simpa only [lift_zero] using Function.injective_id
  | add_one a ih =>
    by_cases h : b = a+1
    · subst b
      simpa only [lift_self] using Function.injective_id
    · have hba' : b ≤ a := lt_add_one_iff.mp (lt_of_le_of_ne hba h)
      have haa : a ≤ Frame.top η := (le_of_lt (lt_add_one a)).trans ha
      rw [lift_add_one,if_neg h]
      intro u v huv
      exact ih b hba' haa ((singleton_eq_iff _ _ _).mp huv)
  | limit a haLim ih =>
    by_cases h : b = a
    · subst b
      simpa only [lift_self] using Function.injective_id
    · have hblt : b < a := lt_of_le_of_ne hba h
      rw [lift_limit η hη a haLim ha b hblt]
      let n := liftIndex η hη a haLim ha b hblt
      intro u v huv
      have hsupport := finiteFiller_injective (level η a) huv
      have hcol : singleton (level η (Frame.delta η a haLim n))
          (lift η hη b (Frame.rho η a haLim n) u) =
          singleton (level η (Frame.delta η a haLim n))
          (lift η hη b (Frame.rho η a haLim n) v) := by
        exact congrArg Prod.snd (Finset.singleton_injective hsupport)
      exact ih (Frame.rho η a haLim n) (Frame.rho_lt η a haLim n) b
        (liftIndex_spec η hη a haLim ha b hblt)
        ((Frame.rho_lt η a haLim n).le.trans ha) ((singleton_eq_iff _ _ _).mp hcol)

end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.RawObjectsPools
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

def tag (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (a : Ordinal.{0}) (n : ℕ) :
    Ambient η hη := lift η hη 0 a (extraAtom n)

theorem tag_injective (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) (ha : a ≤ Frame.top η) : Function.Injective (tag η hη a) := by
  intro n m h
  exact extraAtom_injective (lift_injective η hη 0 a zero_le ha h)

def dataColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) (v : Ambient η hη) : Ambient η hη :=
  Enc (level η (Frame.rho η lam hlam n)) (level η (Frame.delta η lam hlam n))
    (tag η hη (Frame.sigma η lam hlam n) 1) (tag η hη (Frame.sigma η lam hlam n) 3)
    (lift η hη (Frame.q η lam hlam n) (Frame.sigma η lam hlam n) v)

def markerColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) : Ambient η hη :=
  Enc (level η (Frame.rho η lam hlam n)) (level η (Frame.delta η lam hlam n))
    (tag η hη (Frame.sigma η lam hlam n) 2) (tag η hη (Frame.sigma η lam hlam n) 3)
    (tag η hη (Frame.sigma η lam hlam n) 3)

/-- The new (non-propagated) columns; all parameters come from lower layers. -/
def NewColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)) (n : ℕ) (c : Ambient η hη) : Prop :=
  (∃ v ∈ lower (Frame.q η lam hlam n) (Frame.q_lt η lam hlam n),
    c = dataColumn η hη lam hlam n v) ∨
  c = markerColumn η hη lam hlam n ∨
  ∃ v ∈ lower (Frame.rho η lam hlam n) (Frame.rho_lt η lam hlam n),
    c = singleton (level η (Frame.delta η lam hlam n)) v

def SuccessorSet (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) (lower : Set (Ambient η hη)) : Set (Ambient η hη) :=
  {x | ∃ u : Option (ℕ → Ambient η hη), x = collection (level η (a+1)) u ∧
    ∀ f, u = some f → ∀ i, f i ∈ lower}

def LimitSet (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)) : Set (Ambient η hη) :=
  {x | (∃ s : ℕ → Ambient η hη, x = sourceSequence (level η lam) s ∧
      ∀ n, s n ∈ lower (Frame.q η lam hlam n) (Frame.q_lt η lam hlam n)) ∨
    (∃ A : Finset (ℕ × Ambient η hη), x = finiteFiller (level η lam) A ∧
      ∀ p ∈ A, NewColumn η hη lam hlam lower p.1 p.2)}

/-- Actual typed ambient layers as subsets of the small semantic universe. -/
def Valid (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (a : Ordinal.{0}) : Set (Ambient η hη) :=
  Ordinal.limitRecOn a (range sourceAtom ∪ range extraAtom)
    (SuccessorSet η hη)
    (LimitSet η hη)

abbrev W (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (a : Ordinal.{0}) :=
  {x : Ambient η hη // x ∈ Valid η hη a}

@[simp] theorem valid_zero (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) :
    Valid η hη 0 = range sourceAtom ∪ range extraAtom := by
  unfold Valid
  rw [Ordinal.limitRecOn_zero]

theorem valid_add_one (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (a : Ordinal.{0}) :
    Valid η hη (a+1) = SuccessorSet η hη a (Valid η hη a) := by
  unfold Valid
  rw [Ordinal.limitRecOn_add_one]

theorem valid_limit (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) :
    Valid η hη lam = LimitSet η hη lam hlam (fun b _ => Valid η hη b) := by
  unfold Valid
  rw [Ordinal.limitRecOn_limit _ _ _ _ hlam]

theorem valid_singleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) {u : Ambient η hη} (hu : u ∈ Valid η hη a) :
    singleton (level η (a+1)) u ∈ Valid η hη (a+1) := by
  rw [valid_add_one]
  refine ⟨some (fun _ => u),rfl,?_⟩
  intro f hf i
  cases hf
  exact hu

theorem valid_doubleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) {u v : Ambient η hη}
    (hu : u ∈ Valid η hη a) (hv : v ∈ Valid η hη a) :
    doubleton (level η (a+1)) u v ∈ Valid η hη (a+1) := by
  rw [valid_add_one]
  refine ⟨some (fun n => if n = 0 then u else v),rfl,?_⟩
  intro f hf i
  cases hf
  dsimp only
  split <;> assumption

theorem valid_lift (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (b a : Ordinal.{0}) (hba : b ≤ a) (ha : a ≤ Frame.top η)
    {u : Ambient η hη} (hu : u ∈ Valid η hη b) :
    lift η hη b a u ∈ Valid η hη a := by
  induction a using Ordinal.limitRecOn generalizing b u with
  | zero =>
    have hb : b = 0 := le_antisymm hba zero_le
    subst b
    simpa only [lift_self] using hu
  | add_one a ih =>
    by_cases h : b = a+1
    · subst b
      simpa only [lift_self] using hu
    · have hba' : b ≤ a := lt_add_one_iff.mp (lt_of_le_of_ne hba h)
      have haa : a ≤ Frame.top η := (le_of_lt (lt_add_one a)).trans ha
      rw [lift_add_one,if_neg h]
      exact valid_singleton η hη a (ih b hba' haa hu)
  | limit a haLim ih =>
    by_cases h : b = a
    · subst b
      simpa only [lift_self] using hu
    · have hblt : b < a := lt_of_le_of_ne hba h
      rw [lift_limit η hη a haLim ha b hblt,valid_limit η hη a haLim]
      let n := liftIndex η hη a haLim ha b hblt
      have hlow : lift η hη b (Frame.rho η a haLim n) u ∈ Valid η hη (Frame.rho η a haLim n) :=
        ih (Frame.rho η a haLim n) (Frame.rho_lt η a haLim n) b
          (liftIndex_spec η hη a haLim ha b hblt)
          ((Frame.rho_lt η a haLim n).le.trans ha) hu
      apply Or.inr
      refine ⟨_,rfl,?_⟩
      intro p hp
      have hp' := Finset.mem_singleton.mp hp
      subst p
      exact Or.inr (Or.inr ⟨_,hlow,rfl⟩)

theorem valid_tag (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) (ha : a ≤ Frame.top η) (n : ℕ) : tag η hη a n ∈ Valid η hη a := by
  apply valid_lift η hη 0 a zero_le ha
  rw [valid_zero]
  exact Or.inr (mem_range_self n)

end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.CosetConstructionTranslation
section


noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- A concrete realization of source codes by actual typed raw names.
Semantic quotients carry no assumed measurable structure. -/
structure SourceRealization (a : Ordinal.{0}) (E : CodedRelation) where
  value : E.Carrier → Ambient eta heta
  faithful : ∀ x y, E.rel x y ↔ value x = value y
  typed : a ≤ eta → ∀ x, value x ∈ Valid eta heta a

def SourceRealization.transport {a : Ordinal.{0}} {E F : CodedRelation} (h : E = F)
    (r : SourceRealization eta heta a E) : SourceRealization eta heta a F := h ▸ r

theorem SourceRealization.transport_value {a : Ordinal.{0}} {E F : CodedRelation} (h : E = F)
    (r : SourceRealization eta heta a E) (x : F.Carrier) :
    (r.transport eta heta h).value x =
      r.value (cast (congrArg CodedRelation.Carrier h.symm) x) := by
  cases h
  rfl

def bottomRealization : SourceRealization eta heta 0 cantorEquality where
  value := sourceAtom
  faithful := by
    intro x y
    change x = y ↔ sourceAtom x = sourceAtom y
    exact ⟨congrArg sourceAtom,fun h => sourceAtom_injective h⟩
  typed := by
    intro _ x
    rw [valid_zero]
    exact Or.inl (mem_range_self x)

theorem collection_none_ne_some (l : Frame.Layer eta) (f : ℕ → Ambient eta heta) :
    collection l none ≠ collection l (some f) := by
  intro h
  have hm : Member (f 0) (collection l (some f)) := by simp
  rw [← h] at hm
  exact member_collection_none l (f 0) hm

def successorRealization (a : Ordinal.{0}) (E : CodedRelation)
    (r : SourceRealization eta heta a E) :
    SourceRealization eta heta (a+1) (setJump E) where
  value := fun x => collection (level eta (a+1)) (x.map (fun u n => r.value (u n)))
  faithful := by
    intro x y
    cases x with
    | none =>
      cases y with
      | none => exact iff_of_true trivial rfl
      | some v =>
        change False ↔ collection _ none = collection _ (some (fun n => r.value (v n)))
        exact iff_of_false id (collection_none_ne_some eta heta _ _)
    | some u =>
      cases y with
      | none =>
        change False ↔ collection _ (some (fun n => r.value (u n))) = collection _ none
        exact iff_of_false id (Ne.symm (collection_none_ne_some eta heta _ _))
      | some v =>
        change ((∀ i, ∃ j, E.rel (u i) (v j)) ∧ (∀ j, ∃ i, E.rel (u i) (v j))) ↔ _
        simp only [Option.map_some]
        rw [collection_some_eq_iff]
        simp only [← r.faithful]
  typed := by
    intro ha x
    rw [valid_add_one]
    refine ⟨x.map (fun u n => r.value (u n)),rfl,?_⟩
    intro f hf i
    cases x with
    | none => simp at hf
    | some u =>
      cases hf
      exact r.typed ((show a ≤ a+1 from le_self_add).trans ha) (u i)

def limitRealization (a : Ordinal.{0}) (ha : IsSuccLimit a)
    (E : ℕ → CodedRelation)
    (r : ∀ n, SourceRealization eta heta (fundamentalSequence a ha n) (E n)) :
    SourceRealization eta heta a (countableProduct E) where
  value := fun x => sourceSequence (level eta a) (fun n => (r n).value (x n))
  faithful := by
    intro x y
    constructor
    · intro h
      apply congrArg (sourceSequence (level eta a))
      funext n
      exact ((r n).faithful (x n) (y n)).mp (h n)
    · intro h
      have hseq := sourceSequence_injective (level eta a) h
      intro n
      exact ((r n).faithful (x n) (y n)).mpr (congrFun hseq n)
  typed := by
    intro hle x
    rw [valid_limit eta heta a ha]
    left
    refine ⟨fun n => (r n).value (x n),rfl,?_⟩
    intro n
    change (r n).value (x n) ∈ Valid eta heta (Frame.q eta a ha n)
    simpa only [Frame.q_of_le_source eta a ha hle] using
      (r n).typed ((fundamentalSequence_lt a ha n).le.trans hle) (x n)

/-- Actual source-code translation, constructed through the fixed hierarchy's
successor and product-limit code spaces. -/
def sourceStage (a : Ordinal.{0}) : SourceRealization eta heta a (fsTower a) :=
  Ordinal.limitRecOn a
    ((bottomRealization eta heta).transport eta heta fsTower_zero.symm)
    (fun b r => (successorRealization eta heta b (fsTower b) r).transport eta heta
      (fsTower_add_one b).symm)
    (fun lam hlam rec =>
      (limitRealization eta heta lam hlam _
        (fun n => rec (fundamentalSequence lam hlam n) (fundamentalSequence_lt lam hlam n))).transport
          eta heta (fsTower_limit lam hlam).symm)

def translate (a : Ordinal.{0}) : (fsTower a).Carrier → Ambient eta heta :=
  (sourceStage eta heta a).value

theorem translate_eq_iff (a : Ordinal.{0}) (x y : (fsTower a).Carrier) :
    translate eta heta a x = translate eta heta a y ↔ (fsTower a).rel x y :=
  ((sourceStage eta heta a).faithful x y).symm

theorem translate_typed (a : Ordinal.{0}) (ha : a ≤ eta) (x : (fsTower a).Carrier) :
    translate eta heta a x ∈ Valid eta heta a := (sourceStage eta heta a).typed ha x

def successorCode (a : Ordinal.{0}) (x : (fsTower (a+1)).Carrier) :
    Option (ℕ → (fsTower a).Carrier) :=
  cast (congrArg CodedRelation.Carrier (fsTower_add_one a)) x

def limitCode (a : Ordinal.{0}) (ha : IsSuccLimit a) (x : (fsTower a).Carrier) :
    ∀ n, (fsTower (fundamentalSequence a ha n)).Carrier :=
  cast (congrArg CodedRelation.Carrier (fsTower_limit a ha)) x

theorem translate_add_one (a : Ordinal.{0}) (x : (fsTower (a+1)).Carrier) :
    translate eta heta (a+1) x = collection (level eta (a+1))
      ((successorCode a x).map (fun u n => translate eta heta a (u n))) := by
  unfold translate sourceStage
  rw [Ordinal.limitRecOn_add_one,SourceRealization.transport_value]
  rfl

theorem translate_limit (a : Ordinal.{0}) (ha : IsSuccLimit a) (x : (fsTower a).Carrier) :
    translate eta heta a x = sourceSequence (level eta a)
      (fun n => translate eta heta (fundamentalSequence a ha n) (limitCode a ha x n)) := by
  unfold translate sourceStage
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha,SourceRealization.transport_value]
  rfl

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.RawObjectsCountablePools
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

/-- Images of every finite subset of a specified pool. -/
def finiteImages {α β : Type} (f : Finset α → β) (H : Set α) : Set β :=
  range (fun A : Finset H => f (A.map (Function.Embedding.subtype _)))

theorem mem_finiteImages_iff {α β : Type} (f : Finset α → β) (H : Set α) (x : β) :
    x ∈ finiteImages f H ↔ ∃ A : Finset α, (∀ u ∈ A, u ∈ H) ∧ f A = x := by
  classical
  constructor
  · rintro ⟨A,rfl⟩
    exact ⟨_,fun _ hu => Finset.property_of_mem_map_subtype A hu,rfl⟩
  · rintro ⟨A,hA,hx⟩
    refine ⟨A.subtype (· ∈ H),?_⟩
    simpa only [Finset.subtype_map_of_mem hA] using hx

theorem finiteImages_countable {α β : Type} (f : Finset α → β) {H : Set α}
    (hH : H.Countable) : (finiteImages f H).Countable := by
  letI : Countable H := hH.to_subtype
  exact countable_range _

theorem newColumn_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))
    (hcount : ∀ b hb, (lower b hb).Countable) (n : ℕ) :
    {c | NewColumn η hη lam hlam lower n c}.Countable := by
  have heq : {c | NewColumn η hη lam hlam lower n c} =
      dataColumn η hη lam hlam n '' lower (Frame.q η lam hlam n) (Frame.q_lt η lam hlam n) ∪
      ({markerColumn η hη lam hlam n} ∪
        singleton (level η (Frame.delta η lam hlam n)) ''
          lower (Frame.rho η lam hlam n) (Frame.rho_lt η lam hlam n)) := by
    ext c
    simp only [NewColumn,mem_union,mem_image,mem_singleton_iff,mem_setOf_eq]
    aesop
  rw [heq]
  exact ((hcount _ _).image _).union ((countable_singleton _).union ((hcount _ _).image _))

theorem birthSet_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))
    (hcount : ∀ b hb, (lower b hb).Countable) :
    {p : ℕ × Ambient η hη | NewColumn η hη lam hlam lower p.1 p.2}.Countable := by
  have heq : {p : ℕ × Ambient η hη | NewColumn η hη lam hlam lower p.1 p.2} =
      ⋃ n, Prod.mk n '' {c | NewColumn η hη lam hlam lower n c} := by
    ext ⟨n,c⟩
    simp
  rw [heq]
  exact countable_iUnion (fun n => (newColumn_countable η hη lam hlam lower hcount n).image _)

/-- The source-seeded pools from the manuscript. The top source seed, when
desired, is included explicitly in `seeds` at the top layer. -/
def Pool (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0}) : Set (Ambient η hη) :=
  Ordinal.limitRecOn a (seeds 0 ∪ range extraAtom)
    (fun b H => seeds (b+1) ∪ finiteImages (finiteCollection (level η (b+1))) H)
    (fun lam hlam lower => seeds lam ∪ finiteImages (finiteFiller (level η lam))
      {p : ℕ × Ambient η hη | NewColumn η hη lam hlam lower p.1 p.2})

@[simp] theorem pool_zero (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) :
    Pool η hη seeds 0 = seeds 0 ∪ range extraAtom := by
  unfold Pool
  rw [Ordinal.limitRecOn_zero]

theorem pool_add_one (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0}) :
    Pool η hη seeds (a+1) =
      seeds (a+1) ∪ finiteImages (finiteCollection (level η (a+1))) (Pool η hη seeds a) := by
  unfold Pool
  rw [Ordinal.limitRecOn_add_one]

theorem pool_limit (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) :
    Pool η hη seeds lam = seeds lam ∪ finiteImages (finiteFiller (level η lam))
      {p : ℕ × Ambient η hη | NewColumn η hη lam hlam (fun b _ => Pool η hη seeds b) p.1 p.2} := by
  unfold Pool
  rw [Ordinal.limitRecOn_limit _ _ _ _ hlam]

theorem pool_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (hseeds : ∀ a, (seeds a).Countable) (a : Ordinal.{0}) : (Pool η hη seeds a).Countable := by
  induction a using Ordinal.limitRecOn with
  | zero => rw [pool_zero]; exact (hseeds 0).union (countable_range _)
  | add_one a ih => rw [pool_add_one]; exact (hseeds (a+1)).union (finiteImages_countable _ ih)
  | limit a ha ih =>
    rw [pool_limit η hη seeds a ha]
    exact (hseeds a).union (finiteImages_countable _ (birthSet_countable η hη a ha _ ih))

theorem pool_finiteCollection (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0})
    (A : Finset (Ambient η hη)) (hA : ∀ u ∈ A, u ∈ Pool η hη seeds a) :
    finiteCollection (level η (a+1)) A ∈ Pool η hη seeds (a+1) := by
  rw [pool_add_one]
  exact Or.inr ((mem_finiteImages_iff _ _ _).mpr ⟨A,hA,rfl⟩)

theorem pool_singleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0})
    {u : Ambient η hη} (hu : u ∈ Pool η hη seeds a) :
    singleton (level η (a+1)) u ∈ Pool η hη seeds (a+1) := by
  simpa only [finiteCollection_singleton] using
    pool_finiteCollection η hη seeds a {u} (by intro v hv; simpa only [Finset.mem_singleton.mp hv] using hu)

theorem pool_doubleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0})
    {u v : Ambient η hη} (hu : u ∈ Pool η hη seeds a) (hv : v ∈ Pool η hη seeds a) :
    doubleton (level η (a+1)) u v ∈ Pool η hη seeds (a+1) := by
  have hm := pool_finiteCollection η hη seeds a {u,v} (by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · exact h.symm ▸ hu
    · exact (Finset.mem_singleton.mp h).symm ▸ hv)
  simpa only [finiteCollection_doubleton] using hm

/-- Lift closure is built into the finite filler operations and needs no
closure assumption on the source seeds. -/
theorem pool_lift (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (b a : Ordinal.{0}) (hba : b ≤ a) (ha : a ≤ Frame.top η)
    {u : Ambient η hη} (hu : u ∈ Pool η hη seeds b) :
    lift η hη b a u ∈ Pool η hη seeds a := by
  induction a using Ordinal.limitRecOn generalizing b u with
  | zero =>
    have hb : b = 0 := le_antisymm hba zero_le
    subst b
    simpa only [lift_self] using hu
  | add_one a ih =>
    by_cases h : b = a+1
    · subst b
      simpa only [lift_self] using hu
    · have hba' : b ≤ a := lt_add_one_iff.mp (lt_of_le_of_ne hba h)
      have haa : a ≤ Frame.top η := (le_of_lt (lt_add_one a)).trans ha
      rw [lift_add_one,if_neg h]
      exact pool_singleton η hη seeds a (ih b hba' haa hu)
  | limit a haLim ih =>
    by_cases h : b = a
    · subst b
      simpa only [lift_self] using hu
    · have hblt : b < a := lt_of_le_of_ne hba h
      rw [lift_limit η hη a haLim ha b hblt,pool_limit η hη seeds a haLim]
      let n := liftIndex η hη a haLim ha b hblt
      have hlow : lift η hη b (Frame.rho η a haLim n) u ∈ Pool η hη seeds (Frame.rho η a haLim n) :=
        ih (Frame.rho η a haLim n) (Frame.rho_lt η a haLim n) b
          (liftIndex_spec η hη a haLim ha b hblt)
          ((Frame.rho_lt η a haLim n).le.trans ha) hu
      apply Or.inr
      apply (mem_finiteImages_iff _ _ _).mpr
      refine ⟨_,?_,rfl⟩
      intro p hp
      have hp' := Finset.mem_singleton.mp hp
      subst p
      exact Or.inr (Or.inr ⟨_,hlow,rfl⟩)

theorem pool_tag (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (a : Ordinal.{0}) (ha : a ≤ Frame.top η) (n : ℕ) : tag η hη a n ∈ Pool η hη seeds a := by
  apply pool_lift η hη seeds 0 a zero_le ha
  rw [pool_zero]
  exact Or.inr (mem_range_self n)

end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.CosetConstructionSourcePaths
section


noncomputable section
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

def codeCast {E F : CodedRelation} (h : E = F) : E.Carrier ≃ᵐ F.Carrier := by
  cases h
  exact MeasurableEquiv.refl _

theorem codeCast_apply {E F : CodedRelation} (h : E = F) (x : E.Carrier) :
    codeCast h x = cast (congrArg CodedRelation.Carrier h) x := by
  cases h
  rfl

def successorChildCode (a : Ordinal.{0}) (n : ℕ) (x : (fsTower (a+1)).Carrier) :
    Unit ⊕ (fsTower a).Carrier :=
  Sum.map id (fun u : ℕ → (fsTower a).Carrier => u n)
    (optionSumEquiv _ (codeCast (fsTower_add_one a) x))

theorem measurable_successorChildCode (a : Ordinal.{0}) (n : ℕ) :
    Measurable (successorChildCode a n) := by
  have hsum : @Measurable (setJump (fsTower a)).Carrier
      (Unit ⊕ (ℕ → (fsTower a).Carrier)) (setJump (fsTower a)).measurableSpace
      inferInstance (optionSumEquiv _) := by
    rw [setJump_measurableSpace_eq]
    exact comap_measurable _
  exact (measurable_id.sumMap (measurable_pi_apply n)).comp
    (hsum.comp (codeCast (fsTower_add_one a)).measurable)

def limitChildCode (a : Ordinal.{0}) (ha : IsSuccLimit a) (n : ℕ)
    (x : (fsTower a).Carrier) : Unit ⊕ (fsTower (fundamentalSequence a ha n)).Carrier :=
  .inr (codeCast (fsTower_limit a ha) x n)

theorem measurable_limitChildCode (a : Ordinal.{0}) (ha : IsSuccLimit a) (n : ℕ) :
    Measurable (limitChildCode a ha n) :=
  measurable_inr.comp ((measurable_pi_apply n).comp (codeCast (fsTower_limit a ha)).measurable)

structure CodeChildren (a : Ordinal.{0}) where
  rank : ℕ → Ordinal.{0}
  get : ∀ n, (fsTower a).Carrier → Unit ⊕ (fsTower (rank n)).Carrier
  measurable_get : ∀ n, Measurable (get n)
  rank_le : ∀ n, rank n ≤ a

def codeChildren (a : Ordinal.{0}) : CodeChildren a :=
  Ordinal.limitRecOn a
    ⟨fun _ => 0,fun _ _ => .inl (),fun _ => measurable_const,fun _ => le_rfl⟩
    (fun b _ => ⟨fun _ => b,successorChildCode b,measurable_successorChildCode b,
      fun _ => le_self_add⟩)
    (fun lam hlam _ => ⟨fundamentalSequence lam hlam,limitChildCode lam hlam,
      measurable_limitChildCode lam hlam,fun n => (fundamentalSequence_lt lam hlam n).le⟩)

structure PathCode (a : Ordinal.{0}) where
  rank : Ordinal.{0}
  get : (fsTower a).Carrier → Unit ⊕ (fsTower rank).Carrier
  measurable_get : Measurable get
  rank_le : rank ≤ a

/-- Paths are stored in reverse order so adding one last child is a list
constructor. All ranks depend only on the path, never on the input code. -/
def sourcePath (a : Ordinal.{0}) : List ℕ → PathCode a
  | [] => ⟨a,Sum.inr,measurable_inr,le_rfl⟩
  | n :: p =>
      let prev := sourcePath a p
      let child := codeChildren prev.rank
      ⟨child.rank n,Sum.elim (fun _ => .inl ()) (child.get n) ∘ prev.get,
        (measurable_const.sumElim (child.measurable_get n)).comp prev.measurable_get,
        (child.rank_le n).trans prev.rank_le⟩

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def optionalTranslate (a : Ordinal.{0}) (z : Unit ⊕ (fsTower a).Carrier) :
    Option (Ambient eta heta) :=
  match z with
  | .inl _ => none
  | .inr y => some (translate eta heta a y)

def sourcePathValue (p : List ℕ) (x : (fsTower eta).Carrier) : Option (Ambient eta heta) :=
  optionalTranslate eta heta (sourcePath eta p).rank ((sourcePath eta p).get x)

/-- The translated typed downward closure, with its concrete countable path
enumeration. Failed paths do not insert padding atoms into the source seed. -/
def sourceSeeds (a : Ordinal.{0}) (x : (fsTower eta).Carrier) : Set (Ambient eta heta) :=
  {u | ∃ p : List ℕ, (sourcePath eta p).rank = a ∧ sourcePathValue eta heta p x = some u}

theorem sourceSeeds_countable (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    (sourceSeeds eta heta a x).Countable := by
  apply (countable_range (fun p : List ℕ =>
    (sourcePathValue eta heta p x).getD (extraAtom 0))).mono
  rintro u ⟨p,_,hp⟩
  exact ⟨p,by simp only [hp,Option.getD_some]⟩

theorem sourceSeeds_typed (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    sourceSeeds eta heta a x ⊆ Valid eta heta a := by
  rintro u ⟨p,hrank,hp⟩
  unfold sourcePathValue optionalTranslate at hp
  split at hp
  · contradiction
  · rename_i y hy
    cases hp
    have hv := translate_typed eta heta (sourcePath eta p).rank (sourcePath eta p).rank_le y
    simpa only [hrank] using hv

theorem root_mem_sourceSeeds (x : (fsTower eta).Carrier) :
    translate eta heta eta x ∈ sourceSeeds eta heta eta x := ⟨[],rfl,rfl⟩

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionSourceClosure
section


noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def codeChildValue (a : Ordinal.{0}) (n : ℕ) (x : (fsTower a).Carrier) :
    Option (Ambient eta heta) :=
  optionalTranslate eta heta ((codeChildren a).rank n) ((codeChildren a).get n x)

theorem codeChildren_add_one_rank (a : Ordinal.{0}) (n : ℕ) :
    (codeChildren (a+1)).rank n = a := by
  unfold codeChildren
  rw [Ordinal.limitRecOn_add_one]

theorem codeChildren_limit_rank (a : Ordinal.{0}) (ha : IsSuccLimit a) (n : ℕ) :
    (codeChildren a).rank n = fundamentalSequence a ha n := by
  unfold codeChildren
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha]

theorem codeChildValue_add_one (a : Ordinal.{0}) (n : ℕ) (x : (fsTower (a+1)).Carrier) :
    codeChildValue eta heta (a+1) n x =
      (successorCode a x).map (fun u => translate eta heta a (u n)) := by
  unfold codeChildValue codeChildren
  rw [Ordinal.limitRecOn_add_one]
  unfold successorChildCode
  dsimp only
  rw [codeCast_apply]
  change optionalTranslate eta heta a
      (Sum.map id (fun u : ℕ → (fsTower a).Carrier => u n)
        (optionSumEquiv _ (successorCode a x))) = _
  cases successorCode a x <;> rfl

theorem codeChildValue_limit (a : Ordinal.{0}) (ha : IsSuccLimit a) (n : ℕ)
    (x : (fsTower a).Carrier) : codeChildValue eta heta a n x =
      some (translate eta heta (fundamentalSequence a ha n) (limitCode a ha x n)) := by
  unfold codeChildValue codeChildren
  rw [Ordinal.limitRecOn_limit _ _ _ _ ha]
  unfold limitChildCode
  dsimp only
  rw [codeCast_apply]
  rfl

theorem child_mem_sourceSeeds (p : List ℕ) (x : (fsTower eta).Carrier)
    (y : (fsTower (sourcePath eta p).rank).Carrier)
    (hy : (sourcePath eta p).get x = .inr y) (n : ℕ) (u : Ambient eta heta)
    (hu : codeChildValue eta heta (sourcePath eta p).rank n y = some u) :
    u ∈ sourceSeeds eta heta ((codeChildren (sourcePath eta p).rank).rank n) x := by
  refine ⟨n::p,rfl,?_⟩
  unfold sourcePathValue
  simp only [sourcePath,Function.comp_apply,hy,Sum.elim_inr]
  simpa only [codeChildValue] using hu

theorem successor_member_has_child (b a : Ordinal.{0}) (hb : b = a+1)
    (x : (fsTower b).Carrier) (u : Ambient eta heta)
    (hu : Member u (translate eta heta b x)) :
    ∃ n, codeChildValue eta heta b n x = some u ∧ (codeChildren b).rank n = a := by
  subst b
  rw [translate_add_one] at hu
  cases hv : successorCode a x with
  | none => simp only [hv,Option.map_none,member_collection_none] at hu
  | some v =>
    rw [hv] at hu
    obtain ⟨n,hn⟩ := (member_collection_some _ _ _).mp hu
    refine ⟨n,?_,codeChildren_add_one_rank a n⟩
    rw [codeChildValue_add_one,hv,Option.map_some]
    exact congrArg some hn

/-- Successor source seeds contain all members of each of their seeded sets. -/
theorem sourceSeeds_successor_downward (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    {v u : Ambient eta heta} (hv : v ∈ sourceSeeds eta heta (a+1) x) (hu : Member u v) :
    u ∈ sourceSeeds eta heta a x := by
  obtain ⟨p,hrank,hp⟩ := hv
  unfold sourcePathValue optionalTranslate at hp
  split at hp
  · contradiction
  · rename_i y hy
    cases hp
    obtain ⟨n,hchild,hrank'⟩ := successor_member_has_child eta heta
      (sourcePath eta p).rank a hrank y u hu
    have hm := child_mem_sourceSeeds eta heta p x y hy n u hchild
    rwa [hrank'] at hm

theorem sourceSeeds_successor_collection (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    {v : Ambient eta heta} (hv : v ∈ sourceSeeds eta heta (a+1) x) :
    ∃ z, v = collection (level eta (a+1)) z := by
  obtain ⟨p,hrank,hp⟩ := hv
  unfold sourcePathValue optionalTranslate at hp
  split at hp
  · contradiction
  · rename_i y hy
    cases hp
    have haux (b : Ordinal.{0}) (hb : b = a+1) (z : (fsTower b).Carrier) :
        ∃ u, translate eta heta b z = collection (level eta (a+1)) u := by
      subst b
      exact ⟨_,translate_add_one eta heta a z⟩
    exact haux _ hrank y

theorem sourceSeeds_rank_le (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    {u : Ambient eta heta} (hu : u ∈ sourceSeeds eta heta a x) : a ≤ eta := by
  obtain ⟨p,hp,_⟩ := hu
  exact hp ▸ (sourcePath eta p).rank_le

theorem sourceSeeds_empty_of_gt (a : Ordinal.{0}) (ha : eta < a) (x : (fsTower eta).Carrier) :
    sourceSeeds eta heta a x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact not_le_of_gt ha (sourceSeeds_rank_le eta heta a x hu)

theorem limit_value_children (b lam : Ordinal.{0}) (hb : b = lam) (hlam : IsSuccLimit lam)
    (x : (fsTower b).Carrier) :
    ∃ s : ℕ → Ambient eta heta, translate eta heta b x = sourceSequence (level eta lam) s ∧
      ∀ n, codeChildValue eta heta b n x = some (s n) ∧
        (codeChildren b).rank n = fundamentalSequence lam hlam n := by
  subst b
  refine ⟨fun n => translate eta heta (fundamentalSequence lam hlam n) (limitCode lam hlam x n),
    translate_limit eta heta lam hlam x,fun n => ?_⟩
  exact ⟨codeChildValue_limit eta heta lam hlam n x,codeChildren_limit_rank lam hlam n⟩

/-- Limit source seeds contain every one of their actual typed coordinates. -/
theorem sourceSeeds_limit_representation (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (x : (fsTower eta).Carrier) {v : Ambient eta heta} (hv : v ∈ sourceSeeds eta heta lam x) :
    ∃ s : ℕ → Ambient eta heta, v = sourceSequence (level eta lam) s ∧
      ∀ n, s n ∈ sourceSeeds eta heta (Frame.q eta lam hlam n) x := by
  have hle : lam ≤ eta := sourceSeeds_rank_le eta heta lam x hv
  obtain ⟨p,hrank,hp⟩ := hv
  unfold sourcePathValue optionalTranslate at hp
  split at hp
  · contradiction
  · rename_i y hy
    cases hp
    obtain ⟨s,hs,hchildren⟩ := limit_value_children eta heta (sourcePath eta p).rank lam hrank hlam y
    refine ⟨s,hs,fun n => ?_⟩
    have hm := child_mem_sourceSeeds eta heta p x y hy n (s n) (hchildren n).1
    have hq : Frame.q eta lam hlam n = fundamentalSequence lam hlam n :=
      congrFun (Frame.q_of_le_source eta lam hlam hle) n
    rw [(hchildren n).2] at hm
    rwa [hq]

theorem sourceSeeds_limit_downward (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (x : (fsTower eta).Carrier) :
    sourceSeeds eta heta lam x ⊆ LimitSet eta heta lam hlam
      (fun b _ => sourceSeeds eta heta b x) := by
  intro v hv
  obtain ⟨s,hs,hcoord⟩ := sourceSeeds_limit_representation eta heta lam hlam x hv
  exact Or.inl ⟨s,hs,hcoord⟩

theorem seed_subset_pool (seeds : Ordinal.{0} → Set (Ambient eta heta)) (a : Ordinal.{0}) :
    seeds a ⊆ Pool eta heta seeds a := by
  induction a using Ordinal.limitRecOn with
  | zero => rw [pool_zero]; exact subset_union_left
  | add_one a IH => rw [pool_add_one]; exact subset_union_left
  | limit a ha IH => rw [pool_limit eta heta seeds a ha]; exact subset_union_left

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionSeeds
section


noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def topCoordinates (x : (fsTower eta).Carrier) (n : ℕ) : Ambient eta heta :=
  if n = 0 then translate eta heta eta x else tag eta heta (eta+n) 4

def topSource (x : (fsTower eta).Carrier) : Ambient eta heta :=
  sourceSequence (level eta (Frame.top eta)) (topCoordinates eta heta x)

def fullSeeds (a : Ordinal.{0}) (x : (fsTower eta).Carrier) : Set (Ambient eta heta) :=
  if a = Frame.top eta then {topSource eta heta x} else sourceSeeds eta heta a x

theorem eta_add_nat_le_top (n : ℕ) : eta+n ≤ Frame.top eta :=
  (add_lt_add_iff_left eta).mpr (Ordinal.natCast_lt_omega0 n) |>.le

theorem topSource_typed (x : (fsTower eta).Carrier) :
    topSource eta heta x ∈ Valid eta heta (Frame.top eta) := by
  rw [valid_limit eta heta _ (Frame.top_isSuccLimit eta)]
  left
  refine ⟨topCoordinates eta heta x,rfl,fun n => ?_⟩
  change topCoordinates eta heta x n ∈ Valid eta heta
    (Frame.q eta (Frame.top eta) (Frame.top_isSuccLimit eta) n)
  rw [Frame.q_top]
  by_cases hn : n = 0
  · subst n
    simpa only [topCoordinates,if_pos rfl,Nat.cast_zero,add_zero] using
      translate_typed eta heta eta le_rfl x
  · rw [topCoordinates,if_neg hn]
    exact valid_tag eta heta (eta+n) (eta_add_nat_le_top eta n) 4

theorem sourceSeeds_subset_fullSeeds (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    sourceSeeds eta heta a x ⊆ fullSeeds eta heta a x := by
  by_cases ha : a = Frame.top eta
  · rw [ha,sourceSeeds_empty_of_gt eta heta _ (Frame.lt_top eta)]
    exact empty_subset _
  · simp only [fullSeeds,if_neg ha]
    exact Subset.rfl

theorem fullSeeds_countable (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    (fullSeeds eta heta a x).Countable := by
  by_cases ha : a = Frame.top eta
  · rw [fullSeeds,if_pos ha]
    exact countable_singleton _
  · rw [fullSeeds,if_neg ha]
    exact sourceSeeds_countable eta heta a x

theorem fullSeeds_typed (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    fullSeeds eta heta a x ⊆ Valid eta heta a := by
  by_cases ha : a = Frame.top eta
  · subst a
    intro u hu
    have heq : u = topSource eta heta x := by simpa only [fullSeeds,if_pos rfl,mem_singleton_iff] using hu
    rw [heq]
    exact topSource_typed eta heta x
  · rw [fullSeeds,if_neg ha]
    exact sourceSeeds_typed eta heta a x

theorem topCoordinates_mem_pool (x : (fsTower eta).Carrier) (n : ℕ) :
    topCoordinates eta heta x n ∈ Pool eta heta (fun a => fullSeeds eta heta a x) (eta+n) := by
  by_cases hn : n = 0
  · subst n
    simp only [topCoordinates,if_pos rfl,Nat.cast_zero,add_zero]
    apply seed_subset_pool eta heta _ eta
    exact sourceSeeds_subset_fullSeeds eta heta eta x (root_mem_sourceSeeds eta heta x)
  · rw [topCoordinates,if_neg hn]
    exact pool_tag eta heta _ (eta+n) (eta_add_nat_le_top eta n) 4

theorem successor_ne_top (a : Ordinal.{0}) : a+1 ≠ Frame.top eta := by
  intro h
  have hlt : a < Frame.top eta := by
    rw [← h]
    exact lt_add_of_pos_right a zero_lt_one
  have hsucc : a+1 < Frame.top eta := by
    simpa only [succ_eq_add_one] using (Frame.top_isSuccLimit eta).succ_lt hlt
  exact ne_of_lt hsucc h

theorem fullSeeds_successor_collection (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    {v : Ambient eta heta} (hv : v ∈ fullSeeds eta heta (a+1) x) :
    ∃ z, v = collection (level eta (a+1)) z := by
  rw [fullSeeds,if_neg (successor_ne_top eta a)] at hv
  exact sourceSeeds_successor_collection eta heta a x hv

theorem fullSeeds_successor_downward (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    {v u : Ambient eta heta} (hv : v ∈ fullSeeds eta heta (a+1) x) (hu : Member u v) :
    u ∈ Pool eta heta (fun b => fullSeeds eta heta b x) a := by
  rw [fullSeeds,if_neg (successor_ne_top eta a)] at hv
  apply seed_subset_pool eta heta _ a
  exact sourceSeeds_subset_fullSeeds eta heta a x (sourceSeeds_successor_downward eta heta a x hv hu)

theorem fullSeeds_limit_downward (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (x : (fsTower eta).Carrier) : fullSeeds eta heta lam x ⊆
      LimitSet eta heta lam hlam (fun b _ => Pool eta heta (fun a => fullSeeds eta heta a x) b) := by
  intro v hv
  by_cases htop : lam = Frame.top eta
  · subst lam
    have heq : v = topSource eta heta x := by simpa only [fullSeeds,if_pos rfl,mem_singleton_iff] using hv
    rw [heq]
    left
    refine ⟨topCoordinates eta heta x,rfl,fun n => ?_⟩
    change topCoordinates eta heta x n ∈ Pool eta heta _ (Frame.q eta (Frame.top eta) hlam n)
    simpa only [Frame.q_top] using topCoordinates_mem_pool eta heta x n
  · rw [fullSeeds,if_neg htop] at hv
    obtain ⟨s,hs,hcoord⟩ := sourceSeeds_limit_representation eta heta lam hlam x hv
    left
    refine ⟨s,hs,fun n => ?_⟩
    apply seed_subset_pool eta heta _ _
    exact sourceSeeds_subset_fullSeeds eta heta _ x (hcoord n)

theorem topSource_eq_iff (x y : (fsTower eta).Carrier) :
    topSource eta heta x = topSource eta heta y ↔ (fsTower eta).rel x y := by
  constructor
  · intro h
    have hseq := sourceSequence_injective (level eta (Frame.top eta)) h
    have hzero := congrFun hseq 0
    have htrans : translate eta heta eta x = translate eta heta eta y := by
      simpa only [topCoordinates,if_pos rfl] using hzero
    exact (translate_eq_iff eta heta eta x y).mp htrans
  · intro h
    apply congrArg (sourceSequence (level eta (Frame.top eta)))
    funext n
    by_cases hn : n = 0
    · simp only [topCoordinates,if_pos hn]
      exact (translate_eq_iff eta heta eta x y).mpr h
    · simp only [topCoordinates,if_neg hn]

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionSourceInvariant
section


noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- The actual typed semantic downward closure, independent of any source
enumeration or representatives of countable-set invariants. -/
inductive SourceClosure (root : Ambient eta heta) : Ordinal.{0} → Ambient eta heta → Prop
  | root : SourceClosure root eta root
  | member {a : Ordinal.{0}} {v u : Ambient eta heta} :
      SourceClosure root (a+1) v → Member u v → SourceClosure root a u
  | coordinate {lam : Ordinal.{0}} (hlam : IsSuccLimit lam) {v : Ambient eta heta}
      (s : ℕ → Ambient eta heta) : SourceClosure root lam v →
      v = sourceSequence (level eta lam) s → ∀ n,
        SourceClosure root (Frame.q eta lam hlam n) (s n)

theorem codeChildValue_zero (n : ℕ) (x : (fsTower 0).Carrier) :
    codeChildValue eta heta 0 n x = none := by
  unfold codeChildValue codeChildren
  rw [Ordinal.limitRecOn_zero]
  rfl

theorem child_step_closure (root : Ambient eta heta) (a : Ordinal.{0}) :
    ∀ ha : a ≤ eta, ∀ x : (fsTower a).Carrier,
      SourceClosure eta heta root a (translate eta heta a x) → ∀ n u,
      codeChildValue eta heta a n x = some u →
        SourceClosure eta heta root ((codeChildren a).rank n) u := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    intro ha x hroot n u hu
    rw [codeChildValue_zero] at hu
    contradiction
  | add_one a IH =>
    intro ha x hroot n u hu
    rw [codeChildren_add_one_rank]
    apply SourceClosure.member hroot
    rw [translate_add_one]
    cases hs : successorCode a x with
    | none =>
      rw [codeChildValue_add_one,hs] at hu
      contradiction
    | some f =>
      rw [codeChildValue_add_one,hs,Option.map_some] at hu
      exact (member_collection_some _ _ _).mpr ⟨n,Option.some.inj hu⟩
  | limit a ha IH =>
    intro hle x hroot n u hu
    rw [codeChildren_limit_rank a ha]
    rw [codeChildValue_limit eta heta a ha] at hu
    have heq := Option.some.inj hu
    have hc := SourceClosure.coordinate ha
      (fun k => translate eta heta (fundamentalSequence a ha k) (limitCode a ha x k))
      hroot (translate_limit eta heta a ha x) n
    have hq : Frame.q eta a ha n = fundamentalSequence a ha n :=
      congrFun (Frame.q_of_le_source eta a ha hle) n
    simpa only [hq,heq] using hc

theorem path_get_in_closure (p : List ℕ) : ∀ x : (fsTower eta).Carrier,
    ∀ y : (fsTower (sourcePath eta p).rank).Carrier,
      (sourcePath eta p).get x = .inr y →
        SourceClosure eta heta (translate eta heta eta x) (sourcePath eta p).rank
          (translate eta heta (sourcePath eta p).rank y) := by
  induction p with
  | nil =>
    intro x y hy
    cases hy
    exact SourceClosure.root
  | cons n p IH =>
    intro x y hy
    cases hp : (sourcePath eta p).get x with
    | inl z =>
      simp only [sourcePath,Function.comp_apply,hp,Sum.elim_inl] at hy
      contradiction
    | inr z =>
      have hprev := IH x z hp
      have hget : (codeChildren (sourcePath eta p).rank).get n z = .inr y := by
        simpa only [sourcePath,Function.comp_apply,hp,Sum.elim_inr] using hy
      apply child_step_closure eta heta _ _ (sourcePath eta p).rank_le z hprev n
      unfold codeChildValue
      rw [hget]
      rfl

theorem sourceSeeds_iff_closure (a : Ordinal.{0}) (x : (fsTower eta).Carrier)
    (u : Ambient eta heta) : u ∈ sourceSeeds eta heta a x ↔
      SourceClosure eta heta (translate eta heta eta x) a u := by
  constructor
  · rintro ⟨p,hrank,hp⟩
    unfold sourcePathValue optionalTranslate at hp
    split at hp
    · contradiction
    · rename_i y hy
      cases hp
      have hc := path_get_in_closure eta heta p x y hy
      exact Eq.mp (congrArg (fun b => SourceClosure eta heta (translate eta heta eta x) b
        (translate eta heta (sourcePath eta p).rank y)) hrank) hc
  · intro hc
    induction hc with
    | root => exact root_mem_sourceSeeds eta heta x
    | member hparent hmember IH => exact sourceSeeds_successor_downward eta heta _ x IH hmember
    | coordinate hlam s hparent heq n IH =>
      obtain ⟨t,ht,hcoord⟩ := sourceSeeds_limit_representation eta heta _ hlam x IH
      have hst : s = t := sourceSequence_injective _ (heq.symm.trans ht)
      rw [hst]
      exact hcoord n

/-- Equal source invariants generate literally the same typed source pools. -/
theorem sourceSeeds_congr (a : Ordinal.{0}) {x y : (fsTower eta).Carrier}
    (hxy : (fsTower eta).rel x y) : sourceSeeds eta heta a x = sourceSeeds eta heta a y := by
  have heq := (translate_eq_iff eta heta eta x y).mpr hxy
  ext u
  rw [sourceSeeds_iff_closure,sourceSeeds_iff_closure,heq]

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.RawObjectsColumns
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

theorem tag_ne (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) (ha : a ≤ Frame.top η) {n m : ℕ} (hnm : n ≠ m) :
    tag η hη a n ≠ tag η hη a m := fun h => hnm (tag_injective η hη a ha h)

theorem dataColumn_injective (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η) (n : ℕ) :
    Function.Injective (dataColumn η hη lam hlam n) := by
  have hs := (Frame.sigma_lt η lam hlam n).le.trans htop
  intro u v h
  apply lift_injective η hη (Frame.q η lam hlam n) (Frame.sigma η lam hlam n)
    (Frame.q_le_sigma η lam hlam n) hs
  exact Enc_injective _ _ _ _ (tag_ne η hη _ hs (by decide : (1 : ℕ) ≠ 3)) h

theorem dataColumn_ne_marker (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (u : Ambient η hη) :
    dataColumn η hη lam hlam n u ≠ markerColumn η hη lam hlam n := by
  have hs := (Frame.sigma_lt η lam hlam n).le.trans htop
  exact Enc_ne _ _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (1 : ℕ) ≠ 3))
    (tag_ne η hη _ hs (by decide : (1 : ℕ) ≠ 2))

theorem dataColumn_ne_singleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (u v : Ambient η hη) :
    dataColumn η hη lam hlam n u ≠ singleton (level η (Frame.delta η lam hlam n)) v := by
  have hs := (Frame.sigma_lt η lam hlam n).le.trans htop
  exact Enc_ne_singleton _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (1 : ℕ) ≠ 3))

theorem markerColumn_ne_singleton (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (v : Ambient η hη) :
    markerColumn η hη lam hlam n ≠ singleton (level η (Frame.delta η lam hlam n)) v := by
  have hs := (Frame.sigma_lt η lam hlam n).le.trans htop
  exact Enc_ne_singleton _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (2 : ℕ) ≠ 3))

def oldColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ) (c : Ambient η hη) : Ambient η hη :=
  Enc (level η (Frame.rho η lam hlam (n+1))) (level η (Frame.delta η lam hlam (n+1)))
    (tag η hη (Frame.sigma η lam hlam (n+1)) 0) (tag η hη (Frame.sigma η lam hlam (n+1)) 3)
    (lift η hη (Frame.delta η lam hlam n) (Frame.sigma η lam hlam (n+1)) c)

theorem oldColumn_injective (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η) (n : ℕ) :
    Function.Injective (oldColumn η hη lam hlam n) := by
  have hs := (Frame.sigma_lt η lam hlam (n+1)).le.trans htop
  intro u v h
  apply lift_injective η hη (Frame.delta η lam hlam n) (Frame.sigma η lam hlam (n+1))
    (Frame.delta_le_sigma_next η lam hlam n) hs
  exact Enc_injective _ _ _ _ (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 3)) h

theorem oldColumn_ne_new (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)) (n : ℕ)
    (c d : Ambient η hη) (hd : NewColumn η hη lam hlam lower (n+1) d) :
    oldColumn η hη lam hlam n c ≠ d := by
  have hs := (Frame.sigma_lt η lam hlam (n+1)).le.trans htop
  rcases hd with ⟨v,hv,rfl⟩ | rfl | ⟨v,hv,rfl⟩
  · exact Enc_ne _ _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 3))
      (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 1))
  · exact Enc_ne _ _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 3))
      (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 2))
  · exact Enc_ne_singleton _ _ _ _ _ _ (tag_ne η hη _ hs (by decide : (0 : ℕ) ≠ 3))

section Births
variable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))

def BirthData (n : ℕ) :=
  {v : Ambient η hη // v ∈ lower (Frame.q η lam hlam n) (Frame.q_lt η lam hlam n)} ⊕
    (Unit ⊕ {v : Ambient η hη // v ∈ lower (Frame.rho η lam hlam n) (Frame.rho_lt η lam hlam n)})

def encodeNew (n : ℕ) : BirthData η hη lam hlam lower n → Ambient η hη
  | Sum.inl v => dataColumn η hη lam hlam n v.val
  | Sum.inr (Sum.inl _) => markerColumn η hη lam hlam n
  | Sum.inr (Sum.inr v) => singleton (level η (Frame.delta η lam hlam n)) v.val

theorem encodeNew_mem (n : ℕ) (c : BirthData η hη lam hlam lower n) :
    NewColumn η hη lam hlam lower n (encodeNew η hη lam hlam lower n c) := by
  rcases c with v | ⟨⟨⟩⟩ | v
  · exact Or.inl ⟨v.val,v.property,rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨v.val,v.property,rfl⟩)

theorem encodeNew_surjective (n : ℕ) {c : Ambient η hη}
    (hc : NewColumn η hη lam hlam lower n c) :
    ∃ d, encodeNew η hη lam hlam lower n d = c := by
  rcases hc with ⟨v,hv,rfl⟩ | rfl | ⟨v,hv,rfl⟩
  · exact ⟨Sum.inl ⟨v,hv⟩,rfl⟩
  · exact ⟨Sum.inr (Sum.inl ()),rfl⟩
  · exact ⟨Sum.inr (Sum.inr ⟨v,hv⟩),rfl⟩

theorem encodeNew_injective (htop : lam ≤ Frame.top η) (n : ℕ) :
    Function.Injective (encodeNew η hη lam hlam lower n) := by
  intro c d h
  rcases c with v | ⟨⟨⟩⟩ | v <;> rcases d with w | ⟨⟨⟩⟩ | w
  · exact congrArg Sum.inl (Subtype.ext (dataColumn_injective η hη lam hlam htop n h))
  · exact False.elim (dataColumn_ne_marker η hη lam hlam htop n v.val h)
  · exact False.elim (dataColumn_ne_singleton η hη lam hlam htop n v.val w.val h)
  · exact False.elim (dataColumn_ne_marker η hη lam hlam htop n w.val h.symm)
  · rfl
  · exact False.elim (markerColumn_ne_singleton η hη lam hlam htop n w.val h)
  · exact False.elim (dataColumn_ne_singleton η hη lam hlam htop n w.val v.val h.symm)
  · exact False.elim (markerColumn_ne_singleton η hη lam hlam htop n v.val h.symm)
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext ((singleton_eq_iff _ _ _).mp h))

abbrev Birth := Σ n, BirthData η hη lam hlam lower n

def encodeBirth (b : Birth η hη lam hlam lower) : ℕ × Ambient η hη :=
  (b.1,encodeNew η hη lam hlam lower b.1 b.2)

theorem encodeBirth_injective (htop : lam ≤ Frame.top η) :
    Function.Injective (encodeBirth η hη lam hlam lower) := by
  rintro ⟨n,c⟩ ⟨m,d⟩ h
  have hnm : n = m := congrArg Prod.fst h
  subst m
  have hcd := encodeNew_injective η hη lam hlam lower htop n (congrArg Prod.snd h)
  exact congrArg (Sigma.mk n) hcd

end Births
end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.RawObjectsProfiles
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

section Profiles
variable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))

abbrev SourceTuple := ∀ n, {v : Ambient η hη //
  v ∈ lower (Frame.q η lam hlam n) (Frame.q_lt η lam hlam n)}

abbrev LimitRow := SourceTuple η hη lam hlam lower ⊕ Finset (Birth η hη lam hlam lower)

def birthEmbedding (htop : lam ≤ Frame.top η) : Birth η hη lam hlam lower ↪ ℕ × Ambient η hη :=
  ⟨encodeBirth η hη lam hlam lower,encodeBirth_injective η hη lam hlam lower htop⟩

def rowObject (htop : lam ≤ Frame.top η) : LimitRow η hη lam hlam lower → Ambient η hη
  | Sum.inl s => sourceSequence (level η lam) (fun n => (s n).val)
  | Sum.inr A => finiteFiller (level η lam) (A.map (birthEmbedding η hη lam hlam lower htop))

theorem rowObject_injective (htop : lam ≤ Frame.top η) :
    Function.Injective (rowObject η hη lam hlam lower htop) := by
  intro r s h
  rcases r with r | A <;> rcases s with s | B
  · apply congrArg Sum.inl
    have hcoord := sourceSequence_injective (level η lam) h
    funext n
    exact Subtype.ext (congrFun hcoord n)
  · exact False.elim (sourceSequence_ne_finiteFiller _ _ _ _ h)
  · exact False.elim (sourceSequence_ne_finiteFiller _ _ _ _ h.symm)
  · exact congrArg Sum.inr ((Finset.map_injective _)
      (finiteFiller_injective (level η lam) h))

theorem rowObject_mem_limitSet (htop : lam ≤ Frame.top η)
    (r : LimitRow η hη lam hlam lower) :
    rowObject η hη lam hlam lower htop r ∈ LimitSet η hη lam hlam lower := by
  rcases r with s | A
  · exact Or.inl ⟨_,rfl,fun n => (s n).property⟩
  · apply Or.inr
    refine ⟨_,rfl,?_⟩
    intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hp
    exact encodeNew_mem η hη lam hlam lower b.1 b.2

theorem exists_rowObject_of_mem_limitSet (htop : lam ≤ Frame.top η)
    {x : Ambient η hη} (hx : x ∈ LimitSet η hη lam hlam lower) :
    ∃ r, rowObject η hη lam hlam lower htop r = x := by
  classical
  rcases hx with ⟨s,rfl,hs⟩ | ⟨A,rfl,hA⟩
  · exact ⟨Sum.inl (fun n => ⟨s n,hs n⟩),rfl⟩
  · let f := birthEmbedding η hη lam hlam lower htop
    let B := A.preimage f f.injective.injOn
    have hmap : B.map f = A := by
      ext p
      constructor
      · intro hp
        obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hp
        exact Finset.mem_preimage.mp hb
      · intro hp
        obtain ⟨d,hd⟩ := encodeNew_surjective η hη lam hlam lower p.1 (hA p hp)
        let b : Birth η hη lam hlam lower := ⟨p.1,d⟩
        have he : f b = p := Prod.ext rfl hd
        apply Finset.mem_map.mpr
        refine ⟨b,Finset.mem_preimage.mpr ?_,he⟩
        simpa only [he] using hp
    exact ⟨Sum.inr B,congrArg (finiteFiller (level η lam)) hmap⟩

theorem range_rowObject (htop : lam ≤ Frame.top η) :
    range (rowObject η hη lam hlam lower htop) = LimitSet η hη lam hlam lower := by
  ext x
  exact ⟨fun ⟨r,hr⟩ => hr ▸ rowObject_mem_limitSet η hη lam hlam lower htop r,
    exists_rowObject_of_mem_limitSet η hη lam hlam lower htop⟩

def markerBirth (n : ℕ) : Birth η hη lam hlam lower := ⟨n,Sum.inr (Sum.inl ())⟩

def sourceBit (s : SourceTuple η hη lam hlam lower) : Birth η hη lam hlam lower → Bool
  | ⟨n,Sum.inl v⟩ => decide (s n = v)
  | ⟨_,Sum.inr (Sum.inl _)⟩ => true
  | ⟨_,Sum.inr (Sum.inr _)⟩ => false

def rowBit : LimitRow η hη lam hlam lower → Birth η hη lam hlam lower → Bool
  | Sum.inl s,b => sourceBit η hη lam hlam lower s b
  | Sum.inr A,b => decide (b ∈ A)

theorem source_bits_ne_filler (s : SourceTuple η hη lam hlam lower)
    (A : Finset (Birth η hη lam hlam lower)) :
    rowBit η hη lam hlam lower (Sum.inl s) ≠ rowBit η hη lam hlam lower (Sum.inr A) := by
  intro h
  let n := A.sup (fun b => b.1) + 1
  have hquery := congrFun h (markerBirth η hη lam hlam lower n)
  change true = decide (markerBirth η hη lam hlam lower n ∈ A) at hquery
  have hmem := of_decide_eq_true hquery.symm
  have hle : n ≤ A.sup (fun b => b.1) :=
    Finset.le_sup (f := fun b : Birth η hη lam hlam lower => b.1) hmem
  omega

theorem rowBit_injective : Function.Injective (rowBit η hη lam hlam lower) := by
  intro r s h
  rcases r with r | A <;> rcases s with s | B
  · apply congrArg Sum.inl
    funext n
    have hquery := congrFun h (⟨n,Sum.inl (r n)⟩ : Birth η hη lam hlam lower)
    have heq : s n = r n := by
      by_contra hne
      simp only [rowBit,sourceBit,decide_true,decide_eq_false hne] at hquery
      contradiction
    exact heq.symm
  · exact False.elim (source_bits_ne_filler η hη lam hlam lower r B h)
  · exact False.elim (source_bits_ne_filler η hη lam hlam lower s A h.symm)
  · apply congrArg Sum.inr
    ext b
    have hquery := congrFun h b
    by_cases ha : b ∈ A <;> by_cases hb : b ∈ B <;> simp_all [rowBit]

/-- A dedicated column name is its birth ancestor together with the assertion
that its birth precedes the current level. -/
def Column (n : ℕ) := {b : Birth η hη lam hlam lower // b.1 ≤ n}

def propagate (n : ℕ) : Column η hη lam hlam lower n → Column η hη lam hlam lower (n+1) :=
  fun c => ⟨c.val,Nat.le_succ_of_le c.property⟩

theorem propagate_injective (n : ℕ) : Function.Injective (propagate η hη lam hlam lower n) := by
  intro c d h
  exact Subtype.ext (congrArg (fun z : Column η hη lam hlam lower (n+1) => z.val) h)

def profile (n : ℕ) (r : LimitRow η hη lam hlam lower)
    (c : Column η hη lam hlam lower n) : Bool := rowBit η hη lam hlam lower r c.val

theorem profile_propagate (n : ℕ) (r : LimitRow η hη lam hlam lower)
    (c : Column η hη lam hlam lower n) :
    profile η hη lam hlam lower (n+1) r (propagate η hη lam hlam lower n c) =
      profile η hη lam hlam lower n r c := rfl

theorem fullProfile_injective :
    Function.Injective (fun r : LimitRow η hη lam hlam lower => fun n => profile η hη lam hlam lower n r) := by
  intro r s h
  apply rowBit_injective η hη lam hlam lower
  funext b
  exact congrFun (congrFun h b.1) ⟨b,le_rfl⟩

theorem profile_column_separating (n : ℕ) :
    Function.Injective (fun c : Column η hη lam hlam lower n =>
      fun r => profile η hη lam hlam lower n r c) := by
  intro c d h
  have hquery := congrFun h (Sum.inr {c.val})
  have hm : d.val ∈ ({c.val} : Finset (Birth η hη lam hlam lower)) := by
    by_contra hn
    simp only [profile,rowBit,Finset.mem_singleton,decide_true] at hquery
    simp only [Finset.mem_singleton] at hn
    simp only [decide_eq_false hn] at hquery
    contradiction
  exact Subtype.ext (Finset.mem_singleton.mp hm).symm

end Profiles
end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.RawObjectsPoolValidity
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

theorem valid_finiteCollection (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (a : Ordinal.{0}) (A : Finset (Ambient η hη))
    (hA : ∀ u ∈ A, u ∈ Valid η hη a) :
    finiteCollection (level η (a+1)) A ∈ Valid η hη (a+1) := by
  obtain ⟨x,hx⟩ := finiteCollection_is_collection (level η (a+1)) A
  rw [valid_add_one]
  refine ⟨x,hx,?_⟩
  intro f hf i
  have hm : Member (f i) (finiteCollection (level η (a+1)) A) := by
    rw [hx,hf]
    exact (member_collection_some _ _ _).mpr ⟨i,rfl⟩
  exact hA (f i) ((member_finiteCollection _ _ _).mp hm)

theorem newColumn_mono (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)}
    (h : ∀ b hb, lower b hb ⊆ upper b hb) (n : ℕ) {c : Ambient η hη}
    (hc : NewColumn η hη lam hlam lower n c) : NewColumn η hη lam hlam upper n c := by
  rcases hc with ⟨v,hv,rfl⟩ | rfl | ⟨v,hv,rfl⟩
  · exact Or.inl ⟨v,h _ _ hv,rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨v,h _ _ hv,rfl⟩)

theorem limitSet_mono (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)}
    (h : ∀ b hb, lower b hb ⊆ upper b hb) :
    LimitSet η hη lam hlam lower ⊆ LimitSet η hη lam hlam upper := by
  intro x hx
  rcases hx with ⟨s,rfl,hs⟩ | ⟨A,rfl,hA⟩
  · exact Or.inl ⟨s,rfl,fun n => h _ _ (hs n)⟩
  · exact Or.inr ⟨A,rfl,fun p hp => newColumn_mono η hη lam hlam h p.1 (hA p hp)⟩

theorem pool_subset_valid (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (hseeds : ∀ a, seeds a ⊆ Valid η hη a) (a : Ordinal.{0}) :
    Pool η hη seeds a ⊆ Valid η hη a := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    rw [pool_zero,valid_zero]
    exact union_subset (by simpa only [valid_zero] using hseeds 0) subset_union_right
  | add_one a ih =>
    rw [pool_add_one]
    intro x hx
    rcases hx with hs | hx
    · exact hseeds (a+1) hs
    · obtain ⟨A,hA,rfl⟩ := (mem_finiteImages_iff _ _ _).mp hx
      exact valid_finiteCollection η hη a A (fun u hu => ih (hA u hu))
  | limit a ha ih =>
    rw [pool_limit η hη seeds a ha]
    intro x hx
    rcases hx with hs | hx
    · exact hseeds a hs
    · obtain ⟨A,hA,rfl⟩ := (mem_finiteImages_iff _ _ _).mp hx
      rw [valid_limit η hη a ha]
      exact Or.inr ⟨A,rfl,fun p hp => newColumn_mono η hη a ha ih p.1 (hA p hp)⟩

def fullLower (η : Ordinal.{0}) (hη : η < Ordinal.omega 1) (lam : Ordinal.{0}) :
    ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη) := fun b _ => Valid η hη b

def ambientRow (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (x : Ambient η hη) (hx : x ∈ Valid η hη lam) :
    LimitRow η hη lam hlam (fullLower η hη lam) :=
  (exists_rowObject_of_mem_limitSet η hη lam hlam (fullLower η hη lam) htop (x := x)
    (by
      change x ∈ LimitSet η hη lam hlam (fun b _ => Valid η hη b)
      rwa [← valid_limit η hη lam hlam])).choose

theorem rowObject_ambientRow (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (x : Ambient η hη) (hx : x ∈ Valid η hη lam) :
    rowObject η hη lam hlam (fullLower η hη lam) htop (ambientRow η hη lam hlam htop x hx) = x :=
  (exists_rowObject_of_mem_limitSet η hη lam hlam (fullLower η hη lam) htop (x := x)
    (by
      change x ∈ LimitSet η hη lam hlam (fun b _ => Valid η hη b)
      rwa [← valid_limit η hη lam hlam])).choose_spec

def ambientProfile (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (x : Ambient η hη) (c : Column η hη lam hlam (fullLower η hη lam) n) : Bool :=
  if hx : x ∈ Valid η hη lam then
    profile η hη lam hlam (fullLower η hη lam) n (ambientRow η hη lam hlam htop x hx) c
  else false

theorem ambientProfile_propagate (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (x : Ambient η hη) (c : Column η hη lam hlam (fullLower η hη lam) n) :
    ambientProfile η hη lam hlam htop (n+1) x (propagate η hη lam hlam (fullLower η hη lam) n c) =
      ambientProfile η hη lam hlam htop n x c := by
  by_cases hx : x ∈ Valid η hη lam
  · simp only [ambientProfile,dif_pos hx,profile_propagate]
  · simp only [ambientProfile,dif_neg hx]

theorem ambientFullProfile_injOn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η) :
    InjOn (fun x : Ambient η hη => fun n => ambientProfile η hη lam hlam htop n x)
      (Valid η hη lam) := by
  intro x hx y hy h
  have hp : (fun n => profile η hη lam hlam (fullLower η hη lam) n
      (ambientRow η hη lam hlam htop x hx)) =
      (fun n => profile η hη lam hlam (fullLower η hη lam) n
      (ambientRow η hη lam hlam htop y hy)) := by
    funext n c
    have hquery := congrFun (congrFun h n) c
    simpa only [ambientProfile,dif_pos hx,dif_pos hy] using hquery
  have hr := fullProfile_injective η hη lam hlam (fullLower η hη lam) hp
  exact (rowObject_ambientRow η hη lam hlam htop x hx).symm.trans
    ((congrArg (rowObject η hη lam hlam (fullLower η hη lam) htop) hr).trans
      (rowObject_ambientRow η hη lam hlam htop y hy))

end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.RawObjectsTopRecovery
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

theorem all_markers_iff_source (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))
    (r : LimitRow η hη lam hlam lower) :
    (∀ n, rowBit η hη lam hlam lower r (markerBirth η hη lam hlam lower n) = true) ↔
      ∃ s, r = Sum.inl s := by
  constructor
  · intro h
    rcases r with s | A
    · exact ⟨s,rfl⟩
    · let n := A.sup (fun b => b.1) + 1
      have hn := h n
      change decide (markerBirth η hη lam hlam lower n ∈ A) = true at hn
      have hm := of_decide_eq_true hn
      have hb : n ≤ A.sup (fun b => b.1) :=
        Finset.le_sup (f := fun b : Birth η hη lam hlam lower => b.1) hm
      omega
  · rintro ⟨s,rfl⟩ n
    rfl

theorem ambientProfile_rowObject (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (r : LimitRow η hη lam hlam (fullLower η hη lam)) (n : ℕ)
    (c : Column η hη lam hlam (fullLower η hη lam) n) :
    ambientProfile η hη lam hlam htop n (rowObject η hη lam hlam (fullLower η hη lam) htop r) c =
      profile η hη lam hlam (fullLower η hη lam) n r c := by
  have hv : rowObject η hη lam hlam (fullLower η hη lam) htop r ∈ Valid η hη lam := by
    rw [valid_limit η hη lam hlam]
    exact rowObject_mem_limitSet η hη lam hlam (fullLower η hη lam) htop r
  have hr : ambientRow η hη lam hlam htop
      (rowObject η hη lam hlam (fullLower η hη lam) htop r) hv = r :=
    rowObject_injective η hη lam hlam (fullLower η hη lam) htop
      (rowObject_ambientRow η hη lam hlam htop _ hv)
  simp only [ambientProfile,dif_pos hv,hr]

theorem ambient_all_markers_iff_source (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (x : Ambient η hη) (hx : x ∈ Valid η hη lam) :
    (∀ n, ambientProfile η hη lam hlam htop n x
      ⟨markerBirth η hη lam hlam (fullLower η hη lam) n,le_rfl⟩ = true) ↔
      ∃ s : SourceTuple η hη lam hlam (fullLower η hη lam),
        x = sourceSequence (level η lam) (fun n => (s n).val) := by
  constructor
  · intro h
    have hm : ∀ n, rowBit η hη lam hlam (fullLower η hη lam)
        (ambientRow η hη lam hlam htop x hx)
        (markerBirth η hη lam hlam (fullLower η hη lam) n) = true := by
      intro n
      simpa only [ambientProfile,dif_pos hx,profile] using h n
    obtain ⟨s,hs⟩ := (all_markers_iff_source η hη lam hlam (fullLower η hη lam) _).mp hm
    refine ⟨s,?_⟩
    have he := rowObject_ambientRow η hη lam hlam htop x hx
    rw [hs] at he
    exact he.symm
  · rintro ⟨s,rfl⟩ n
    have h := ambientProfile_rowObject η hη lam hlam htop (Sum.inl s) n
      ⟨markerBirth η hη lam hlam (fullLower η hη lam) n,le_rfl⟩
    exact h

/-- At a limit pool with one source seed, the all-marker test identifies
that seed uniquely among all of its finite-support fillers. -/
theorem pool_unique_all_markers (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (hseeds : ∀ a, seeds a ⊆ Valid η hη a)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (s : ℕ → Ambient η hη) (hseed : seeds lam = {sourceSequence (level η lam) s})
    {x : Ambient η hη} (hx : x ∈ Pool η hη seeds lam)
    (hm : ∀ n, ambientProfile η hη lam hlam htop n x
      ⟨markerBirth η hη lam hlam (fullLower η hη lam) n,le_rfl⟩ = true) :
    x = sourceSequence (level η lam) s := by
  have hv := pool_subset_valid η hη seeds hseeds lam hx
  obtain ⟨t,ht⟩ := (ambient_all_markers_iff_source η hη lam hlam htop x hv).mp hm
  rw [pool_limit η hη seeds lam hlam] at hx
  rcases hx with hx | hx
  · simpa only [hseed,mem_singleton_iff] using hx
  · obtain ⟨A,hA,hx⟩ := (mem_finiteImages_iff _ _ _).mp hx
    exact False.elim (sourceSequence_ne_finiteFiller _ _ _ _ (ht.symm.trans hx.symm))

end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.CosetConstructionPoolInvariant
section


noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem fullSeeds_congr (a : Ordinal.{0}) {x y : (fsTower eta).Carrier}
    (hxy : (fsTower eta).rel x y) : fullSeeds eta heta a x = fullSeeds eta heta a y := by
  by_cases ha : a = Frame.top eta
  · simp only [fullSeeds,if_pos ha,(topSource_eq_iff eta heta x y).mpr hxy]
  · simp only [fullSeeds,if_neg ha,sourceSeeds_congr eta heta a hxy]

theorem pools_congr (a : Ordinal.{0}) {x y : (fsTower eta).Carrier}
    (hxy : (fsTower eta).rel x y) :
    Pool eta heta (fun b => fullSeeds eta heta b x) a =
      Pool eta heta (fun b => fullSeeds eta heta b y) a := by
  have hseed : (fun b => fullSeeds eta heta b x) = (fun b => fullSeeds eta heta b y) :=
    funext (fun b => fullSeeds_congr eta heta b hxy)
  rw [hseed]

theorem topCoordinates_typed (x : (fsTower eta).Carrier) (n : ℕ) :
    topCoordinates eta heta x n ∈ Valid eta heta
      (Frame.q eta (Frame.top eta) (Frame.top_isSuccLimit eta) n) := by
  rw [Frame.q_top]
  by_cases hn : n = 0
  · subst n
    simpa only [topCoordinates,if_pos rfl,Nat.cast_zero,add_zero] using
      translate_typed eta heta eta le_rfl x
  · rw [topCoordinates,if_neg hn]
    exact valid_tag eta heta (eta+n) (eta_add_nat_le_top eta n) 4

theorem topSource_all_markers (x : (fsTower eta).Carrier) :
    ∀ n, ambientProfile eta heta (Frame.top eta) (Frame.top_isSuccLimit eta) le_rfl n
      (topSource eta heta x)
      ⟨markerBirth eta heta (Frame.top eta) (Frame.top_isSuccLimit eta)
        (fullLower eta heta (Frame.top eta)) n,le_rfl⟩ = true := by
  apply (ambient_all_markers_iff_source eta heta _ _ le_rfl _ (topSource_typed eta heta x)).mpr
  exact ⟨fun n => ⟨topCoordinates eta heta x n,topCoordinates_typed eta heta x n⟩,rfl⟩

theorem topSource_mem_pool (x : (fsTower eta).Carrier) :
    topSource eta heta x ∈ Pool eta heta (fun b => fullSeeds eta heta b x) (Frame.top eta) := by
  apply seed_subset_pool eta heta _ _
  simp [fullSeeds]

/-- Equality of the actual top pools already reflects the entire source
invariant: their unique all-marker source rows must be equal. -/
theorem topPool_eq_iff (x y : (fsTower eta).Carrier) :
    Pool eta heta (fun b => fullSeeds eta heta b x) (Frame.top eta) =
      Pool eta heta (fun b => fullSeeds eta heta b y) (Frame.top eta) ↔ (fsTower eta).rel x y := by
  constructor
  · intro hpool
    have hx : topSource eta heta x ∈
        Pool eta heta (fun b => fullSeeds eta heta b y) (Frame.top eta) := by
      rw [← hpool]
      exact topSource_mem_pool eta heta x
    have heq := pool_unique_all_markers eta heta (fun b => fullSeeds eta heta b y)
      (fun a => fullSeeds_typed eta heta a y) (Frame.top eta) (Frame.top_isSuccLimit eta) le_rfl
      (topCoordinates eta heta y) (by simp [fullSeeds,topSource]) hx
      (topSource_all_markers eta heta x)
    exact (topSource_eq_iff eta heta x y).mp heq
  · exact pools_congr eta heta (Frame.top eta)

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.RawObjectsColumnEncoding
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects
section Encoding
variable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη))

def freshColumn (n : ℕ) (c : BirthData η hη lam hlam lower n) :
    Column η hη lam hlam lower n := ⟨⟨n,c⟩,le_rfl⟩

theorem column_succ_cases (n : ℕ) (c : Column η hη lam hlam lower (n+1)) :
    (∃ d, c = freshColumn η hη lam hlam lower (n+1) d) ∨
      (∃ d, c = propagate η hη lam hlam lower n d) := by
  rcases c with ⟨⟨k,c⟩,hk⟩
  change k ≤ n+1 at hk
  by_cases h : k = n+1
  · subst k
    exact Or.inl ⟨c,rfl⟩
  · exact Or.inr ⟨⟨⟨k,c⟩,by change k ≤ n; omega⟩,rfl⟩

/-- Encode a column by advancing its unique birth ancestor through the
actual P-family maps. -/
def encodeColumn : (n : ℕ) → Column η hη lam hlam lower n → Ambient η hη
  | 0,⟨⟨k,c⟩,hk⟩ => encodeNew η hη lam hlam lower 0 ((Nat.eq_zero_of_le_zero hk) ▸ c)
  | n+1,c => if h : c.val.1 = n+1 then encodeNew η hη lam hlam lower (n+1) (h ▸ c.val.2)
    else oldColumn η hη lam hlam n (encodeColumn n ⟨c.val,by have hc := c.property; omega⟩)

@[simp] theorem encodeColumn_fresh (n : ℕ) (c : BirthData η hη lam hlam lower n) :
    encodeColumn η hη lam hlam lower n (freshColumn η hη lam hlam lower n c) =
      encodeNew η hη lam hlam lower n c := by
  cases n <;> simp [encodeColumn,freshColumn]

@[simp] theorem encodeColumn_propagate (n : ℕ) (c : Column η hη lam hlam lower n) :
    encodeColumn η hη lam hlam lower (n+1) (propagate η hη lam hlam lower n c) =
      oldColumn η hη lam hlam n (encodeColumn η hη lam hlam lower n c) := by
  have h : c.val.1 ≠ n+1 := Nat.ne_of_lt (Nat.lt_succ_of_le c.property)
  simp only [encodeColumn,propagate,dif_neg h]
  apply congrArg (oldColumn η hη lam hlam n)
  apply congrArg (encodeColumn η hη lam hlam lower n)
  exact Subtype.ext rfl

theorem encodeColumn_injective (htop : lam ≤ Frame.top η) (n : ℕ) :
    Function.Injective (encodeColumn η hη lam hlam lower n) := by
  induction n with
  | zero =>
    rintro ⟨⟨k,c⟩,hk⟩ ⟨⟨j,d⟩,hj⟩ h
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst k
    subst j
    have hcd := encodeNew_injective η hη lam hlam lower htop 0 h
    exact congrArg (freshColumn η hη lam hlam lower 0) hcd
  | succ n ih =>
    intro c d h
    rcases column_succ_cases η hη lam hlam lower n c with ⟨c,rfl⟩ | ⟨c,rfl⟩ <;>
      rcases column_succ_cases η hη lam hlam lower n d with ⟨d,rfl⟩ | ⟨d,rfl⟩
    · rw [encodeColumn_fresh,encodeColumn_fresh] at h
      exact congrArg (freshColumn η hη lam hlam lower (n+1))
        (encodeNew_injective η hη lam hlam lower htop (n+1) h)
    · rw [encodeColumn_fresh,encodeColumn_propagate] at h
      exact False.elim (oldColumn_ne_new η hη lam hlam htop lower n _ _
        (encodeNew_mem η hη lam hlam lower (n+1) c) h.symm)
    · rw [encodeColumn_propagate,encodeColumn_fresh] at h
      exact False.elim (oldColumn_ne_new η hη lam hlam htop lower n _ _
        (encodeNew_mem η hη lam hlam lower (n+1) d) h)
    · rw [encodeColumn_propagate,encodeColumn_propagate] at h
      exact congrArg (propagate η hη lam hlam lower n)
        (ih (oldColumn_injective η hη lam hlam htop n h))

def ColumnSet (n : ℕ) : Set (Ambient η hη) := range (encodeColumn η hη lam hlam lower n)

theorem columnSet_zero : ColumnSet η hη lam hlam lower 0 =
    {c | NewColumn η hη lam hlam lower 0 c} := by
  ext c
  constructor
  · rintro ⟨⟨⟨k,d⟩,hk⟩,rfl⟩
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact encodeNew_mem η hη lam hlam lower 0 d
  · intro hc
    obtain ⟨d,rfl⟩ := encodeNew_surjective η hη lam hlam lower 0 hc
    exact ⟨freshColumn η hη lam hlam lower 0 d,encodeColumn_fresh η hη lam hlam lower 0 d⟩

theorem columnSet_succ (n : ℕ) : ColumnSet η hη lam hlam lower (n+1) =
    oldColumn η hη lam hlam n '' ColumnSet η hη lam hlam lower n ∪
      {c | NewColumn η hη lam hlam lower (n+1) c} := by
  ext c
  constructor
  · rintro ⟨d,rfl⟩
    rcases column_succ_cases η hη lam hlam lower n d with ⟨d,rfl⟩ | ⟨d,rfl⟩
    · exact Or.inr (by rw [encodeColumn_fresh]; exact encodeNew_mem η hη lam hlam lower (n+1) d)
    · exact Or.inl ⟨_,⟨d,rfl⟩,(encodeColumn_propagate η hη lam hlam lower n d).symm⟩
  · rintro (⟨d,⟨d,rfl⟩,rfl⟩ | hc)
    · exact ⟨propagate η hη lam hlam lower n d,encodeColumn_propagate η hη lam hlam lower n d⟩
    · obtain ⟨d,rfl⟩ := encodeNew_surjective η hη lam hlam lower (n+1) hc
      exact ⟨freshColumn η hη lam hlam lower (n+1) d,encodeColumn_fresh η hη lam hlam lower (n+1) d⟩

end Encoding
end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.RawObjectsPoolColumns
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

theorem pool_Enc (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0})
    {t b u : Ambient η hη} (ht : t ∈ Pool η hη seeds a)
    (hb : b ∈ Pool η hη seeds a) (hu : u ∈ Pool η hη seeds a) :
    Enc (level η (a+1)) (level η (a+2)) t b u ∈ Pool η hη seeds (a+2) ∧
      ∀ c, Member c (Enc (level η (a+1)) (level η (a+2)) t b u) →
        c ∈ Pool η hη seeds (a+1) := by
  have hs := pool_singleton η hη seeds a ht
  have hp := pool_doubleton η hη seeds a hb hu
  constructor
  · simpa only [add_assoc,one_add_one_eq_two] using
      pool_doubleton η hη seeds (a+1) hs hp
  · intro c hc
    rcases (Enc_member_iff _ _ _ _ _ _).mp hc with rfl | rfl
    · exact hs
    · exact hp

theorem pool_newColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) {c : Ambient η hη}
    (hc : NewColumn η hη lam hlam (fun b _ => Pool η hη seeds b) n c) :
    c ∈ Pool η hη seeds (Frame.delta η lam hlam n) ∧
      ∀ u, Member u c → u ∈ Pool η hη seeds (Frame.rho η lam hlam n) := by
  have hs := (Frame.sigma_lt η lam hlam n).le.trans htop
  have ht (m : ℕ) := pool_tag η hη seeds (Frame.sigma η lam hlam n) hs m
  rcases hc with ⟨v,hv,rfl⟩ | rfl | ⟨v,hv,rfl⟩
  · have hd := pool_lift η hη seeds (Frame.q η lam hlam n) (Frame.sigma η lam hlam n)
      (Frame.q_le_sigma η lam hlam n) hs hv
    exact pool_Enc η hη seeds (Frame.sigma η lam hlam n) (ht 1) (ht 3) hd
  · exact pool_Enc η hη seeds (Frame.sigma η lam hlam n) (ht 2) (ht 3) (ht 3)
  · constructor
    · simpa only [Frame.rho,Frame.delta,add_assoc,one_add_one_eq_two] using
        pool_singleton η hη seeds (Frame.rho η lam hlam n) hv
    · intro u hu
      exact ((member_singleton _ _ _).mp hu).symm ▸ hv

theorem pool_oldColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) {c : Ambient η hη} (hc : c ∈ Pool η hη seeds (Frame.delta η lam hlam n)) :
    oldColumn η hη lam hlam n c ∈ Pool η hη seeds (Frame.delta η lam hlam (n+1)) ∧
      ∀ u, Member u (oldColumn η hη lam hlam n c) →
        u ∈ Pool η hη seeds (Frame.rho η lam hlam (n+1)) := by
  have hs := (Frame.sigma_lt η lam hlam (n+1)).le.trans htop
  have ht (m : ℕ) := pool_tag η hη seeds (Frame.sigma η lam hlam (n+1)) hs m
  have hd := pool_lift η hη seeds (Frame.delta η lam hlam n) (Frame.sigma η lam hlam (n+1))
    (Frame.delta_le_sigma_next η lam hlam n) hs hc
  exact pool_Enc η hη seeds (Frame.sigma η lam hlam (n+1)) (ht 0) (ht 3) hd

/-- Every actual dedicated column belongs to its correct main pool and all
members of its set payload belong to the correct lower main pool. -/
theorem pool_encodeColumn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    (n : ℕ) (c : Column η hη lam hlam (fun b _ => Pool η hη seeds b) n) :
    encodeColumn η hη lam hlam (fun b _ => Pool η hη seeds b) n c ∈
        Pool η hη seeds (Frame.delta η lam hlam n) ∧
      ∀ u, Member u (encodeColumn η hη lam hlam (fun b _ => Pool η hη seeds b) n c) →
        u ∈ Pool η hη seeds (Frame.rho η lam hlam n) := by
  induction n with
  | zero =>
    rcases c with ⟨⟨k,d⟩,hk⟩
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact pool_newColumn η hη seeds lam hlam htop 0
      (encodeNew_mem η hη lam hlam _ 0 d)
  | succ n ih =>
    rcases column_succ_cases η hη lam hlam (fun b _ => Pool η hη seeds b) n c with ⟨d,rfl⟩ | ⟨d,rfl⟩
    · rw [encodeColumn_fresh]
      exact pool_newColumn η hη seeds lam hlam htop (n+1)
        (encodeNew_mem η hη lam hlam _ (n+1) d)
    · rw [encodeColumn_propagate]
      exact pool_oldColumn η hη seeds lam hlam htop n (ih d).1

theorem pool_columnSet_countable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (hseeds : ∀ a, (seeds a).Countable)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η) (n : ℕ) :
    (ColumnSet η hη lam hlam (fun b _ => Pool η hη seeds b) n).Countable := by
  apply (pool_countable η hη seeds hseeds (Frame.delta η lam hlam n)).mono
  rintro c ⟨d,rfl⟩
  exact (pool_encodeColumn η hη seeds lam hlam htop n d).1

end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.RawObjectsBirthAbsoluteness
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

section BirthAbsoluteness
variable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)}

theorem columnSet_mono (h : ∀ b hb, lower b hb ⊆ upper b hb) (n : ℕ) :
    ColumnSet η hη lam hlam lower n ⊆ ColumnSet η hη lam hlam upper n := by
  induction n with
  | zero =>
    rw [columnSet_zero,columnSet_zero]
    intro c hc
    exact newColumn_mono η hη lam hlam h 0 hc
  | succ n ih =>
    rw [columnSet_succ,columnSet_succ]
    apply union_subset_union
    · rintro c ⟨d,hd,rfl⟩
      exact ⟨d,ih hd,rfl⟩
    · intro c hc
      exact newColumn_mono η hη lam hlam h (n+1) hc

/-- Restricted columns have exactly the same birth status as their ambient
semantic names. No new ambient predecessor appears after restricting pools. -/
theorem newColumn_birth_absolute (htop : lam ≤ Frame.top η)
    (h : ∀ b hb, lower b hb ⊆ upper b hb) (n : ℕ) :
    {c | NewColumn η hη lam hlam lower n c} =
      ColumnSet η hη lam hlam lower n ∩ {c | NewColumn η hη lam hlam upper n c} := by
  ext c
  constructor
  · intro hc
    obtain ⟨d,hd⟩ := encodeNew_surjective η hη lam hlam lower n hc
    refine ⟨⟨freshColumn η hη lam hlam lower n d,?_⟩,
      newColumn_mono η hη lam hlam h n hc⟩
    exact (encodeColumn_fresh η hη lam hlam lower n d).trans hd
  · rintro ⟨hc,hnew⟩
    cases n with
    | zero => rwa [columnSet_zero] at hc
    | succ n =>
      rw [columnSet_succ] at hc
      rcases hc with ⟨d,hd,rfl⟩ | hc
      · exact False.elim (oldColumn_ne_new η hη lam hlam htop upper n d _ hnew rfl)
      · exact hc

/-- Even across different restricted pools, an actual column object has one
semantic birth ancestor. -/
theorem encoded_columns_same_birth (htop : lam ≤ Frame.top η) (n : ℕ)
    (c : Column η hη lam hlam lower n) (d : Column η hη lam hlam upper n)
    (h : encodeColumn η hη lam hlam lower n c = encodeColumn η hη lam hlam upper n d) :
    encodeBirth η hη lam hlam lower c.val = encodeBirth η hη lam hlam upper d.val := by
  induction n with
  | zero =>
    rcases c with ⟨⟨k,c⟩,hk⟩
    rcases d with ⟨⟨j,d⟩,hj⟩
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst k
    subst j
    exact Prod.ext rfl h
  | succ n ih =>
    rcases column_succ_cases η hη lam hlam lower n c with ⟨c,rfl⟩ | ⟨c,rfl⟩ <;>
      rcases column_succ_cases η hη lam hlam upper n d with ⟨d,rfl⟩ | ⟨d,rfl⟩
    · rw [encodeColumn_fresh,encodeColumn_fresh] at h
      exact Prod.ext rfl h
    · rw [encodeColumn_fresh,encodeColumn_propagate] at h
      exact False.elim (oldColumn_ne_new η hη lam hlam htop lower n _ _
        (encodeNew_mem η hη lam hlam lower (n+1) c) h.symm)
    · rw [encodeColumn_propagate,encodeColumn_fresh] at h
      exact False.elim (oldColumn_ne_new η hη lam hlam htop upper n _ _
        (encodeNew_mem η hη lam hlam upper (n+1) d) h)
    · rw [encodeColumn_propagate,encodeColumn_propagate] at h
      exact ih c d (oldColumn_injective η hη lam hlam htop n h)

end BirthAbsoluteness
end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.RawObjectsNaturality
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

section Naturality
variable (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)}
    (h : ∀ b hb, lower b hb ⊆ upper b hb)

def mapBirthData (n : ℕ) : BirthData η hη lam hlam lower n → BirthData η hη lam hlam upper n
  | Sum.inl v => Sum.inl ⟨v.val,h _ _ v.property⟩
  | Sum.inr (Sum.inl u) => Sum.inr (Sum.inl u)
  | Sum.inr (Sum.inr v) => Sum.inr (Sum.inr ⟨v.val,h _ _ v.property⟩)

theorem mapBirthData_injective (n : ℕ) :
    Function.Injective (mapBirthData η hη lam hlam h n) := by
  intro c d hc
  rcases c with v | ⟨u | v⟩ <;> rcases d with w | ⟨z | w⟩
  · apply congrArg Sum.inl
    apply Subtype.ext
    exact congrArg (fun t : {v : Ambient η hη // v ∈ upper (Frame.q η lam hlam n)
      (Frame.q_lt η lam hlam n)} => t.val) (Sum.inl.inj hc)
  · cases hc
  · cases hc
  · cases hc
  · exact congrArg (Sum.inr ∘ Sum.inl) (Sum.inl.inj (Sum.inr.inj hc))
  · have hc' := _root_.Sum.inr.inj hc; cases hc'
  · cases hc
  · have hc' := _root_.Sum.inr.inj hc; cases hc'
  · apply congrArg (Sum.inr ∘ Sum.inr)
    apply Subtype.ext
    exact congrArg (fun t : {v : Ambient η hη // v ∈ upper (Frame.rho η lam hlam n)
      (Frame.rho_lt η lam hlam n)} => t.val) (Sum.inr.inj (Sum.inr.inj hc))

def mapBirth : Birth η hη lam hlam lower ↪ Birth η hη lam hlam upper where
  toFun b := ⟨b.1,mapBirthData η hη lam hlam h b.1 b.2⟩
  inj' := by
    rintro ⟨n,c⟩ ⟨m,d⟩ heq
    have hnm : n=m := congrArg Sigma.fst heq
    subst m
    exact congrArg (Sigma.mk n) ((mapBirthData_injective η hη lam hlam h n)
      (eq_of_heq (Sigma.mk.inj_iff.mp heq).2))

def mapSourceTuple (s : SourceTuple η hη lam hlam lower) : SourceTuple η hη lam hlam upper :=
  fun n => ⟨(s n).val,h _ _ (s n).property⟩

def mapRow : LimitRow η hη lam hlam lower → LimitRow η hη lam hlam upper
  | Sum.inl s => Sum.inl (mapSourceTuple η hη lam hlam h s)
  | Sum.inr A => Sum.inr (A.map (mapBirth η hη lam hlam h))

def mapColumn (n : ℕ) (c : Column η hη lam hlam lower n) : Column η hη lam hlam upper n :=
  ⟨mapBirth η hη lam hlam h c.val,c.property⟩

@[simp] theorem encodeNew_map (n : ℕ) (c : BirthData η hη lam hlam lower n) :
    encodeNew η hη lam hlam upper n (mapBirthData η hη lam hlam h n c) =
      encodeNew η hη lam hlam lower n c := by
  rcases c with v | ⟨u | v⟩ <;> rfl

@[simp] theorem encodeBirth_map (b : Birth η hη lam hlam lower) :
    encodeBirth η hη lam hlam upper (mapBirth η hη lam hlam h b) =
      encodeBirth η hη lam hlam lower b := by
  rcases b with ⟨n,c⟩
  exact Prod.ext rfl (encodeNew_map η hη lam hlam h n c)

theorem mapColumn_fresh (n : ℕ) (c : BirthData η hη lam hlam lower n) :
    mapColumn η hη lam hlam h n (freshColumn η hη lam hlam lower n c) =
      freshColumn η hη lam hlam upper n (mapBirthData η hη lam hlam h n c) := rfl

theorem mapColumn_propagate (n : ℕ) (c : Column η hη lam hlam lower n) :
    mapColumn η hη lam hlam h (n+1) (propagate η hη lam hlam lower n c) =
      propagate η hη lam hlam upper n (mapColumn η hη lam hlam h n c) := rfl

@[simp] theorem encodeColumn_map (n : ℕ) (c : Column η hη lam hlam lower n) :
    encodeColumn η hη lam hlam upper n (mapColumn η hη lam hlam h n c) =
      encodeColumn η hη lam hlam lower n c := by
  induction n with
  | zero =>
    rcases c with ⟨⟨k,c⟩,hk⟩
    have hk0 : k=0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact encodeNew_map η hη lam hlam h 0 c
  | succ n ih =>
    rcases column_succ_cases η hη lam hlam lower n c with ⟨c,rfl⟩ | ⟨c,rfl⟩
    · rw [mapColumn_fresh,encodeColumn_fresh,encodeColumn_fresh,encodeNew_map]
    · rw [mapColumn_propagate,encodeColumn_propagate,encodeColumn_propagate,ih]

@[simp] theorem rowObject_map (htop : lam ≤ Frame.top η) (r : LimitRow η hη lam hlam lower) :
    rowObject η hη lam hlam upper htop (mapRow η hη lam hlam h r) =
      rowObject η hη lam hlam lower htop r := by
  rcases r with s | A
  · rfl
  · simp only [mapRow,rowObject,Finset.map_map]
    congr 1
    apply congrArg (fun f => A.map f)
    apply Function.Embedding.ext
    intro b
    exact encodeBirth_map η hη lam hlam h b

@[simp] theorem rowBit_map (r : LimitRow η hη lam hlam lower) (b : Birth η hη lam hlam lower) :
    rowBit η hη lam hlam upper (mapRow η hη lam hlam h r) (mapBirth η hη lam hlam h b) =
      rowBit η hη lam hlam lower r b := by
  rcases r with s | A
  · rcases b with ⟨n,v | ⟨u | v⟩⟩
    · change decide (_ = _) = decide (_ = _)
      apply decide_eq_decide.mpr
      simp only [Subtype.ext_iff,mapSourceTuple]
    · rfl
    · rfl
  · change decide (_ ∈ A.map _) = decide (b ∈ A)
    apply decide_eq_decide.mpr
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨c,hc,heq⟩
      exact (mapBirth η hη lam hlam h).injective heq ▸ hc
    · intro hb
      exact ⟨b,hb,rfl⟩

@[simp] theorem profile_map (n : ℕ) (r : LimitRow η hη lam hlam lower)
    (c : Column η hη lam hlam lower n) :
    profile η hη lam hlam upper n (mapRow η hη lam hlam h r) (mapColumn η hη lam hlam h n c) =
      profile η hη lam hlam lower n r c := rowBit_map η hη lam hlam h r c.val

end Naturality

/-- Profiles depend on the actual row and column semantic names, even when
the two countable pools and their subtype presentations differ. -/
theorem profile_semantic_congr (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)} (n : ℕ)
    (r : LimitRow η hη lam hlam lower) (s : LimitRow η hη lam hlam upper)
    (c : Column η hη lam hlam lower n) (d : Column η hη lam hlam upper n)
    (hrow : rowObject η hη lam hlam lower htop r = rowObject η hη lam hlam upper htop s)
    (hcol : encodeColumn η hη lam hlam lower n c = encodeColumn η hη lam hlam upper n d) :
    profile η hη lam hlam lower n r c = profile η hη lam hlam upper n s d := by
  let common : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη) :=
    fun b hb => lower b hb ∪ upper b hb
  have hleft : ∀ b hb, lower b hb ⊆ common b hb := fun _ _ => subset_union_left
  have hright : ∀ b hb, upper b hb ⊆ common b hb := fun _ _ => subset_union_right
  have hr : mapRow η hη lam hlam hleft r = mapRow η hη lam hlam hright s :=
    rowObject_injective η hη lam hlam common htop
      ((rowObject_map η hη lam hlam hleft htop r).trans
        (hrow.trans (rowObject_map η hη lam hlam hright htop s).symm))
  have hc : mapColumn η hη lam hlam hleft n c = mapColumn η hη lam hlam hright n d :=
    encodeColumn_injective η hη lam hlam common htop n
      ((encodeColumn_map η hη lam hlam hleft n c).trans
        (hcol.trans (encodeColumn_map η hη lam hlam hright n d).symm))
  calc
    profile η hη lam hlam lower n r c =
        profile η hη lam hlam common n (mapRow η hη lam hlam hleft r)
          (mapColumn η hη lam hlam hleft n c) := (profile_map η hη lam hlam hleft n r c).symm
    _ = profile η hη lam hlam common n (mapRow η hη lam hlam hright s)
          (mapColumn η hη lam hlam hright n d) := by rw [hr,hc]
    _ = profile η hη lam hlam upper n s d := profile_map η hη lam hlam hright n s d

theorem ambientProfile_restricted (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top η)
    {lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient η hη)}
    (h : ∀ b hb, lower b hb ⊆ fullLower η hη lam b hb)
    (n : ℕ) (r : LimitRow η hη lam hlam lower) (c : Column η hη lam hlam lower n) :
    ambientProfile η hη lam hlam htop n (rowObject η hη lam hlam lower htop r)
      (mapColumn η hη lam hlam h n c) = profile η hη lam hlam lower n r c := by
  have hx : rowObject η hη lam hlam lower htop r ∈ Valid η hη lam := by
    have hm := rowObject_mem_limitSet η hη lam hlam (fullLower η hη lam) htop
      (mapRow η hη lam hlam h r)
    rw [rowObject_map] at hm
    rwa [valid_limit η hη lam hlam] 
  have hr : ambientRow η hη lam hlam htop (rowObject η hη lam hlam lower htop r) hx =
      mapRow η hη lam hlam h r := by
    apply rowObject_injective η hη lam hlam (fullLower η hη lam) htop
    exact (rowObject_ambientRow η hη lam hlam htop _ hx).trans
      (rowObject_map η hη lam hlam h htop r).symm
  simp only [ambientProfile,dif_pos hx,hr]
  exact profile_map η hη lam hlam h n r c

end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.RawObjectsPoolRoles
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

theorem pool_infinite (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0}) :
    Infinite (Pool η hη seeds a) := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    let f (n : ℕ) : Pool η hη seeds 0 := ⟨extraAtom n,by rw [pool_zero]; exact Or.inr ⟨n,rfl⟩⟩
    exact Infinite.of_injective f (fun n m h => extraAtom_injective (congrArg Subtype.val h))
  | add_one a ih =>
    letI := ih
    let f (u : Pool η hη seeds a) : Pool η hη seeds (a+1) :=
      ⟨singleton (level η (a+1)) u.val,pool_singleton η hη seeds a u.property⟩
    apply Infinite.of_injective f
    intro u v h
    exact Subtype.ext ((singleton_eq_iff _ _ _).mp (congrArg Subtype.val h))
  | limit a ha ih =>
    let f (n : ℕ) : Pool η hη seeds a :=
      ⟨finiteFiller (level η a) {(n,markerColumn η hη a ha n)},by
        rw [pool_limit η hη seeds a ha]
        apply Or.inr
        apply (mem_finiteImages_iff _ _ _).mpr
        refine ⟨_,?_,rfl⟩
        intro p hp
        have hp' := Finset.mem_singleton.mp hp
        subst p
        exact Or.inr (Or.inl rfl)⟩
    apply Infinite.of_injective f
    intro n m h
    have hA := finiteFiller_injective (level η a) (congrArg Subtype.val h)
    exact congrArg Prod.fst (Finset.singleton_injective hA)

def ordinaryRaw {η : Ordinal.{0}} {hη : η < Ordinal.omega 1}
    (row col : Ambient η hη) : Bool := decide (Member col row)

theorem ordinary_role_injOn {η : Ordinal.{0}} {hη : η < Ordinal.omega 1}
    (l : Frame.Layer η) (P Q : Set (Ambient η hη))
    (hc : ∀ r ∈ P, ∃ x, r = collection l x)
    (hlower : ∀ r ∈ P, ∀ c, Member c r → c ∈ Q) :
    InjOn (fun r => fun c : Q => ordinaryRaw r c.val) P := by
  intro x hx y hy h
  obtain ⟨u,rfl⟩ := hc x hx
  obtain ⟨v,rfl⟩ := hc y hy
  apply collection_ext
  intro c
  by_cases hQ : c ∈ Q
  · have hquery := congrFun h (⟨c,hQ⟩ : Q)
    by_cases hcu : Member c (collection l u) <;> by_cases hcv : Member c (collection l v) <;>
      simp_all [ordinaryRaw]
  · have hcu : ¬ Member c (collection l u) := fun hm => hQ (hlower _ hx c hm)
    have hcv : ¬ Member c (collection l v) := fun hm => hQ (hlower _ hy c hm)
    simp only [hcu,hcv]

theorem pool_successor_collection (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη))
    (hseeds : ∀ a, seeds a ⊆ Valid η hη a) (a : Ordinal.{0})
    {x : Ambient η hη} (hx : x ∈ Pool η hη seeds (a+1)) :
    ∃ u, x = collection (level η (a+1)) u := by
  have ht := pool_subset_valid η hη seeds hseeds (a+1) hx
  rw [valid_add_one] at ht
  exact ⟨ht.choose,ht.choose_spec.1⟩

theorem pool_member_lower (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0})
    (hseed : ∀ x ∈ seeds (a+1), ∀ c, Member c x → c ∈ Pool η hη seeds a)
    {x c : Ambient η hη} (hx : x ∈ Pool η hη seeds (a+1)) (hcx : Member c x) :
    c ∈ Pool η hη seeds a := by
  rw [pool_add_one] at hx
  rcases hx with hs | hx
  · exact hseed x hs c hcx
  · obtain ⟨A,hA,rfl⟩ := (mem_finiteImages_iff _ _ _).mp hx
    exact hA c ((member_finiteCollection _ _ _).mp hcx)

/-- The exact common-lower-pool injectivity used in between-pool token recovery. -/
theorem ordinary_pool_union_injOn (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (X Y : Ordinal.{0} → Set (Ambient η hη))
    (hX : ∀ a, X a ⊆ Valid η hη a) (hY : ∀ a, Y a ⊆ Valid η hη a)
    (a : Ordinal.{0})
    (hdX : ∀ x ∈ X (a+1), ∀ c, Member c x → c ∈ Pool η hη X a)
    (hdY : ∀ x ∈ Y (a+1), ∀ c, Member c x → c ∈ Pool η hη Y a) :
    InjOn (fun r => fun c : (Pool η hη X a ∪ Pool η hη Y a : Set (Ambient η hη)) => ordinaryRaw r c.val)
      (Pool η hη X (a+1) ∪ Pool η hη Y (a+1)) := by
  apply ordinary_role_injOn (level η (a+1))
  · intro r hr
    rcases hr with hr | hr
    · exact pool_successor_collection η hη X hX a hr
    · exact pool_successor_collection η hη Y hY a hr
  · intro r hr c hcr
    rcases hr with hr | hr
    · exact Or.inl (pool_member_lower η hη X a hdX hr hcr)
    · exact Or.inr (pool_member_lower η hη Y a hdY hr hcr)

theorem ordinary_pool_column_separating (η : Ordinal.{0}) (hη : η < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient η hη)) (a : Ordinal.{0}) :
    Function.Injective (fun c : Pool η hη seeds a =>
      fun r : Pool η hη seeds (a+1) => ordinaryRaw r.val c.val) := by
  intro c d h
  let r : Pool η hη seeds (a+1) :=
    ⟨singleton (level η (a+1)) c.val,pool_singleton η hη seeds a c.property⟩
  have hquery := congrFun h r
  have heq : d.val = c.val := by
    by_contra hne
    simp only [ordinaryRaw,member_singleton] at hquery
    simp [r,hne] at hquery
  exact Subtype.ext heq.symm

end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.GenericTables
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology TopologicalSpace

namespace FSCofinality.GenericTables

/-- Both dimensions remain part of a finite Boolean matrix, including zero dimensions. -/
def BoolMatrix := Σ l : ℕ, Σ m : ℕ, Fin l → Fin m → Bool

instance : Countable BoolMatrix := by unfold BoolMatrix; infer_instance

abbrev Index := ℕ × BoolMatrix × ℕ × ℕ
abbrev Table := Index → Bool

structure Request where
  role : ℕ
  matrix : BoolMatrix
  side : Bool
  opposite : ℕ
  value : Bool

instance : Countable Request := by
  apply Function.Injective.countable (f := fun r : Request =>
    (r.role,r.matrix,r.side,r.opposite,r.value))
  intro r s h
  cases r
  cases s
  simpa only [Prod.mk.injEq,Request.mk.injEq] using h

def Request.key (r : Request) := (r.role,r.matrix,r.side,r.opposite)

/-- `false` varies the column label, `true` varies the row label. -/
def Request.index (r : Request) (z : ℕ) : Index :=
  if r.side then (r.role,r.matrix,r.opposite,z) else (r.role,r.matrix,z,r.opposite)

def Compatible (P : Finset Request) : Prop :=
  ∀ r ∈ P, ∀ s ∈ P, r.key = s.key → r.value = s.value

theorem Request.index_eq_of_key_eq {r s : Request} (h : r.key = s.key) (z : ℕ) :
    r.index z = s.index z := by
  cases r with | mk er mr sr or vr =>
    cases s with | mk es ms ss os vs =>
      simp only [Request.key,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl,rfl⟩
      rfl

theorem compatible_of_realization (A : Table) (P : Finset Request) (z : ℕ)
    (h : ∀ r ∈ P, A (r.index z) = r.value) : Compatible P := by
  intro r hr s hs hkey
  rw [← h r hr,← h s hs,Request.index_eq_of_key_eq hkey]

theorem index_eq_key {r s : Request} {z : ℕ}
    (hr : z ≠ r.opposite) (hs : z ≠ s.opposite)
    (h : r.index z = s.index z) : r.key = s.key := by
  cases r with | mk er mr sr or vr =>
    cases s with | mk es ms ss os vs =>
      cases sr <;> cases ss <;> simp_all [Request.index,Request.key]

def patternSet (P : Finset Request) (z : ℕ) : Set Table :=
  {A | ∀ r ∈ P, A (r.index z) = r.value}

theorem isOpen_patternSet (P : Finset Request) (z : ℕ) : IsOpen (patternSet P z) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [patternSet]
  | @insert r P hr IH =>
    have heq : patternSet (insert r P) z =
        {A | A (r.index z) = r.value} ∩ patternSet P z := by
      ext A
      simp [patternSet]
    rw [heq]
    exact ((isOpen_discrete ({r.value} : Set Bool)).preimage (continuous_apply _)).inter IH

def witnessSet (D : Set ℕ) (P : Finset Request) (N : ℕ) : Set Table :=
  {A | ∃ z ∈ D, N < z ∧ A ∈ patternSet P z}

theorem isOpen_witnessSet (D : Set ℕ) (P : Finset Request) (N : ℕ) :
    IsOpen (witnessSet D P N) := by
  classical
  have heq : witnessSet D P N = ⋃ z : ℕ,
      if z ∈ D ∧ N < z then patternSet P z else ∅ := by
    ext A
    simp only [witnessSet,mem_setOf_eq,mem_iUnion]
    constructor
    · rintro ⟨z,hz,hN,hA⟩
      exact ⟨z,by simpa [hz,hN] using hA⟩
    · rintro ⟨z,hz⟩
      by_cases h : z ∈ D ∧ N < z
      · exact ⟨z,h.1,h.2,by simpa [h] using hz⟩
      · simp [h] at hz
  rw [heq]
  apply isOpen_iUnion
  intro z
  split_ifs
  · exact isOpen_patternSet P z
  · exact isOpen_empty

def modify (A : Table) (P : Finset Request) (z : ℕ) : Table :=
  fun i => if h : ∃ r ∈ P, r.index z = i then (Classical.choose h).value else A i

theorem modify_pattern (A : Table) (P : Finset Request) (hP : Compatible P)
    (z : ℕ) (hz : ∀ r ∈ P, z ≠ r.opposite) : modify A P z ∈ patternSet P z := by
  intro r hr
  have hex : ∃ s ∈ P, s.index z = r.index z := ⟨r,hr,rfl⟩
  rw [modify,dif_pos hex]
  obtain ⟨hs,hindex⟩ := Classical.choose_spec hex
  exact hP _ hs r hr (index_eq_key (hz _ hs) (hz r hr) hindex)

theorem index_varying_label (r : Request) (z : ℕ) :
    z = (r.index z).2.2.1 ∨ z = (r.index z).2.2.2 := by
  cases h : r.side <;> simp [Request.index,h]

theorem dense_witnessSet (D : Set ℕ) (hD : D.Infinite)
    (P : Finset Request) (hP : Compatible P) (N : ℕ) : Dense (witnessSet D P N) := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨A,hA⟩ := hUne
  obtain ⟨I,V,hV,hsub⟩ := isOpen_pi_iff.mp hU A hA
  let bad := I.image (fun i : Index => i.2.2.1) ∪ I.image (fun i : Index => i.2.2.2) ∪
    P.image Request.opposite ∪ Finset.range (N+1)
  obtain ⟨z,hz,hfresh⟩ := hD.exists_notMem_finset bad
  have hzold (i : Index) (hi : i ∈ I) :
      z ≠ i.2.2.1 ∧ z ≠ i.2.2.2 := by
    constructor <;> intro h
    · apply hfresh
      simp only [bad,Finset.mem_union,Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl ⟨i,hi,h.symm⟩))
    · apply hfresh
      simp only [bad,Finset.mem_union,Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨i,hi,h.symm⟩))
  have hzreq (r : Request) (hr : r ∈ P) : z ≠ r.opposite := by
    intro h
    apply hfresh
    simp only [bad,Finset.mem_union,Finset.mem_image]
    exact Or.inl (Or.inr ⟨r,hr,h.symm⟩)
  have hN : N < z := by
    by_contra h
    have hh : z ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    exact hfresh (Finset.mem_union_right _ hh)
  have hsame (i : Index) (hi : i ∈ I) : modify A P z i = A i := by
    have hnone : ¬ ∃ r ∈ P, r.index z = i := by
      rintro ⟨r,hr,heq⟩
      have hv := index_varying_label r z
      rw [heq] at hv
      exact hv.elim (hzold i hi).1 (hzold i hi).2
    simp only [modify,dif_neg hnone]
  refine ⟨modify A P z,?_,z,hz,hN,modify_pattern A P hP z hzreq⟩
  apply hsub
  intro i hi
  rw [hsame i hi]
  exact (hV i hi).2

/-- One table simultaneously realizes all finite consistent requests, along
every member of a prescribed countable family of infinite label sets. -/
def GenericOn (D : ℕ → Set ℕ) (A : Table) : Prop :=
  ∀ P : Finset Request, Compatible P → ∀ i N : ℕ,
    ∃ z ∈ D i, N < z ∧ ∀ r ∈ P, A (r.index z) = r.value

theorem exists_generic (D : ℕ → Set ℕ) (hD : ∀ i, (D i).Infinite) :
    ∃ A : Table, GenericOn D A := by
  letI : PolishSpace Table := {
    toSecondCountableTopology := inferInstance
    toIsCompletelyMetrizableSpace := inferInstance }
  let Req := {P : Finset Request // Compatible P} × ℕ × ℕ
  have hd : Dense (⋂ q : Req, witnessSet (D q.2.1) q.1.val q.2.2) :=
    dense_iInter_of_isOpen (fun q => isOpen_witnessSet _ _ _)
      (fun q => dense_witnessSet _ (hD _) _ q.1.property _)
  obtain ⟨A,hA⟩ := hd.nonempty
  refine ⟨A,fun P hP i N => ?_⟩
  exact mem_iInter.mp hA (⟨P,hP⟩,i,N)

end FSCofinality.GenericTables

end
end

-- Original module: FSCofinalityProof.GenericTablesPointed
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.GenericTables

theorem compatible_pair {r s : Request} (hrs : r.key ≠ s.key) : Compatible {r,s} := by
  classical
  intro u hu v hv huv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · rfl
  · exact False.elim (hrs huv)
  · exact False.elim (hrs huv.symm)
  · rfl

theorem separates_rows {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A)
    (e : ℕ) (M M' : BoolMatrix) (k k' : ℕ) (hne : (M,k) ≠ (M',k')) :
    ∃ d, A (e,M,d,k) = false ∧ A (e,M',d,k') = true := by
  let r : Request := ⟨e,M,false,k,false⟩
  let s : Request := ⟨e,M',false,k',true⟩
  have hrs : r.key ≠ s.key := by
    intro h
    apply hne
    have hh : M = M' ∧ k = k' := by simpa [r,s,Request.key] using h
    exact Prod.ext hh.1 hh.2
  obtain ⟨d,_,_,hd⟩ := hA {r,s} (compatible_pair hrs) 0 0
  exact ⟨d,hd r (by simp),hd s (by simp)⟩

theorem row_signature_injective {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A) (e : ℕ) :
    Function.Injective (fun p : BoolMatrix × ℕ => fun d : ℕ => A (e,p.1,d,p.2)) := by
  intro p q h
  by_contra hne
  obtain ⟨d,hd,hd'⟩ := separates_rows hA e p.1 q.1 p.2 q.2 hne
  have hh := congrFun h d
  change A (e,p.1,d,p.2) = A (e,q.1,d,q.2) at hh
  rw [hd,hd'] at hh
  contradiction

def BoolMatrix.entry (M : BoolMatrix) (i j : ℕ) : Bool :=
  if hi : i < M.1 then if hj : j < M.2.1 then M.2.2 ⟨i,hi⟩ ⟨j,hj⟩ else false else false

/-- The finite raw-incidence matrix, retaining the tuple lengths. -/
def contextMatrix {V : Type*} (C : List (V → Bool)) (s : List V) : BoolMatrix :=
  ⟨C.length,s.length,fun i j => C[i] (s[j])⟩

theorem contextMatrix_length {V : Type*} (C : List (V → Bool)) (s : List V) :
    (contextMatrix C s).1 = C.length := rfl

theorem contextMatrix_entry {V : Type*} (C : List (V → Bool)) (s : List V)
    (i j : ℕ) (hi : i < C.length) (hj : j < s.length) :
    (contextMatrix C s).entry i j = C[i] s[j] := by
  simp [BoolMatrix.entry,contextMatrix,hi,hj]

theorem contextMatrix_entry_singleton {V : Type*} (C : List (V → Bool))
    (i : ℕ) (hi : i < C.length) (v : V) :
    (contextMatrix C [v]).entry i 0 = C[i] v := by
  simp [BoolMatrix.entry,contextMatrix,hi]

theorem contextMatrix_injective {V : Type*} (C C' : List (V → Bool))
    (h : ∀ s : List V, contextMatrix C s = contextMatrix C' s) : C = C' := by
  have hlen : C.length = C'.length := congrArg Sigma.fst (h [])
  apply List.ext_getElem hlen
  intro i hi hi'
  apply funext
  intro v
  have hh := congrArg (fun M : BoolMatrix => M.entry i 0) (h [v])
  simpa only [contextMatrix_entry_singleton C i hi v,
    contextMatrix_entry_singleton C' i hi' v] using hh

/-- Pointed-context injectivity: all finite lower contexts and natural copy
labels determine the ordered row-profile tuple and its row copy label. -/
theorem pointed_context_injective {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A)
    (e : ℕ) {V : Type*} :
    Function.Injective (fun p : List (V → Bool) × ℕ =>
      fun q : List V × ℕ => A (e,contextMatrix p.1 q.1,q.2,p.2)) := by
  intro p q hpq
  have hlocal (s : List V) : (contextMatrix p.1 s,p.2) = (contextMatrix q.1 s,q.2) := by
    apply row_signature_injective hA e
    funext d
    exact congrFun hpq (s,d)
  exact Prod.ext (contextMatrix_injective p.1 q.1 (fun s => congrArg Prod.fst (hlocal s)))
    (show p.2 = q.2 from congrArg (fun r : BoolMatrix × ℕ => r.2) (hlocal []))

end FSCofinality.GenericTables

end
end

-- Original module: FSCofinalityProof.GenericTablesHistories
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.GenericTables

/-- A full finite activation list and an eventually-zero natural sequence. -/
structure History where
  activation : List ℕ
  ordered : activation.Pairwise (· ≤ ·)
  noise : ℕ →₀ ℕ

instance : Countable History := by
  apply Function.Injective.countable (f := fun h : History => (h.activation,h.noise))
  intro h k heq
  cases h
  cases k
  simpa only [Prod.mk.injEq,History.mk.injEq] using heq

def FullHistory (l : ℕ) := {h : History // h.activation.length = l}

instance (l : ℕ) : Countable (FullHistory l) := inferInstanceAs (Countable {h : History // _})

def basicHistory (l k : ℕ) : FullHistory l :=
  ⟨⟨List.replicate l 0,by simp,Finsupp.single 0 k⟩,by simp⟩

theorem basicHistory_injective (l : ℕ) : Function.Injective (basicHistory l) := by
  intro k k' h
  have heq := congrArg (fun h : FullHistory l => h.val.noise 0) h
  simpa [basicHistory] using heq

instance (l : ℕ) : Infinite (FullHistory l) := Infinite.of_injective _ (basicHistory_injective l)

/-- Every natural full label denotes a legitimate history of the given length. -/
def fullLabelEquiv (l : ℕ) : FullHistory l ≃ ℕ := Classical.choice inferInstance

def History.fullLabel (h : History) : ℕ := fullLabelEquiv h.activation.length ⟨h,rfl⟩

def History.activeTimes (h : History) (n : ℕ) : List ℕ :=
  h.activation.filter (fun a => decide (a ≤ n))

def History.noisePrefix (h : History) (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (n+1) => h.noise i)

def History.localView (h : History) (n : ℕ) : List ℕ × List ℕ :=
  (h.activeTimes n,h.noisePrefix n)

def History.localCode (h : History) (n : ℕ) : ℕ := Encodable.encode (h.localView n)

theorem localCode_eq_iff (h k : History) (n : ℕ) :
    h.localCode n = k.localCode n ↔ h.localView n = k.localView n :=
  Encodable.encode_injective.eq_iff

theorem activeTimes_previous (h : History) (n : ℕ) :
    h.activeTimes n = (h.activeTimes (n+1)).filter (fun a => decide (a ≤ n)) := by
  simp only [History.activeTimes,List.filter_filter]
  congr 1
  funext a
  by_cases ha : a ≤ n
  · have hb : a ≤ n+1 := by omega
    simp [ha,hb]
  · simp [ha]

theorem noisePrefix_previous (h : History) (n : ℕ) :
    h.noisePrefix n = (h.noisePrefix (n+1)).take (n+1) := by
  apply List.ext_getElem
  · simp [History.noisePrefix]
  · intro i hi hi'
    simp only [History.noisePrefix,List.getElem_take,List.getElem_ofFn]

theorem localCode_refines (h k : History) (n : ℕ)
    (heq : h.localCode (n+1) = k.localCode (n+1)) : h.localCode n = k.localCode n := by
  apply (localCode_eq_iff h k n).mpr
  have hv := (localCode_eq_iff h k (n+1)).mp heq
  apply Prod.ext
  · change h.activeTimes n = k.activeTimes n
    have hh : h.activeTimes (n+1) = k.activeTimes (n+1) := congrArg Prod.fst hv
    rw [activeTimes_previous h n,activeTimes_previous k n,hh]
  · change h.noisePrefix n = k.noisePrefix n
    have hh : h.noisePrefix (n+1) = k.noisePrefix (n+1) := congrArg Prod.snd hv
    rw [noisePrefix_previous h n,noisePrefix_previous k n,hh]

/-- Future activation slots are invisible to a local view. -/
theorem activeTimes_append_late (h : History) (extra : List ℕ) (n : ℕ)
    (hlate : ∀ a ∈ extra, n < a) :
    (h.activation ++ extra).filter (fun a => decide (a ≤ n)) = h.activeTimes n := by
  rw [List.filter_append]
  have he : extra.filter (fun a => decide (a ≤ n)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    simpa only [decide_eq_true_eq] using not_le.mpr (hlate a ha)
  simp [he,History.activeTimes]

/-- Labels obtained by varying only the newest noise entry in a local code. -/
def localLabelSet (active pref : List ℕ) : Set ℕ :=
  range (fun k : ℕ => Encodable.encode (active,pref ++ [k]))

theorem infinite_localLabelSet (active pref : List ℕ) : (localLabelSet active pref).Infinite := by
  apply Set.infinite_range_of_injective
  intro k k' h
  have heq := Encodable.encode_injective h
  have hh : pref ++ [k] = pref ++ [k'] := congrArg Prod.snd heq
  simpa only [List.append_cancel_left_eq,List.cons.injEq,and_true] using hh

def History.bump (h : History) (M k : ℕ) : History :=
  ⟨h.activation,h.ordered,h.noise + Finsupp.single (M+1) k⟩

@[simp] theorem bump_activation (h : History) (M k : ℕ) :
    (h.bump M k).activation = h.activation := rfl

theorem bump_noise_prefix (h : History) (M k i : ℕ) (hi : i ≤ M) :
    (h.bump M k).noise i = h.noise i := by
  simp only [History.bump,Finsupp.add_apply]
  rw [Finsupp.single_eq_of_ne (by omega : i ≠ M+1),add_zero]

theorem bump_injective (h : History) (M : ℕ) : Function.Injective (h.bump M) := by
  intro k k' heq
  have hh := congrArg (fun g : History => g.noise (M+1)) heq
  simpa [History.bump] using hh

/-- Full labels with an entire activation list fixed and a noise prefix fixed. -/
def fullLabelSet (h : History) (M : ℕ) : Set ℕ :=
  {z | ∃ k : FullHistory h.activation.length,
    fullLabelEquiv _ k = z ∧ k.val.activation = h.activation ∧
      ∀ i ≤ M, k.val.noise i = h.noise i}

theorem infinite_fullLabelSet (h : History) (M : ℕ) : (fullLabelSet h M).Infinite := by
  let f : ℕ → ℕ := fun k => fullLabelEquiv h.activation.length ⟨h.bump M k,rfl⟩
  have hf : Function.Injective f := by
    intro k k' heq
    have hh := (fullLabelEquiv h.activation.length).injective heq
    exact bump_injective h M (congrArg Subtype.val hh)
  apply (Set.infinite_range_of_injective hf).mono
  rintro z ⟨k,rfl⟩
  exact ⟨⟨h.bump M k,rfl⟩,rfl,rfl,fun i hi => bump_noise_prefix h M k i hi⟩

theorem activeTimes_eq_self (h : History) (n : ℕ)
    (hn : ∀ a ∈ h.activation, a ≤ n) : h.activeTimes n = h.activation := by
  apply List.filter_eq_self.mpr
  intro a ha
  exact decide_eq_true (hn a ha)

/-- All local histories determine the actual entire finite activation
list and the eventually-zero noise sequence. -/
theorem all_localCodes_injective : Function.Injective (fun h : History => h.localCode) := by
  intro h k heq
  have hv (n : ℕ) : h.localView n = k.localView n :=
    (localCode_eq_iff h k n).mp (congrFun heq n)
  let N := h.activation.sum + k.activation.sum
  have hact : h.activation = k.activation := by
    have hh : h.activeTimes N = k.activeTimes N := congrArg Prod.fst (hv N)
    rw [activeTimes_eq_self h N (fun a ha => (List.le_sum_of_mem ha).trans (Nat.le_add_right _ _)),
      activeTimes_eq_self k N (fun a ha => (List.le_sum_of_mem ha).trans (Nat.le_add_left _ _))] at hh
    exact hh
  have hnoise : h.noise = k.noise := by
    ext i
    have hh := congrArg (fun p : List ℕ × List ℕ => p.2[i]?) (hv i)
    simpa only [History.localView,History.noisePrefix,List.getElem?_ofFn,
      dif_pos (Nat.lt_succ_self i),Option.some.injEq] using hh
  cases h
  cases k
  simp_all only [History.mk.injEq,true_and,and_self]

abbrev AllowedIndex := Unit ⊕ (List ℕ × List ℕ) ⊕ (History × ℕ)

def allowedSet : AllowedIndex → Set ℕ
  | .inl _ => univ
  | .inr (.inl (active,pref)) => localLabelSet active pref
  | .inr (.inr (h,M)) => fullLabelSet h M

theorem infinite_allowedSet (i : AllowedIndex) : (allowedSet i).Infinite := by
  rcases i with _ | (⟨active,pref⟩ | ⟨h,M⟩)
  · exact Set.infinite_univ
  · exact infinite_localLabelSet active pref
  · exact infinite_fullLabelSet h M

def allowedEnumeration : ℕ → AllowedIndex := Classical.choose (exists_surjective_nat AllowedIndex)

theorem allowedEnumeration_surjective : Function.Surjective allowedEnumeration :=
  Classical.choose_spec (exists_surjective_nat AllowedIndex)

def allowedSets (n : ℕ) : Set ℕ := allowedSet (allowedEnumeration n)

/-- A fixed actual family of independent Boolean tables meeting every local
history and full-history-tail requirement of the construction. -/
def genericTable : Table := Classical.choose (exists_generic allowedSets (fun i => infinite_allowedSet _))

theorem genericTable_generic : GenericOn allowedSets genericTable :=
  Classical.choose_spec (exists_generic allowedSets (fun i => infinite_allowedSet _))

theorem genericTable_realizes (P : Finset Request) (hP : Compatible P)
    (i : AllowedIndex) (N : ℕ) : ∃ z ∈ allowedSet i,
      N < z ∧ ∀ r ∈ P, genericTable (r.index z) = r.value := by
  obtain ⟨n,hn⟩ := allowedEnumeration_surjective i
  obtain ⟨z,hz,hN,hbits⟩ := genericTable_generic P hP n N
  exact ⟨z,by simpa only [allowedSets,hn] using hz,hN,hbits⟩

end FSCofinality.GenericTables

end
end

-- Original module: FSCofinalityProof.TokenStructures
section


noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

abbrev Token (U : Type*) := List U × ℕ

def history {U : Type*} (v : Token U) : FullHistory v.1.length :=
  (fullLabelEquiv v.1.length).symm v.2

def ofHistory {U : Type*} (t : List U) (h : FullHistory t.length) : Token U :=
  (t,fullLabelEquiv t.length h)

@[simp] theorem history_ofHistory {U : Type*} (t : List U) (h : FullHistory t.length) :
    history (ofHistory t h) = h := (fullLabelEquiv t.length).symm_apply_apply h

def activeLength {U : Type*} (v : Token U) (n : ℕ) : ℕ :=
  ((history v).val.activeTimes n).length

def activeTuple {U : Type*} (v : Token U) (n : ℕ) : List U := v.1.take (activeLength v n)

def localCode {U : Type*} (v : Token U) (n : ℕ) : ℕ := (history v).val.localCode n

theorem activeLength_mono {U : Type*} (v : Token U) (n : ℕ) :
    activeLength v n ≤ activeLength v (n+1) := by
  unfold activeLength
  rw [activeTimes_previous (history v).val n]
  exact List.length_filter_le _ _

theorem activeTuple_eq_full {U : Type*} (v : Token U) (n : ℕ)
    (hn : ∀ a ∈ (history v).val.activation, a ≤ n) : activeTuple v n = v.1 := by
  unfold activeTuple activeLength
  rw [activeTimes_eq_self _ _ hn,(history v).property,List.take_length]

def ordinaryEdge {U V : Type*} (A : Table) (e : ℕ) (R : U → V → Bool)
    (v : Token U) (w : Token V) : Bool :=
  A (e,contextMatrix (v.1.map R) w.1,w.2,v.2)

/-- A lower pool with every finite context present decodes ordinary tokens
exactly whenever the actual raw rows are distinct. -/
theorem ordinary_neighborhood_injective {U V : Type*} {D : ℕ → Set ℕ} {A : Table}
    (hA : GenericOn D A) (e : ℕ) (R : U → V → Bool) (hR : Function.Injective R) :
    Function.Injective (fun v : Token U => fun w : Token V => ordinaryEdge A e R v w) := by
  intro v w heq
  have h : (v.1.map R,v.2) = (w.1.map R,w.2) := by
    apply pointed_context_injective hA e
    exact heq
  apply Prod.ext
  · exact (List.map_injective_iff.mpr hR) (congrArg Prod.fst h)
  · exact congrArg (fun p : List (V → Bool) × ℕ => p.2) h

section Limit
variable {U : Type*} {Col : ℕ → Type*}
variable (profile : ∀ n, U → Col n → Bool)

def activeProfiles (v : Token U) (n : ℕ) : List (Col n → Bool) :=
  (activeTuple v n).map (profile n)

def R (n : ℕ) (v w : Token U) : Prop :=
  localCode v n = localCode w n ∧ activeProfiles profile v n = activeProfiles profile w n

theorem R_equivalence (n : ℕ) : Equivalence (R profile n) := by
  refine ⟨fun v => ⟨rfl,rfl⟩,fun h => ⟨h.1.symm,h.2.symm⟩,
    fun h h' => ⟨h.1.trans h'.1,h.2.trans h'.2⟩⟩

def branchEdge (A : Table) (e n : ℕ) (v : Token U) (w : Token (Col n)) : Bool :=
  A (e,contextMatrix (activeProfiles profile v n) w.1,w.2,localCode v n)

theorem R_iff_branch_neighborhood {D : ℕ → Set ℕ} {A : Table}
    (hA : GenericOn D A) (e n : ℕ) (v w : Token U) :
    R profile n v w ↔ ∀ c : Token (Col n),
      branchEdge profile A e n v c = branchEdge profile A e n w c := by
  constructor
  · rintro ⟨hl,hp⟩ c
    simp only [branchEdge,hl,hp]
  · intro h
    have heq : (activeProfiles profile v n,localCode v n) =
        (activeProfiles profile w n,localCode w n) := by
      apply pointed_context_injective hA e
      funext c
      exact h c
    exact ⟨congrArg Prod.snd heq,congrArg Prod.fst heq⟩

variable (j : ∀ n, Col n → Col (n+1))
variable (propagate : ∀ n u c, profile (n+1) u (j n c) = profile n u c)
include j propagate

theorem activeProfiles_previous (v : Token U) (n : ℕ) :
    activeProfiles profile v n =
      ((activeProfiles profile v (n+1)).map (fun f c => f (j n c))).take (activeLength v n) := by
  have hp : (fun u c => profile (n+1) u (j n c)) = profile n := by
    funext u c
    exact propagate n u c
  simp only [activeProfiles,activeTuple,List.map_take,List.map_map,Function.comp_def]
  rw [hp,List.take_take,Nat.min_eq_left (activeLength_mono v n)]

theorem R_refines (n : ℕ) {v w : Token U} (h : R profile (n+1) v w) : R profile n v w := by
  have hl : localCode v n = localCode w n :=
    localCode_refines (history v).val (history w).val n h.1
  have hlen : activeLength v n = activeLength w n := by
    have hh := (localCode_eq_iff (history v).val (history w).val n).mp hl
    exact congrArg (fun p : List ℕ × List ℕ => p.1.length) hh
  refine ⟨hl,?_⟩
  rw [activeProfiles_previous profile j propagate v n,
    activeProfiles_previous profile j propagate w n,h.2,hlen]

theorem profile_eq_of_later (u v : U) {m n : ℕ} (hmn : m ≤ n)
    (h : profile n u = profile n v) : profile m u = profile m v := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact h
  | succ n IH =>
    by_cases hm : m = n+1
    · rw [hm]
      exact h
    · apply IH (by omega)
      funext c
      have hh := congrFun h (j n c)
      simpa only [propagate] using hh

/-- Finite activation does not lose earlier profile information: propagation
recovers all levels before a slot's activation. -/
theorem all_R_separate (hinj : Function.Injective (fun u : U => fun n => profile n u))
    {v w : Token U} (h : ∀ n, R profile n v w) : v = w := by
  have hhist : (history v).val = (history w).val :=
    all_localCodes_injective (funext (fun n => (h n).1))
  let N := (history v).val.activation.sum + (history w).val.activation.sum
  have hfullv (n : ℕ) (hn : N ≤ n) : activeTuple v n = v.1 := by
    apply activeTuple_eq_full
    intro a ha
    exact (List.le_sum_of_mem ha).trans ((Nat.le_add_right _ _).trans hn)
  have hfullw (n : ℕ) (hn : N ≤ n) : activeTuple w n = w.1 := by
    apply activeTuple_eq_full
    intro a ha
    exact (List.le_sum_of_mem ha).trans ((Nat.le_add_left _ _).trans hn)
  have hp (n : ℕ) (hn : N ≤ n) : v.1.map (profile n) = w.1.map (profile n) := by
    simpa only [activeProfiles,hfullv n hn,hfullw n hn] using (h n).2
  have hlen : v.1.length = w.1.length := by
    have hh := congrArg List.length (hp N le_rfl)
    simpa only [List.length_map] using hh
  have htuple : v.1 = w.1 := by
    apply List.ext_getElem hlen
    intro i hi hi'
    apply hinj
    funext n
    let m := max N n
    apply profile_eq_of_later profile j propagate _ _ (show n ≤ m from le_max_right _ _)
    have hh := congrArg (fun t : List (Col m → Bool) => t[i]?) (hp m (le_max_left _ _))
    simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi',Option.map_some,Option.some.injEq] using hh
  apply Prod.ext htuple
  cases v with | mk tv kv =>
    cases w with | mk tw kw =>
      change tv = tw at htuple
      subst tw
      have hh : history (tv,kv) = history (tv,kw) := Subtype.ext hhist
      have hh' := congrArg (fullLabelEquiv tv.length) hh
      simpa only [history,Equiv.apply_symm_apply] using hh'

end Limit
end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenRecovery
section


noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

/-- A semantic name is the literal ambient tuple and the same full copy
label used in every incident decoding role. -/
def name {U : Type*} (P : Set U) (v : Token P) : Token U := (v.1.map Subtype.val,v.2)

theorem name_injective {U : Type*} (P : Set U) : Function.Injective (name P) := by
  intro v w h
  apply Prod.ext
  · exact (List.map_injective_iff.mpr Subtype.val_injective) (congrArg Prod.fst h)
  · exact congrArg (fun v : Token U => v.2) h

theorem list_eq_of_injOn {U V : Type*} (f : U → V) (S : Set U) (hf : S.InjOn f)
    (a b : List U) (ha : ∀ u ∈ a, u ∈ S) (hb : ∀ u ∈ b, u ∈ S)
    (h : a.map f = b.map f) : a = b := by
  have hlen : a.length = b.length := by
    simpa only [List.length_map] using congrArg List.length h
  apply List.ext_getElem hlen
  intro i hi hi'
  apply hf (ha a[i] (List.getElem_mem hi)) (hb b[i] (List.getElem_mem hi'))
  have hh := congrArg (fun l : List V => l[i]?) h
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi',Option.map_some,Option.some.injEq] using hh

/-- Shared-name successor recovery across two different raw pools. Only
the common lower pool is used as a query space; no Borel selection from
the ambient semantic quotient is involved. -/
theorem ordinary_recovery_between_pools {U V : Type*} {D : ℕ → Set ℕ} {A : Table}
    (hA : GenericOn D A) (e : ℕ) (PX PY : Set U) (Q : Set V) (raw : U → V → Bool)
    (hraw : (PX ∪ PY).InjOn (fun u => fun q : Q => raw u q.val))
    (v : Token PX) (w : Token PY)
    (hsignature : ∀ q : Token Q,
      ordinaryEdge A e (fun u : PX => fun q : Q => raw u.val q.val) v q =
        ordinaryEdge A e (fun u : PY => fun q : Q => raw u.val q.val) w q) :
    name PX v = name PY w := by
  have h : (v.1.map (fun u : PX => fun q : Q => raw u.val q.val),v.2) =
      (w.1.map (fun u : PY => fun q : Q => raw u.val q.val),w.2) := by
    apply pointed_context_injective hA e
    funext q
    exact hsignature q
  have hm : (name PX v).1.map (fun u => fun q : Q => raw u q.val) =
      (name PY w).1.map (fun u => fun q : Q => raw u q.val) := by
    simpa only [name,List.map_map,Function.comp_def] using congrArg Prod.fst h
  apply Prod.ext
  · apply list_eq_of_injOn _ _ hraw _ _ ?_ ?_ hm
    · intro u hu
      obtain ⟨u',_,rfl⟩ := List.mem_map.mp hu
      exact Or.inl u'.property
    · intro u hu
      obtain ⟨u',_,rfl⟩ := List.mem_map.mp hu
      exact Or.inr u'.property
  · exact congrArg (fun p : List (Q → Bool) × ℕ => p.2) h

/-- Every raw object appears in a singleton token. A bijection preserving
literal token names therefore identifies the entire two raw pools. -/
theorem pools_eq_of_named_bijection {U : Type*} (P Q : Set U)
    (f : Token P ≃ Token Q) (hname : ∀ v, name Q (f v) = name P v) : P = Q := by
  have hsubset : P ⊆ Q := by
    intro u hu
    let v : Token P := ([⟨u,hu⟩],0)
    have hh := congrArg Prod.fst (hname v)
    change (f v).1.map Subtype.val = [u] at hh
    have hmem : u ∈ (f v).1.map Subtype.val := by
      rw [hh]
      simp [name,v]
    obtain ⟨q,_,hq⟩ := List.mem_map.mp hmem
    simpa only [hq] using q.property
  have hreverse : Q ⊆ P := by
    intro u hu
    let w : Token Q := ([⟨u,hu⟩],0)
    have hh := congrArg Prod.fst (hname (f.symm w))
    rw [f.apply_symm_apply] at hh
    change [u] = (f.symm w).1.map Subtype.val at hh
    have hmem : u ∈ (f.symm w).1.map Subtype.val := by
      rw [← hh]
      simp [name,w]
    obtain ⟨p,_,hp⟩ := List.mem_map.mp hmem
    simpa only [hp] using p.property
  exact Set.Subset.antisymm hsubset hreverse

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.GenericTablesBottom
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology

namespace FSCofinality.GenericTables.Bottom

abbrev Cantor := ℕ → Bool
abbrev Pattern := ℕ × Finset (ℕ × List Bool)

def bitsPrefix (z : Cantor) (n : ℕ) : List Bool := List.ofFn (fun i : Fin n => z i)

theorem continuous_bitsPrefix (n : ℕ) : Continuous (fun z : Cantor => bitsPrefix z n) :=
  (continuous_of_discreteTopology : Continuous (List.ofFn : (Fin n → Bool) → List Bool)).comp
    (continuous_pi (fun i => continuous_apply (i : ℕ)))

def coordinatePattern (q : ℕ) : Pattern :=
  (Encodable.decode (α := Pattern) (Nat.unpair q).1).getD (0,∅)

@[simp] theorem coordinatePattern_pair (p : Pattern) (t : ℕ) :
    coordinatePattern (Nat.pair (Encodable.encode p) t) = p := by
  simp [coordinatePattern,Nat.unpair_pair]

/-- A continuous family of independent rows with arbitrary fixed finite prefixes. -/
def beta (fixed : ℕ → List Bool) (z : Cantor) (k : ℕ) : Cantor := fun q =>
  if hq : q < (fixed k).length then (fixed k)[q]
  else decide ((k,bitsPrefix z (coordinatePattern q).1) ∈ (coordinatePattern q).2)

theorem beta_prefix (fixed : ℕ → List Bool) (z : Cantor) (k i : ℕ)
    (hi : i < (fixed k).length) : beta fixed z k i = (fixed k)[i] := by
  simp [beta,hi]

theorem continuous_beta_fixed (fixed : ℕ → List Bool) (k : ℕ) :
    Continuous (fun z : Cantor => beta fixed z k) := by
  apply continuous_pi
  intro q
  by_cases hq : q < (fixed k).length
  · simp only [beta,dif_pos hq]
    exact continuous_const
  · simp only [beta,dif_neg hq]
    apply (continuous_of_discreteTopology : Continuous
      (fun s : List Bool => decide ((k,s) ∈ (coordinatePattern q).2))).comp
    exact continuous_bitsPrefix _

theorem continuous_beta (fixed : ℕ → List Bool) :
    Continuous (fun p : Cantor × ℕ => beta fixed p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hk : ∀ᶠ q : Cantor × ℕ in 𝓝 p, q.2 = p.2 :=
    (continuous_snd.tendsto p).eventually ((isOpen_discrete {p.2}).mem_nhds rfl)
  have hc : ContinuousAt (fun q : Cantor × ℕ => beta fixed q.1 p.2) p :=
    ((continuous_beta_fixed fixed p.2).comp continuous_fst).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [hk] with q hq
  rw [hq]

theorem exists_prefix_injective {ι : Type*} [Fintype ι] (p : ι → Cantor × ℕ)
    (hp : Function.Injective p) :
    ∃ n : ℕ, Function.Injective (fun i => ((p i).2,bitsPrefix (p i).1 n)) := by
  classical
  have hpair (i j : ι) : ∃ n : ℕ, ∀ m ≥ n,
      ((p i).2,bitsPrefix (p i).1 m) = ((p j).2,bitsPrefix (p j).1 m) → i = j := by
    by_cases hij : i = j
    · exact ⟨0,fun _ _ _ => hij⟩
    by_cases hk : (p i).2 = (p j).2
    · have hz : (p i).1 ≠ (p j).1 := by
        intro h
        exact hij (hp (Prod.ext h hk))
      have hex : ∃ r : ℕ, (p i).1 r ≠ (p j).1 r := by
        by_contra! h
        exact hz (funext h)
      obtain ⟨r,hr⟩ := hex
      refine ⟨r+1,fun m hm heq => ?_⟩
      have hh : bitsPrefix (p i).1 m = bitsPrefix (p j).1 m := congrArg Prod.snd heq
      have hpoint := congrFun (List.ofFn_injective hh) ⟨r,by omega⟩
      exact False.elim (hr hpoint)
    · exact ⟨0,fun _ _ heq => False.elim (hk (congrArg Prod.fst heq))⟩
  choose n hn using hpair
  let N : ℕ := Finset.univ.sup (fun ij : ι×ι => n ij.1 ij.2)
  refine ⟨N,fun i j heq => hn i j N ?_ heq⟩
  exact Finset.le_sup (f := fun ij : ι×ι => n ij.1 ij.2) (Finset.mem_univ (i,j))

/-- Every pattern on finitely many distinct rows occurs beyond every bound.
This supplies the finite independence used for new coordinate vertices. -/
theorem beta_finite_independence (fixed : ℕ → List Bool)
    {ι : Type*} [Fintype ι] (p : ι → Cantor × ℕ) (hp : Function.Injective p)
    (epsilon : ι → Bool) (N : ℕ) :
    ∃ q > N, ∀ i, beta fixed (p i).1 (p i).2 q = epsilon i := by
  classical
  obtain ⟨n,hn⟩ := exists_prefix_injective p hp
  let key : ι → ℕ × List Bool := fun i => ((p i).2,bitsPrefix (p i).1 n)
  let pos : Finset (ℕ × List Bool) :=
    (Finset.univ.filter (fun i => epsilon i = true)).image key
  have hpos (i : ι) : decide (key i ∈ pos) = epsilon i := by
    cases hi : epsilon i
    · apply decide_eq_false_iff_not.mpr
      rintro hh
      obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hh
      have heq : j = i := hn hji
      subst j
      have htrue : epsilon i = true := (Finset.mem_filter.mp hj).2
      rw [hi] at htrue
      contradiction
    · apply decide_eq_true
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  let L := Finset.univ.sup (fun i : ι => (fixed (p i).2).length)
  let q := Nat.pair (Encodable.encode (n,pos)) (N+L+1)
  have hq : N+L+1 ≤ q := Nat.right_le_pair _ _
  refine ⟨q,by omega,fun i => ?_⟩
  have hi : ¬ q < (fixed (p i).2).length := by
    have hl : (fixed (p i).2).length ≤ L :=
      Finset.le_sup (f := fun j : ι => (fixed (p j).2).length) (Finset.mem_univ i)
    omega
  simp only [beta,dif_neg hi,q,coordinatePattern_pair]
  exact hpos i

theorem beta_injective (fixed : ℕ → List Bool) :
    Function.Injective (fun p : Cantor × ℕ => beta fixed p.1 p.2) := by
  intro p q heq
  by_contra hpq
  let f : Bool → Cantor × ℕ := fun b => if b then q else p
  have hf : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp_all [f]
  obtain ⟨j,_,hj⟩ := beta_finite_independence fixed f hf id 0
  have h0 := hj false
  have h1 := hj true
  simp only [f,Bool.false_eq_true,if_false,if_true,id_eq] at h0 h1
  have h := congrFun heq j
  change beta fixed p.1 p.2 j = beta fixed q.1 q.2 j at h
  rw [h0,h1] at h
  contradiction

end FSCofinality.GenericTables.Bottom

end
end

-- Original module: FSCofinalityProof.GenericTablesBottomCoordination
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology

namespace FSCofinality.GenericTables.Bottom

abbrev ValidPattern := {P : Finset Request // Compatible P}

instance : Nonempty ValidPattern := ⟨⟨∅,by simp [Compatible]⟩⟩

def upperSolutions (P : ValidPattern) : Set ℕ :=
  {k | ∀ r ∈ P.val, genericTable (r.index k) = r.value}

theorem infinite_upperSolutions (P : ValidPattern) : (upperSolutions P).Infinite := by
  change ¬ (upperSolutions P).Finite
  intro hfin
  obtain ⟨N,hN⟩ := hfin.bddAbove
  obtain ⟨k,_,hk,hbits⟩ := genericTable_realizes P.val P.property (.inl ()) N
  exact not_lt_of_ge (hN hbits) hk

def patternEnumeration : ℕ → ValidPattern := Classical.choose (exists_surjective_nat ValidPattern)

theorem patternEnumeration_surjective : Function.Surjective patternEnumeration :=
  Classical.choose_spec (exists_surjective_nat ValidPattern)

def prefixTable : Table := Classical.choose
  (exists_generic (fun i => upperSolutions (patternEnumeration i))
    (fun i => infinite_upperSolutions _))

theorem prefixTable_generic : GenericOn
    (fun i => upperSolutions (patternEnumeration i)) prefixTable :=
  Classical.choose_spec (exists_generic (fun i => upperSolutions (patternEnumeration i))
    (fun i => infinite_upperSolutions _))

def zeroMatrix : BoolMatrix := ⟨0,0,fun i => Fin.elim0 i⟩

def fixedPrefix (k : ℕ) : List Bool :=
  List.ofFn (fun i : Fin k => prefixTable (0,zeroMatrix,i,k))

def bitRequest (s : List Bool) (i : Fin s.length) : Request :=
  ⟨0,zeroMatrix,true,i,s[i]⟩

def stringPattern (s : List Bool) : Finset Request := Finset.univ.image (bitRequest s)

theorem compatible_stringPattern (s : List Bool) : Compatible (stringPattern s) := by
  rintro r hr t ht hkey
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
  have hij : i = j := Fin.ext (by simpa [bitRequest,Request.key] using hkey)
  subst j
  rfl

theorem fixedPrefix_realizes (P : ValidPattern) (s : List Bool) (N : ℕ) :
    ∃ k > N, k ∈ upperSolutions P ∧ (fixedPrefix k).take s.length = s := by
  obtain ⟨i,hi⟩ := patternEnumeration_surjective P
  obtain ⟨k,hk,hN,hbits⟩ := prefixTable_generic (stringPattern s)
    (compatible_stringPattern s) i (max N s.length)
  refine ⟨k,lt_of_le_of_lt (le_max_left _ _) hN,?_,?_⟩
  · simpa only [hi] using hk
  · have hlen : s.length ≤ k := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
    apply List.ext_getElem
    · simp only [List.length_take,fixedPrefix,List.length_ofFn,Nat.min_eq_left hlen]
    · intro j hj hj'
      have hjk : j < k := lt_of_lt_of_le hj' hlen
      simp only [fixedPrefix,List.getElem_take,List.getElem_ofFn]
      have hb := hbits (bitRequest s ⟨j,hj'⟩)
        (Finset.mem_image.mpr ⟨⟨j,hj'⟩,Finset.mem_univ _,rfl⟩)
      exact hb

def coordinatedBeta (z : Cantor) (k : ℕ) : Cantor := beta fixedPrefix z k

theorem continuous_coordinatedBeta :
    Continuous (fun p : Cantor × ℕ => coordinatedBeta p.1 p.2) := continuous_beta _

theorem coordinatedBeta_injective :
    Function.Injective (fun p : Cantor × ℕ => coordinatedBeta p.1 p.2) := beta_injective _

theorem coordinatedBeta_finite_independence
    {ι : Type*} [Fintype ι] (p : ι → Cantor × ℕ) (hp : Function.Injective p)
    (epsilon : ι → Bool) (N : ℕ) :
    ∃ q > N, ∀ i, coordinatedBeta (p i).1 (p i).2 q = epsilon i :=
  beta_finite_independence _ p hp epsilon N

/-- The fixed raw context `z` is arbitrary. Every compatible upper pattern
and finite bottom bit pattern are realized by unboundedly many copy labels. -/
theorem upper_and_bottom_realization (z : Cantor) (P : ValidPattern)
    (s : List Bool) (N : ℕ) : ∃ k > N,
      k ∈ upperSolutions P ∧ bitsPrefix (coordinatedBeta z k) s.length = s := by
  obtain ⟨k,hk,hupper,hpref⟩ := fixedPrefix_realizes P s N
  refine ⟨k,hk,hupper,?_⟩
  have hlen : s.length ≤ (fixedPrefix k).length := by
    have hh := congrArg List.length hpref
    simp only [List.length_take] at hh
    omega
  apply List.ext_getElem
  · simp [bitsPrefix]
  · intro i hi hi'
    simp only [bitsPrefix,List.getElem_ofFn]
    have hh := congrArg (fun t : List Bool => t[i]?) hpref
    have hiK : i < (fixedPrefix k).length := lt_of_lt_of_le hi' hlen
    have hget : (fixedPrefix k)[i] = s[i] := by
      simpa only [List.getElem?_take,hi',if_true,List.getElem?_eq_getElem hiK,
        List.getElem?_eq_getElem hi',Option.some.injEq] using hh
    exact (beta_prefix fixedPrefix z k i hiK).trans hget

end FSCofinality.GenericTables.Bottom

end
end

-- Original module: FSCofinalityProof.HierarchySigma
section


noncomputable section
open Set MeasureTheory TopologicalSpace

namespace FSCofinality

/-- The coinduced measurable structure on a countable dependent sum is
standard Borel when every summand is standard Borel. -/
theorem standardBorel_sigma {X : ℕ → Type} [∀ n, MeasurableSpace (X n)]
    [∀ n, StandardBorelSpace (X n)] : StandardBorelSpace (Σ n, X n) := by
  choose t hb hp using (fun n => StandardBorelSpace.polish (α := X n))
  letI : ∀ n, TopologicalSpace (X n) := t
  letI : ∀ n, BorelSpace (X n) := hb
  letI : ∀ n, PolishSpace (X n) := hp
  have hB : (inferInstance : MeasurableSpace (Σ n, X n)) = borel (Σ n, X n) := by
    apply le_antisymm
    · intro s hs
      have hslice (n : ℕ) : MeasurableSet (Sigma.mk n ⁻¹' s) :=
        MeasurableSpace.measurableSet_iInf.mp hs n
      letI : MeasurableSpace (Σ n, X n) := borel (Σ n, X n)
      letI : BorelSpace (Σ n, X n) := ⟨rfl⟩
      have himage (n : ℕ) : MeasurableSet (Sigma.mk n '' (Sigma.mk n ⁻¹' s)) :=
        (Topology.IsOpenEmbedding.sigmaMk (i := n)).measurableEmbedding.measurableSet_image' (hslice n)
      have heq : s = ⋃ n, Sigma.mk n '' (Sigma.mk n ⁻¹' s) := by
        apply le_antisymm
        · rintro ⟨n,x⟩ hx
          exact mem_iUnion.mpr ⟨n,⟨x,hx,rfl⟩⟩
        · intro z hz
          obtain ⟨n,x,hx,rfl⟩ := mem_iUnion.mp hz
          exact hx
      rw [heq]
      exact MeasurableSet.iUnion himage
    · change MeasurableSpace.generateFrom {s : Set (Σ n, X n) | IsOpen s} ≤ _
      apply MeasurableSpace.generateFrom_le
      intro s hs
      apply MeasurableSpace.measurableSet_iInf.mpr
      intro n
      change MeasurableSet (Sigma.mk n ⁻¹' s)
      exact (hs.preimage (continuous_sigmaMk (i := n))).measurableSet
  letI : BorelSpace (Σ n, X n) := ⟨hB⟩
  letI : PolishSpace (Σ n, X n) :=
    { toSecondCountableTopology := inferInstance
      toIsCompletelyMetrizableSpace := inferInstance }
  infer_instance

end FSCofinality

end
end

-- Original module: FSCofinalityProof.GenericTablesBottomMap
section


noncomputable section
open Set MeasureTheory

namespace FSCofinality.GenericTables.Bottom

/-- Finite ordered contexts, with repetitions and the empty tuple allowed. -/
abbrev Context (V : Type*) := Σ l : ℕ, Fin l → V

variable {V : Type} [MeasurableSpace V] [StandardBorelSpace V]

instance contextStandardBorel : StandardBorelSpace (Context V) :=
  FSCofinality.standardBorel_sigma (X := fun l => Fin l → V)

def contextCode : Context V → Cantor := Classical.choose
  (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated (Context V))

theorem measurable_contextCode : Measurable (contextCode (V := V)) :=
  (Classical.choose_spec
    (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated (Context V))).1

theorem contextCode_injective : Function.Injective (contextCode (V := V)) :=
  (Classical.choose_spec
    (MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated (Context V))).2

def bottomMap (t : Context V) (k : ℕ) : Cantor := coordinatedBeta (contextCode t) k

theorem measurable_bottomMap :
    Measurable (fun p : Context V × ℕ => bottomMap p.1 p.2) :=
  continuous_coordinatedBeta.measurable.comp
    ((measurable_contextCode.comp measurable_fst).prodMk measurable_snd)

theorem bottomMap_injective :
    Function.Injective (fun p : Context V × ℕ => bottomMap p.1 p.2) := by
  intro p q heq
  have hh : (contextCode p.1,p.2) = (contextCode q.1,q.2) := coordinatedBeta_injective heq
  exact Prod.ext (contextCode_injective (congrArg (fun r : Cantor × ℕ => r.1) hh))
    (congrArg (fun r : Cantor × ℕ => r.2) hh)

theorem measurableEmbedding_bottomMap :
    MeasurableEmbedding (fun p : Context V × ℕ => bottomMap p.1 p.2) :=
  measurable_bottomMap.measurableEmbedding bottomMap_injective

theorem bottomMap_finite_independence {ι : Type*} [Fintype ι]
    (p : ι → Context V × ℕ) (hp : Function.Injective p) (epsilon : ι → Bool) (N : ℕ) :
    ∃ q > N, ∀ i, bottomMap (p i).1 (p i).2 q = epsilon i := by
  apply coordinatedBeta_finite_independence
    (fun i => (contextCode (p i).1,(p i).2)) ?_ epsilon N
  intro i j hij
  apply hp
  exact Prod.ext (contextCode_injective (congrArg (fun r : Cantor × ℕ => r.1) hij))
    (congrArg (fun r : Cantor × ℕ => r.2) hij)

/-- The full bottom-coordination lemma, uniform in a fixed raw context. -/
theorem bottomMap_realization (t : Context V) (P : ValidPattern) (s : List Bool) (N : ℕ) :
    ∃ k > N, k ∈ upperSolutions P ∧ bitsPrefix (bottomMap t k) s.length = s :=
  upper_and_bottom_realization (contextCode t) P s N

end FSCofinality.GenericTables.Bottom

end
end

-- Original module: FSCofinalityProof.TokenBottomRecovery
section


noncomputable section

namespace FSCofinality.Tokens
open GenericTables

def contextOfList {U : Type*} (t : List U) : Bottom.Context U := ⟨t.length,fun i => t[i]⟩

theorem contextOfList_injective {U : Type*} : Function.Injective (contextOfList (U := U)) := by
  intro s t h
  have hh := congrArg (fun c : Bottom.Context U => List.ofFn c.2) h
  change List.ofFn s.get = List.ofFn t.get at hh
  simpa only [List.ofFn_get] using hh

variable {U : Type} [MeasurableSpace U] [StandardBorelSpace U]

def bottomListMap (t : List U) (k : ℕ) : Bottom.Cantor := Bottom.bottomMap (contextOfList t) k

theorem bottomListMap_injective :
    Function.Injective (fun p : Token U => bottomListMap p.1 p.2) := by
  intro p q heq
  have hh : (contextOfList p.1,p.2) = (contextOfList q.1,q.2) := Bottom.bottomMap_injective heq
  exact Prod.ext (contextOfList_injective (congrArg Prod.fst hh))
    (congrArg (fun t : Bottom.Context U × ℕ => t.2) hh)

/-- Pointwise fixing the intended coordinate enumeration preserves exactly
the bottom neighborhood, which recovers the literal raw tuple and label. -/
theorem bottom_recovery_between_pools (P Q : Set U) (v : Token P) (w : Token Q)
    (h : bottomListMap (name P v).1 v.2 = bottomListMap (name Q w).1 w.2) :
    name P v = name Q w := bottomListMap_injective h

theorem bottomListMap_finite_independence {ι : Type*} [Fintype ι]
    (p : ι → Token U) (hp : Function.Injective p) (epsilon : ι → Bool) (N : ℕ) :
    ∃ q > N, ∀ i, bottomListMap (p i).1 (p i).2 q = epsilon i := by
  apply Bottom.bottomMap_finite_independence
    (fun i => (contextOfList (p i).1,(p i).2)) ?_ epsilon N
  intro i j heq
  apply hp
  exact Prod.ext (contextOfList_injective (congrArg Prod.fst heq))
    (congrArg (fun t : Bottom.Context U × ℕ => t.2) heq)

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenMap
section


noncomputable section

namespace FSCofinality.Tokens
open GenericTables

def mapToken {U V : Type*} (f : U → V) (v : Token U) : Token V := (v.1.map f,v.2)

theorem history_mapToken {U V : Type*} (f : U → V) (v : Token U) :
    (history (mapToken f v)).val = (history v).val := by
  unfold mapToken history
  rw [List.length_map]

theorem localCode_mapToken {U V : Type*} (f : U → V) (v : Token U) (n : ℕ) :
    localCode (mapToken f v) n = localCode v n := by
  unfold localCode
  rw [history_mapToken]

theorem activeTuple_mapToken {U V : Type*} (f : U → V) (v : Token U) (n : ℕ) :
    activeTuple (mapToken f v) n = (activeTuple v n).map f := by
  unfold activeTuple activeLength
  rw [history_mapToken]
  exact List.map_take.symm

theorem branchEdge_mapToken {U V : Type*} {Col : ℕ → Type*}
    (f : U → V) (profile : ∀ n, V → Col n → Bool) (A : Table) (e n : ℕ)
    (v : Token U) (c : Token (Col n)) :
    branchEdge profile A e n (mapToken f v) c =
      branchEdge (fun n u => profile n (f u)) A e n v c := by
  simp only [branchEdge,activeProfiles,localCode_mapToken,activeTuple_mapToken,
    List.map_map,Function.comp_def]

def widen {U : Type*} {P S : Set U} (h : P ⊆ S) : Token P → Token S :=
  mapToken (fun u => ⟨u.val,h u.property⟩)

theorem name_widen {U : Type*} {P S : Set U} (h : P ⊆ S) (v : Token P) :
    name S (widen h v) = name P v := by
  simp only [name,widen,mapToken,List.map_map,Function.comp_def]

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenLimitRecovery
section


noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

/-- Limit recovery in two countable presentations of the same ambient raw
universe. Full profile injectivity is needed only on the two actual pools. -/
theorem limit_recovery_between_pools {U : Type*} {Col : ℕ → Type*}
    {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A) (e : ℕ → ℕ)
    (PX PY : Set U) (profile : ∀ n, U → Col n → Bool)
    (j : ∀ n, Col n → Col (n+1))
    (propagate : ∀ n, ∀ u ∈ PX ∪ PY, ∀ c, profile (n+1) u (j n c) = profile n u c)
    (hinj : (PX ∪ PY).InjOn (fun u => fun n => profile n u))
    (v : Token PX) (w : Token PY)
    (hsignature : ∀ n q,
      branchEdge (fun n u => profile n u.val) A (e n) n v q =
        branchEdge (fun n u => profile n u.val) A (e n) n w q) :
    name PX v = name PY w := by
  let S := PX ∪ PY
  let liftX : PX → S := fun u => ⟨u.val,Or.inl u.property⟩
  let liftY : PY → S := fun u => ⟨u.val,Or.inr u.property⟩
  let p : ∀ n, S → Col n → Bool := fun n u => profile n u.val
  have hp : Function.Injective (fun u : S => fun n => p n u) := by
    intro u v heq
    apply Subtype.ext
    exact hinj u.property v.property heq
  have hR (n : ℕ) : R p n (mapToken liftX v) (mapToken liftY w) := by
    apply (R_iff_branch_neighborhood p hA (e n) n _ _).mpr
    intro q
    rw [branchEdge_mapToken,branchEdge_mapToken]
    exact hsignature n q
  have heq := all_R_separate p j (fun n u c => propagate n u.val u.property c) hp hR
  have hn := congrArg (name S) heq
  simpa only [name,mapToken,List.map_map,Function.comp_def,liftX,liftY] using hn

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.CosetConstructionTokenModels
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

abbrev MainIndex := Frame.Layer eta
abbrev LimitIndex := {a : MainIndex eta // IsSuccLimit (Frame.rank a)}
abbrev ColumnIndex := LimitIndex eta × ℕ
abbrev SuccessorIndex := {a : MainIndex eta // Frame.rank a + 1 ≤ Frame.top eta}
abbrev TokenSort := MainIndex eta ⊕ ColumnIndex eta
abbrev OrdinaryRole := SuccessorIndex eta ⊕ ColumnIndex eta

instance mainIndex_countable : Countable (MainIndex eta) := Frame.layer_countable eta heta
instance limitIndex_countable : Countable (LimitIndex eta) := by
  letI := mainIndex_countable eta heta
  exact inferInstanceAs (Countable {a : MainIndex eta // _})
instance columnIndex_countable : Countable (ColumnIndex eta) := by
  letI := limitIndex_countable eta heta
  infer_instance
instance sort_countable : Countable (TokenSort eta) := by
  letI := mainIndex_countable eta heta
  letI := columnIndex_countable eta heta
  infer_instance
instance ordinaryRole_countable : Countable (OrdinaryRole eta) := by
  letI := mainIndex_countable eta heta
  letI := columnIndex_countable eta heta
  infer_instance

def mainPool (x : (fsTower eta).Carrier) (a : Ordinal.{0}) : Set (Ambient eta heta) :=
  Pool eta heta (fun b => fullSeeds eta heta b x) a

def lowerPools (x : (fsTower eta).Carrier) (lam : Ordinal.{0}) :
    ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta) := fun b _ => mainPool eta heta x b

def raw (x : (fsTower eta).Carrier) : TokenSort eta → Type
  | .inl a => mainPool eta heta x (Frame.rank a)
  | .inr (lam,n) => Column eta heta (Frame.rank lam.val) lam.property
      (lowerPools eta heta x (Frame.rank lam.val)) n

instance mainPool_countable (x : (fsTower eta).Carrier) (a : Ordinal.{0}) :
    Countable (mainPool eta heta x a) :=
  (pool_countable eta heta _ (fun b => fullSeeds_countable eta heta b x) a).to_subtype

instance columnRaw_countable (x : (fsTower eta).Carrier) (c : ColumnIndex eta) :
    Countable (raw eta heta x (.inr c)) := by
  rcases c with ⟨lam,n⟩
  let f : raw eta heta x (.inr (lam,n)) → mainPool eta heta x
      (Frame.delta eta (Frame.rank lam.val) lam.property n) := fun c =>
    ⟨encodeColumn eta heta (Frame.rank lam.val) lam.property
      (lowerPools eta heta x (Frame.rank lam.val)) n c,
      (pool_encodeColumn eta heta _ _ _ (Frame.rank_le_top lam.val) n c).1⟩
  apply Function.Injective.countable (f := f)
  intro c d h
  exact encodeColumn_injective eta heta _ _ _ (Frame.rank_le_top lam.val) n
    (congrArg Subtype.val h)

instance raw_countable (x : (fsTower eta).Carrier) (s : TokenSort eta) : Countable (raw eta heta x s) := by
  cases s with
  | inl a => exact mainPool_countable eta heta x _
  | inr c => exact columnRaw_countable eta heta x c

def Vertex (x : (fsTower eta).Carrier) := ℕ ⊕ Σ s : TokenSort eta, Token (raw eta heta x s)

instance vertex_countable (x : (fsTower eta).Carrier) : Countable (Vertex eta heta x) := by
  letI := sort_countable eta heta
  exact inferInstanceAs (Countable (ℕ ⊕ Σ s : TokenSort eta, List (raw eta heta x s) × ℕ))

instance vertex_infinite (x : (fsTower eta).Carrier) : Infinite (Vertex eta heta x) :=
  Infinite.of_injective (Sum.inl : ℕ → Vertex eta heta x) Sum.inl_injective

def sortOf {x : (fsTower eta).Carrier} : Vertex eta heta x → Option (TokenSort eta)
  | .inl _ => none
  | .inr ⟨s,_⟩ => some s

def mainSort (a : Ordinal.{0}) (ha : a ≤ Frame.top eta) : TokenSort eta :=
  .inl (Frame.ofOrdinal eta a ha)

def rowSort : OrdinaryRole eta → TokenSort eta
  | .inl a => mainSort eta (Frame.rank a.val+1) a.property
  | .inr c => .inr c

def colSort : OrdinaryRole eta → TokenSort eta
  | .inl a => .inl a.val
  | .inr (lam,n) => mainSort eta (Frame.rho eta (Frame.rank lam.val) lam.property n)
      ((Frame.rho_lt eta _ lam.property n).le.trans (Frame.rank_le_top lam.val))

def ordinaryMatrix (x : (fsTower eta).Carrier) (e : OrdinaryRole eta) :
    raw eta heta x (rowSort eta e) → raw eta heta x (colSort eta e) → Bool := by
  cases e with
  | inl a =>
    intro r c
    exact ordinaryRaw r.val c.val
  | inr c =>
    rcases c with ⟨lam,n⟩
    intro r c
    exact ordinaryRaw
      (encodeColumn eta heta _ lam.property (lowerPools eta heta x _) n r) c.val

def roleNumber : OrdinaryRole eta ⊕ ColumnIndex eta ↪ ℕ := by
  letI := ordinaryRole_countable eta heta
  letI := columnIndex_countable eta heta
  letI := Encodable.ofCountable (OrdinaryRole eta ⊕ ColumnIndex eta)
  exact ⟨Encodable.encode,Encodable.encode_injective⟩

def ambientLower (x : (fsTower eta).Carrier) (lam : Ordinal.{0}) :
    ∀ b hb, lowerPools eta heta x lam b hb ⊆ fullLower eta heta lam b hb :=
  fun b _ => pool_subset_valid eta heta _ (fun a => fullSeeds_typed eta heta a x) b

def limitProfile (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (r : raw eta heta x (.inl lam.val))
    (c : raw eta heta x (.inr (lam,n))) : Bool :=
  ambientProfile eta heta (Frame.rank lam.val) lam.property (Frame.rank_le_top lam.val) n r.val
    (mapColumn eta heta _ lam.property (ambientLower eta heta x _) n c)

def ordinary (x : (fsTower eta).Carrier) (e : OrdinaryRole eta)
    (r : Token (raw eta heta x (rowSort eta e)))
    (c : Token (raw eta heta x (colSort eta e))) : Bool :=
  ordinaryEdge genericTable (roleNumber eta heta (.inl e)) (ordinaryMatrix eta heta x e) r c

def branch (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (r : Token (raw eta heta x (.inl lam.val)))
    (c : Token (raw eta heta x (.inr (lam,n)))) : Bool :=
  branchEdge (limitProfile eta heta x lam) genericTable (roleNumber eta heta (.inr (lam,n))) n r c

abbrev Symbol := Option (TokenSort eta) ⊕
  (OrdinaryRole eta ⊕ (ColumnIndex eta ⊕ (ColumnIndex eta ⊕ Unit)))

def arity : Symbol eta → ℕ
  | .inl _ => 1
  | .inr _ => 2

def language : CountableRelationalLanguage where
  Symbol := Symbol eta
  arity := arity eta
  countable := by
    letI := sort_countable eta heta
    letI := ordinaryRole_countable eta heta
    letI := columnIndex_countable eta heta
    infer_instance

def tokenAt {x : (fsTower eta).Carrier} (s : TokenSort eta) :
    Vertex eta heta x → Option (Token (raw eta heta x s))
  | .inl _ => none
  | .inr ⟨t,v⟩ => if h : t=s then some (h ▸ v) else none

def coordinateAt {x : (fsTower eta).Carrier} : Vertex eta heta x → Option ℕ
  | .inl n => some n
  | .inr _ => none

def edgeAt {x : (fsTower eta).Carrier} (s t : TokenSort eta)
    (f : Token (raw eta heta x s) → Token (raw eta heta x t) → Bool)
    (u v : Vertex eta heta x) : Bool :=
  (tokenAt eta heta s u).elim false (fun r => (tokenAt eta heta t v).elim false (f r))

def zeroSort : TokenSort eta := mainSort eta 0 zero_le

/-- All non-sort symbols are binary. Bottom neighborhoods are supplied by
the actual atom decoder; no sigma algebra on the raw semantic universe is used. -/
def diagram (bottom : ∀ x : (fsTower eta).Carrier,
    Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x : (fsTower eta).Carrier) :
    (s : Symbol eta) → (Fin (arity eta s) → Vertex eta heta x) → Bool
  | .inl s,a => decide (sortOf eta heta (a (0 : Fin 1)) = s)
  | .inr (.inl e),a => edgeAt eta heta (rowSort eta e) (colSort eta e)
      (ordinary eta heta x e) (a (0 : Fin 2)) (a (1 : Fin 2))
  | .inr (.inr (.inl (lam,n))),a => edgeAt eta heta (.inl lam.val) (.inr (lam,n))
      (branch eta heta x lam n) (a (0 : Fin 2)) (a (1 : Fin 2))
  | .inr (.inr (.inr (.inl (lam,n)))),a =>
      edgeAt eta heta (.inl lam.val) (.inl lam.val)
        (fun r t => decide (R (limitProfile eta heta x lam) n r t)) (a (0 : Fin 2)) (a (1 : Fin 2))
  | .inr (.inr (.inr (.inr _))),a =>
      (tokenAt eta heta (zeroSort eta) (a (0 : Fin 2))).elim false (fun r =>
        (coordinateAt eta heta (a (1 : Fin 2))).elim false (bottom x r))

def modelWithEnumeration (bottom : ∀ x : (fsTower eta).Carrier,
    Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x : (fsTower eta).Carrier) (e : ℕ ≃ Vertex eta heta x) :
    Structures (language eta heta) :=
  fun c => diagram eta heta bottom x c.1 (e ∘ c.2)

def LiteralIsomorphic (bottom : ∀ x : (fsTower eta).Carrier,
    Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x y : (fsTower eta).Carrier) : Prop :=
  ∃ e : Vertex eta heta x ≃ Vertex eta heta y,
    ∀ s a, diagram eta heta bottom x s a = diagram eta heta bottom y s (e ∘ a)

theorem isomorphic_modelWithEnumeration_iff
    (bottom : ∀ x : (fsTower eta).Carrier, Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x y : (fsTower eta).Carrier)
    (e : ℕ ≃ Vertex eta heta x) (f : ℕ ≃ Vertex eta heta y) :
    Isomorphic (modelWithEnumeration eta heta bottom x e) (modelWithEnumeration eta heta bottom y f) ↔
      LiteralIsomorphic eta heta bottom x y := by
  constructor
  · rintro ⟨p,hp⟩
    let q := (e.symm.trans p).trans f
    refine ⟨q,fun s a => ?_⟩
    have h := hp s (e.symm ∘ a)
    simpa only [modelWithEnumeration,q,Equiv.trans_apply,Function.comp_def,
      Equiv.apply_symm_apply] using h
  · rintro ⟨q,hq⟩
    let p := (e.trans q).trans f.symm
    refine ⟨p,fun s a => ?_⟩
    have h := hq s (e ∘ a)
    simpa only [modelWithEnumeration,p,Equiv.trans_apply,Function.comp_def,
      Equiv.apply_symm_apply] using h

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.CosetConstructionSourceBorel
section


noncomputable section
open Set MeasureTheory

namespace FSCofinality.CosetConstruction

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- Equality of the represented optional semantic values is Borel on each
fixed source code level, although the raw semantic universe has no Borel
structure installed on it. -/
theorem measurableSet_optionalTranslate_eq (a : Ordinal.{0}) :
    MeasurableSet {p : (Unit ⊕ (fsTower a).Carrier) × (Unit ⊕ (fsTower a).Carrier) |
      optionalTranslate eta heta a p.1 = optionalTranslate eta heta a p.2} := by
  let E := fsTower a
  have hE := regular_fsTower a
  letI : StandardBorelSpace E.Carrier := hE.standardBorel
  letI : StandardBorelSpace (Unit ⊕ E.Carrier) := standardBorel_sum
  let base : E.Carrier := Classical.choice hE.nonempty
  let get : Unit ⊕ E.Carrier → E.Carrier := Sum.elim (fun _ => base) id
  have hg : Measurable get := measurable_const.sumElim measurable_id
  have hn : MeasurableSet {x : Unit ⊕ E.Carrier | x = .inl ()} :=
    measurableSet_singleton _
  have heq := hE.measurable_graph.preimage
    ((hg.comp measurable_fst).prodMk (hg.comp measurable_snd))
  have hboth := (hn.preimage measurable_fst).inter (hn.preimage measurable_snd)
  have hsome := (hn.preimage measurable_fst).compl.inter (hn.preimage measurable_snd).compl
  convert hboth.union (hsome.inter heq) using 1
  ext p
  rcases p with ⟨x,y⟩
  rcases x with ⟨⟨⟩⟩ | x <;> rcases y with ⟨⟨⟩⟩ | y
  all_goals simp [optionalTranslate,get,translate_eq_iff]
  all_goals rfl

theorem optionalTranslate_cast {a b : Ordinal.{0}} (h : a = b)
    (z : Unit ⊕ (fsTower a).Carrier) :
    optionalTranslate eta heta b (Sum.map id (codeCast (congrArg fsTower h)) z) =
      optionalTranslate eta heta a z := by
  cases h
  cases z <;> rfl

/-- The semantic equality tests needed to remove repetitions from the
countable source-path enumeration are actual Borel predicates. -/
theorem measurableSet_sourcePathValue_eq (p q : List ℕ)
    (hrank : (sourcePath eta p).rank = (sourcePath eta q).rank) :
    MeasurableSet {xy : (fsTower eta).Carrier × (fsTower eta).Carrier |
      sourcePathValue eta heta p xy.1 = sourcePathValue eta heta q xy.2} := by
  let f := (sourcePath eta p).get
  let g := Sum.map id (codeCast (congrArg fsTower hrank.symm)) ∘ (sourcePath eta q).get
  have hf : Measurable f := (sourcePath eta p).measurable_get
  have hg : Measurable g := (measurable_id.sumMap (codeCast _).measurable).comp
    (sourcePath eta q).measurable_get
  have h := (measurableSet_optionalTranslate_eq eta heta (sourcePath eta p).rank).preimage
    ((hf.comp measurable_fst).prodMk (hg.comp measurable_snd))
  convert h using 1
  ext xy
  simp only [mem_setOf_eq,mem_preimage,sourcePathValue,f,g,Function.comp_apply]
  rw [optionalTranslate_cast eta heta hrank.symm]

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionSeedCodes
section


noncomputable section
open Set MeasureTheory Ordinal

namespace FSCofinality.CosetConstruction
open RawObjects

abbrev SeedIndex := Option (List ℕ)
variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- A countable, input-independent code list for the actual source seeds.
The empty index denotes the one top source seed, not a missing invariant. -/
def evalSeed (a : Ordinal.{0}) (s : SeedIndex) (x : (fsTower eta).Carrier) :
    Option (Ambient eta heta) :=
  match s with
  | none => if a = Frame.top eta then some (topSource eta heta x) else none
  | some p => if (sourcePath eta p).rank = a then sourcePathValue eta heta p x else none

theorem evalSeed_covers (a : Ordinal.{0}) (x : (fsTower eta).Carrier) (u : Ambient eta heta) :
    u ∈ fullSeeds eta heta a x ↔ ∃ s : SeedIndex, evalSeed eta heta a s x = some u := by
  constructor
  · intro hu
    by_cases ha : a = Frame.top eta
    · have heq : u = topSource eta heta x := by simpa only [fullSeeds,if_pos ha,mem_singleton_iff] using hu
      exact ⟨none,by simp [evalSeed,ha,heq]⟩
    · rw [fullSeeds,if_neg ha] at hu
      obtain ⟨p,hp,hvalue⟩ := hu
      exact ⟨some p,by simp only [evalSeed,if_pos hp,hvalue]⟩
  · rintro ⟨s,hs⟩
    cases s with
    | none =>
      by_cases ha : a = Frame.top eta
      · have heq : topSource eta heta x = u := by simpa only [evalSeed,if_pos ha,Option.some.injEq] using hs
        simp [fullSeeds,ha,← heq]
      · simp [evalSeed,ha] at hs
    | some p =>
      by_cases hp : (sourcePath eta p).rank = a
      · have hv : sourcePathValue eta heta p x = some u := by simpa only [evalSeed,if_pos hp] using hs
        exact sourceSeeds_subset_fullSeeds eta heta a x ⟨p,hp,hv⟩
      · simp [evalSeed,hp] at hs

theorem measurableSet_sourcePath_absent (p : List ℕ) :
    MeasurableSet {x : (fsTower eta).Carrier | sourcePathValue eta heta p x = none} := by
  have h := (measurableSet_optionalTranslate_eq eta heta (sourcePath eta p).rank).preimage
    ((sourcePath eta p).measurable_get.prodMk
      (measurable_const : Measurable (fun _ : (fsTower eta).Carrier =>
        (Sum.inl () : Unit ⊕ (fsTower (sourcePath eta p).rank).Carrier))))
  convert h using 1

theorem measurableSet_evalSeed_absent (a : Ordinal.{0}) (s : SeedIndex) :
    MeasurableSet {x : (fsTower eta).Carrier | evalSeed eta heta a s x = none} := by
  cases s with
  | none =>
    by_cases ha : a = Frame.top eta <;> simp [evalSeed,ha]
  | some p =>
    by_cases hp : (sourcePath eta p).rank = a
    · simpa only [evalSeed,if_pos hp] using measurableSet_sourcePath_absent eta heta p
    · simp [evalSeed,hp]

theorem measurableSet_evalSeed_eq (a : Ordinal.{0}) (s t : SeedIndex) :
    MeasurableSet {xy : (fsTower eta).Carrier × (fsTower eta).Carrier |
      evalSeed eta heta a s xy.1 = evalSeed eta heta a t xy.2} := by
  cases s with
  | none =>
    cases t with
    | none =>
      by_cases ha : a = Frame.top eta
      · have h := (regular_fsTower eta).measurable_graph
        convert h using 1
        ext xy
        simp only [evalSeed,if_pos ha,Option.some.injEq,topSource_eq_iff]
      · simp [evalSeed,ha]
    | some q =>
      by_cases ha : a = Frame.top eta
      · have hq : (sourcePath eta q).rank ≠ a := by
          intro h
          have hle := (sourcePath eta q).rank_le
          rw [h,ha] at hle
          exact not_le_of_gt (Frame.lt_top eta) hle
        simp only [evalSeed,if_pos ha,if_neg hq]
        simp
      · have h := (measurableSet_evalSeed_absent eta heta a (some q)).preimage
          (measurable_snd : Measurable (fun xy : (fsTower eta).Carrier × (fsTower eta).Carrier => xy.2))
        convert h using 1
        ext xy
        simp only [Set.mem_setOf_eq,Set.mem_preimage,evalSeed,if_neg ha]
        exact eq_comm
  | some p =>
    cases t with
    | none =>
      by_cases ha : a = Frame.top eta
      · have hp : (sourcePath eta p).rank ≠ a := by
          intro h
          have hle := (sourcePath eta p).rank_le
          rw [h,ha] at hle
          exact not_le_of_gt (Frame.lt_top eta) hle
        simp only [evalSeed,if_pos ha,if_neg hp]
        simp
      · have h := (measurableSet_evalSeed_absent eta heta a (some p)).preimage
          (measurable_fst : Measurable (fun xy : (fsTower eta).Carrier × (fsTower eta).Carrier => xy.1))
        convert h using 1
        ext xy
        simp only [Set.mem_setOf_eq,Set.mem_preimage,evalSeed,if_neg ha]
    | some q =>
      by_cases hp : (sourcePath eta p).rank = a
      · by_cases hq : (sourcePath eta q).rank = a
        · simpa only [evalSeed,if_pos hp,if_pos hq] using
            measurableSet_sourcePathValue_eq eta heta p q (hp.trans hq.symm)
        · have h := (measurableSet_evalSeed_absent eta heta a (some p)).preimage
            (measurable_fst : Measurable (fun xy : (fsTower eta).Carrier × (fsTower eta).Carrier => xy.1))
          simpa only [evalSeed,if_neg hq] using h
      · have h := (measurableSet_evalSeed_absent eta heta a (some q)).preimage
          (measurable_snd : Measurable (fun xy : (fsTower eta).Carrier × (fsTower eta).Carrier => xy.2))
        convert h using 1
        ext xy
        simp only [Set.mem_setOf_eq,Set.mem_preimage,evalSeed,if_neg hp]
        exact eq_comm

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionSeedShapes
section


noncomputable section
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem translate_zero (x : (fsTower 0).Carrier) :
    translate eta heta 0 x = sourceAtom (cast (congrArg CodedRelation.Carrier fsTower_zero) x) := by
  unfold translate sourceStage
  rw [Ordinal.limitRecOn_zero,SourceRealization.transport_value]
  rfl

theorem evalSeed_zero_source (s : SeedIndex) (x : (fsTower eta).Carrier)
    (v : Ambient eta heta) (hv : evalSeed eta heta 0 s x = some v) :
    ∃ r, v = sourceAtom r := by
  cases s with
  | none =>
    have ht : (0 : Ordinal.{0}) ≠ Frame.top eta :=
      ne_of_lt (lt_of_le_of_lt zero_le (Frame.lt_top eta))
    simp only [evalSeed,if_neg ht] at hv
    contradiction
  | some p =>
    have hp : (sourcePath eta p).rank = 0 := by
      by_contra h
      simp only [evalSeed,if_neg h] at hv
      contradiction
    have hvalue : sourcePathValue eta heta p x = some v := by
      simpa only [evalSeed,if_pos hp] using hv
    unfold sourcePathValue optionalTranslate at hvalue
    split at hvalue
    · contradiction
    · rename_i y hy
      cases hvalue
      have haux (b : Ordinal.{0}) (hb : b = 0) (y : (fsTower b).Carrier) :
          ∃ r, translate eta heta b y = sourceAtom r := by
        subst b
        exact ⟨_,translate_zero eta heta y⟩
      exact haux _ hp y

theorem evalSeed_zero_ne_extra (s : SeedIndex) (x : (fsTower eta).Carrier) (n : ℕ) :
    evalSeed eta heta 0 s x ≠ some (extraAtom n) := by
  intro hv
  obtain ⟨r,hr⟩ := evalSeed_zero_source eta heta s x _ hv
  exact sourceAtom_ne_extraAtom r n hr.symm

theorem successor_member_iff_child (b a : Ordinal.{0}) (hb : b = a+1)
    (y : (fsTower b).Carrier) (u : Ambient eta heta) :
    Member u (translate eta heta b y) ↔
      ∃ n, codeChildValue eta heta b n y = some u := by
  subst b
  rw [translate_add_one]
  cases hv : successorCode a y with
  | none => simp only [hv,Option.map_none,member_collection_none]
            simp only [codeChildValue_add_one,hv,Option.map_none,reduceCtorEq,exists_const]
  | some v =>
    simp only [hv,Option.map_some,member_collection_some,codeChildValue_add_one,
      Option.some.injEq]

theorem evalSeed_successor_none (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    evalSeed eta heta (a+1) none x = none := by
  simp only [evalSeed,if_neg (successor_ne_top eta a)]

theorem evalSeed_successor_member (a : Ordinal.{0}) (p : List ℕ)
    (x : (fsTower eta).Carrier) (v u : Ambient eta heta)
    (hv : evalSeed eta heta (a+1) (some p) x = some v) :
    Member u v ↔ ∃ n, evalSeed eta heta a (some (n::p)) x = some u := by
  have hp : (sourcePath eta p).rank = a+1 := by
    by_contra h
    simp only [evalSeed,if_neg h] at hv
    contradiction
  have hvalue : sourcePathValue eta heta p x = some v := by
    simpa only [evalSeed,if_pos hp] using hv
  unfold sourcePathValue optionalTranslate at hvalue
  split at hvalue
  · contradiction
  · rename_i y hy
    cases hvalue
    rw [successor_member_iff_child eta heta _ a hp]
    apply exists_congr
    intro n
    have hn : (sourcePath eta (n::p)).rank = a := by
      change (codeChildren (sourcePath eta p).rank).rank n = a
      rw [hp,codeChildren_add_one_rank]
    change (codeChildren (sourcePath eta p).rank).rank n = a at hn
    simp only [evalSeed,if_pos hn,sourcePathValue,sourcePath,
      Function.comp_apply,hy,Sum.elim_inr,codeChildValue]

def childSeed (s : SeedIndex) (n : ℕ) : SeedIndex := s.map (n::·)

theorem evalSeed_successor_member_all (a : Ordinal.{0}) (s : SeedIndex)
    (x : (fsTower eta).Carrier) (v u : Ambient eta heta)
    (hv : evalSeed eta heta (a+1) s x = some v) :
    Member u v ↔ ∃ n, evalSeed eta heta a (childSeed s n) x = some u := by
  cases s with
  | none => rw [evalSeed_successor_none] at hv; contradiction
  | some p => exact evalSeed_successor_member eta heta a p x v u hv

theorem evalSeed_limit_source (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (s : SeedIndex) (x : (fsTower eta).Carrier) (v : Ambient eta heta)
    (hv : evalSeed eta heta lam s x = some v) :
    ∃ z, v = sourceSequence (level eta lam) z := by
  cases s with
  | none =>
    by_cases ha : lam = Frame.top eta
    · have heq : topSource eta heta x = v := by
        simpa only [evalSeed,if_pos ha,Option.some.injEq] using hv
      exact ⟨topCoordinates eta heta x,by simpa only [ha,topSource] using heq.symm⟩
    · simp only [evalSeed,if_neg ha] at hv
      contradiction
  | some p =>
    have hp : (sourcePath eta p).rank = lam := by
      by_contra h
      simp only [evalSeed,if_neg h] at hv
      contradiction
    have hvalue : sourcePathValue eta heta p x = some v := by
      simpa only [evalSeed,if_pos hp] using hv
    unfold sourcePathValue optionalTranslate at hvalue
    split at hvalue
    · contradiction
    · rename_i y hy
      cases hvalue
      obtain ⟨z,hz,_⟩ := limit_value_children eta heta _ lam hp hlam y
      exact ⟨z,hz⟩

theorem evalSeed_limit_ne_filler (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (s : SeedIndex) (x : (fsTower eta).Carrier) (A : Finset (ℕ × Ambient eta heta)) :
    evalSeed eta heta lam s x ≠ some (finiteFiller (level eta lam) A) := by
  intro hv
  obtain ⟨z,hz⟩ := evalSeed_limit_source eta heta lam hlam s x _ hv
  exact sourceSequence_ne_finiteFiller _ _ z A hz.symm

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionFiniteEval
section


noncomputable section
attribute [local instance] Classical.propDecidable

namespace FSCofinality.CosetConstruction

def liftFinite {C Z : Type*} (base : Z) (f : C → Option Z) (A : Finset C) : Option (Finset Z) :=
  if ∀ c ∈ A, f c ≠ none then some (A.image (fun c => (f c).getD base)) else none

theorem liftFinite_some {C Z : Type*} (base : Z) (f : C → Option Z) (A : Finset C)
    (hA : ∀ c ∈ A, f c ≠ none) :
    liftFinite base f A = some (A.image (fun c => (f c).getD base)) := by
  simp only [liftFinite,if_pos hA]

theorem liftFinite_mem {C Z : Type*} (base : Z) (f : C → Option Z) (A : Finset C) (B : Finset Z)
    (h : liftFinite base f A = some B) : ∀ u ∈ B, ∃ c ∈ A, f c = some u := by
  classical
  unfold liftFinite at h
  split_ifs at h with hA
  · cases h
    intro u hu
    obtain ⟨c,hc,hu⟩ := Finset.mem_image.mp hu
    refine ⟨c,hc,?_⟩
    cases heq : f c with
    | none => exact False.elim (hA c hc heq)
    | some z => simpa only [heq,Option.getD_some,Option.some.injEq] using hu

theorem liftFinite_mem_iff {C Z : Type*} (base : Z) (f : C → Option Z) (A : Finset C)
    (B : Finset Z) (h : liftFinite base f A = some B) (u : Z) :
    u ∈ B ↔ ∃ c ∈ A, f c = some u := by
  constructor
  · exact liftFinite_mem base f A B h u
  · rintro ⟨c,hc,hv⟩
    unfold liftFinite at h
    split_ifs at h with hA
    cases h
    exact Finset.mem_image.mpr ⟨c,hc,by simp only [hv,Option.getD_some]⟩

theorem liftFinite_covers {C Z : Type*} (base : Z) (f : C → Option Z) (B : Finset Z)
    (hB : ∀ u ∈ B, ∃ c, f c = some u) : ∃ A : Finset C, liftFinite base f A = some B := by
  classical
  let g : B → C := fun u => Classical.choose (hB u.val u.property)
  have hg (u : B) : f (g u) = some u.val := Classical.choose_spec (hB u.val u.property)
  let A : Finset C := Finset.univ.image g
  have hA : ∀ c ∈ A, f c ≠ none := by
    rintro c hc
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hc
    rw [hg]
    simp
  refine ⟨A,?_⟩
  rw [liftFinite_some base f A hA]
  congr 1
  ext u
  constructor
  · intro hu
    obtain ⟨c,hc,hu⟩ := Finset.mem_image.mp hu
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hc
    have heq : v.val = u := by simpa only [hg,Option.getD_some] using hu
    exact heq ▸ v.property
  · intro hu
    exact Finset.mem_image.mpr ⟨g ⟨u,hu⟩,
      Finset.mem_image.mpr ⟨⟨u,hu⟩,Finset.mem_univ _,rfl⟩,
      by simp only [hg,Option.getD_some]⟩

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionPoolCodes
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- A concrete countable collection of partial names for the actual semantic
pool. The absence value discards failed source paths instead of adding padding
objects to the pool. -/
structure PoolCodes (a : Ordinal.{0}) where
  Code : Type
  countable : Countable Code
  value : Code → (fsTower eta).Carrier → Option (Ambient eta heta)
  seed : SeedIndex → Code
  value_seed : ∀ s x, value (seed s) x = evalSeed eta heta a s x
  covers : ∀ x u, (∃ c, value c x = some u) ↔
    u ∈ Pool eta heta (fun b => fullSeeds eta heta b x) a

attribute [instance] PoolCodes.countable

def zeroPoolCodes : PoolCodes eta heta 0 where
  Code := SeedIndex ⊕ ℕ
  countable := inferInstance
  value := Sum.elim (evalSeed eta heta 0) (fun n _ => some (extraAtom n))
  seed := Sum.inl
  value_seed := fun _ _ => rfl
  covers := by
    intro x u
    rw [pool_zero]
    constructor
    · rintro ⟨c,hc⟩
      cases c with
      | inl s => exact Or.inl ((evalSeed_covers eta heta 0 x u).mpr ⟨s,hc⟩)
      | inr n => exact Or.inr ⟨n,Option.some.inj hc⟩
    · rintro (h|⟨n,rfl⟩)
      · obtain ⟨s,hs⟩ := (evalSeed_covers eta heta 0 x u).mp h
        exact ⟨.inl s,hs⟩
      · exact ⟨.inr n,rfl⟩

def successorPoolCodes (a : Ordinal.{0}) (lower : PoolCodes eta heta a) :
    PoolCodes eta heta (a+1) where
  Code := SeedIndex ⊕ Finset lower.Code
  countable := inferInstance
  value := Sum.elim (evalSeed eta heta (a+1)) (fun A x =>
    (liftFinite (extraAtom 0) (fun c => lower.value c x) A).map
      (finiteCollection (level eta (a+1))))
  seed := Sum.inl
  value_seed := fun _ _ => rfl
  covers := by
    intro x u
    rw [pool_add_one]
    constructor
    · rintro ⟨c,hc⟩
      cases c with
      | inl s => exact Or.inl ((evalSeed_covers eta heta (a+1) x u).mpr ⟨s,hc⟩)
      | inr A =>
        change (liftFinite (extraAtom 0) (fun c => lower.value c x) A).map _ = some u at hc
        cases hv : liftFinite (extraAtom 0) (fun c => lower.value c x) A with
        | none => simp only [hv,Option.map_none] at hc; contradiction
        | some B =>
          have hu : finiteCollection (level eta (a+1)) B = u := by
            simpa only [hv,Option.map_some,Option.some.injEq] using hc
          refine Or.inr ((mem_finiteImages_iff _ _ _).mpr ⟨B,?_,hu⟩)
          intro z hz
          obtain ⟨c,_,hc⟩ := liftFinite_mem _ _ A B hv z hz
          exact (lower.covers x z).mp ⟨c,hc⟩
    · rintro (h|h)
      · obtain ⟨s,hs⟩ := (evalSeed_covers eta heta (a+1) x u).mp h
        exact ⟨.inl s,hs⟩
      · obtain ⟨B,hB,rfl⟩ := (mem_finiteImages_iff _ _ _).mp h
        obtain ⟨A,hA⟩ := liftFinite_covers (extraAtom 0) (fun c => lower.value c x) B
          (fun z hz => (lower.covers x z).mpr (hB z hz))
        exact ⟨.inr A,by simp only [Sum.elim_inr,hA,Option.map_some]⟩

def BirthCode (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b) : Type :=
  Σ n : ℕ,
    (lower (Frame.q eta lam hlam n) (Frame.q_lt eta lam hlam n)).Code ⊕
      (Unit ⊕ (lower (Frame.rho eta lam hlam n) (Frame.rho_lt eta lam hlam n)).Code)

instance birthCode_countable (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b) : Countable (BirthCode eta heta lam hlam lower) :=
  inferInstanceAs (Countable (Σ n : ℕ,
    (lower (Frame.q eta lam hlam n) (Frame.q_lt eta lam hlam n)).Code ⊕
      (Unit ⊕ (lower (Frame.rho eta lam hlam n) (Frame.rho_lt eta lam hlam n)).Code)))

def evalBirthCode (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b)
    (c : BirthCode eta heta lam hlam lower) (x : (fsTower eta).Carrier) :
    Option (ℕ × Ambient eta heta) :=
  match c with
  | ⟨n,.inl d⟩ =>
      ((lower _ (Frame.q_lt eta lam hlam n)).value d x).map
        (fun z => (n,dataColumn eta heta lam hlam n z))
  | ⟨n,.inr (.inl _)⟩ => some (n,markerColumn eta heta lam hlam n)
  | ⟨n,.inr (.inr d)⟩ =>
      ((lower _ (Frame.rho_lt eta lam hlam n)).value d x).map
        (fun z => (n,singleton (level eta (Frame.delta eta lam hlam n)) z))

theorem evalBirthCode_covers (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b) (x : (fsTower eta).Carrier)
    (p : ℕ × Ambient eta heta) :
    (∃ c, evalBirthCode eta heta lam hlam lower c x = some p) ↔
      NewColumn eta heta lam hlam (fun b _ =>
        Pool eta heta (fun a => fullSeeds eta heta a x) b) p.1 p.2 := by
  rcases p with ⟨n,z⟩
  constructor
  · rintro ⟨⟨m,c⟩,hc⟩
    cases c with
    | inl d =>
      change ((lower _ (Frame.q_lt eta lam hlam m)).value d x).map _ = some (n,z) at hc
      cases hv : (lower _ (Frame.q_lt eta lam hlam m)).value d x with
      | none => simp only [hv,Option.map_none] at hc; contradiction
      | some u =>
        have hp : (m,dataColumn eta heta lam hlam m u) = (n,z) := by
          simpa only [hv,Option.map_some,Option.some.injEq] using hc
        cases hp
        exact Or.inl ⟨u,((lower _ _).covers x u).mp ⟨d,hv⟩,rfl⟩
    | inr c =>
      cases c with
      | inl unit =>
        have hp : (m,markerColumn eta heta lam hlam m) = (n,z) := Option.some.inj hc
        cases hp
        exact Or.inr (Or.inl rfl)
      | inr d =>
        change ((lower _ (Frame.rho_lt eta lam hlam m)).value d x).map _ = some (n,z) at hc
        cases hv : (lower _ (Frame.rho_lt eta lam hlam m)).value d x with
        | none => simp only [hv,Option.map_none] at hc; contradiction
        | some u =>
          have hp : (m,singleton (level eta (Frame.delta eta lam hlam m)) u) = (n,z) := by
            simpa only [hv,Option.map_some,Option.some.injEq] using hc
          cases hp
          exact Or.inr (Or.inr ⟨u,((lower _ _).covers x u).mp ⟨d,hv⟩,rfl⟩)
  · rintro (⟨u,hu,hz⟩|h|⟨u,hu,hz⟩)
    · change z = dataColumn eta heta lam hlam n u at hz
      obtain ⟨d,hd⟩ := ((lower _ (Frame.q_lt eta lam hlam n)).covers x u).mpr hu
      exact ⟨⟨n,.inl d⟩,by simp only [evalBirthCode,hd,Option.map_some,hz]⟩
    · change z = markerColumn eta heta lam hlam n at h
      rw [h]
      exact ⟨⟨n,.inr (.inl ())⟩,rfl⟩
    · change z = singleton (level eta (Frame.delta eta lam hlam n)) u at hz
      obtain ⟨d,hd⟩ := ((lower _ (Frame.rho_lt eta lam hlam n)).covers x u).mpr hu
      exact ⟨⟨n,.inr (.inr d)⟩,by simp only [evalBirthCode,hd,Option.map_some,hz]⟩

def limitPoolCodes (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b) : PoolCodes eta heta lam where
  Code := SeedIndex ⊕ Finset (BirthCode eta heta lam hlam lower)
  countable := inferInstance
  value := Sum.elim (evalSeed eta heta lam) (fun A x =>
    (liftFinite (0,extraAtom 0) (fun c => evalBirthCode eta heta lam hlam lower c x) A).map
      (finiteFiller (level eta lam)))
  seed := Sum.inl
  value_seed := fun _ _ => rfl
  covers := by
    intro x u
    rw [pool_limit eta heta _ lam hlam]
    constructor
    · rintro ⟨c,hc⟩
      cases c with
      | inl s => exact Or.inl ((evalSeed_covers eta heta lam x u).mpr ⟨s,hc⟩)
      | inr A =>
        change (liftFinite (0,extraAtom 0) (fun c => evalBirthCode eta heta lam hlam lower c x) A).map _ = some u at hc
        cases hv : liftFinite (0,extraAtom 0) (fun c => evalBirthCode eta heta lam hlam lower c x) A with
        | none => simp only [hv,Option.map_none] at hc; contradiction
        | some B =>
          have hu : finiteFiller (level eta lam) B = u := by
            simpa only [hv,Option.map_some,Option.some.injEq] using hc
          refine Or.inr ((mem_finiteImages_iff _ _ _).mpr ⟨B,?_,hu⟩)
          intro z hz
          obtain ⟨c,_,hc⟩ := liftFinite_mem _ _ A B hv z hz
          exact (evalBirthCode_covers eta heta lam hlam lower x z).mp ⟨c,hc⟩
    · rintro (h|h)
      · obtain ⟨s,hs⟩ := (evalSeed_covers eta heta lam x u).mp h
        exact ⟨.inl s,hs⟩
      · obtain ⟨B,hB,rfl⟩ := (mem_finiteImages_iff _ _ _).mp h
        obtain ⟨A,hA⟩ := liftFinite_covers (0,extraAtom 0)
          (fun c => evalBirthCode eta heta lam hlam lower c x) B
          (fun z hz => (evalBirthCode_covers eta heta lam hlam lower x z).mpr (hB z hz))
        exact ⟨.inr A,by simp only [Sum.elim_inr,hA,Option.map_some]⟩

def poolCodes (a : Ordinal.{0}) : PoolCodes eta heta a :=
  Ordinal.limitRecOn a (zeroPoolCodes eta heta)
    (successorPoolCodes eta heta) (limitPoolCodes eta heta)

theorem poolCodes_zero : poolCodes eta heta 0 = zeroPoolCodes eta heta := by
  unfold poolCodes
  rw [Ordinal.limitRecOn_zero]

theorem poolCodes_add_one (a : Ordinal.{0}) :
    poolCodes eta heta (a+1) = successorPoolCodes eta heta a (poolCodes eta heta a) := by
  unfold poolCodes
  rw [Ordinal.limitRecOn_add_one]

theorem poolCodes_limit (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) :
    poolCodes eta heta lam = limitPoolCodes eta heta lam hlam (fun b _ => poolCodes eta heta b) := by
  unfold poolCodes
  rw [Ordinal.limitRecOn_limit _ _ _ _ hlam]

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionFiniteBorel
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction

theorem liftFinite_none_iff {C Z : Type} (base : Z) (f : C → Option Z) (A : Finset C) :
    liftFinite base f A = none ↔ ∃ c ∈ A, f c = none := by
  simp [liftFinite]

private theorem getD_eq_iff {Z : Type} (base : Z) (x y : Option Z)
    (hx : x ≠ none) (hy : y ≠ none) : x.getD base = y.getD base ↔ x=y := by
  cases x <;> cases y <;> simp_all

theorem liftFinite_eq_iff {C D Z : Type} (base : Z) (f : C → Option Z) (g : D → Option Z)
    (A : Finset C) (B : Finset D) :
    liftFinite base f A = liftFinite base g B ↔
      ((∃ c ∈ A, f c = none) ∧ (∃ d ∈ B, g d = none)) ∨
      ((∀ c ∈ A, f c ≠ none) ∧ (∀ d ∈ B, g d ≠ none) ∧
        (∀ c ∈ A, ∃ d ∈ B, f c = g d) ∧ (∀ d ∈ B, ∃ c ∈ A, f c = g d)) := by
  have hbadF : (∃ c ∈ A, f c = none) ↔ ¬ (∀ c ∈ A, f c ≠ none) := by simp
  have hbadG : (∃ d ∈ B, g d = none) ↔ ¬ (∀ d ∈ B, g d ≠ none) := by simp
  by_cases hA : ∀ c ∈ A, f c ≠ none <;> by_cases hB : ∀ d ∈ B, g d ≠ none
  · rw [liftFinite_some base f A hA,liftFinite_some base g B hB,Option.some.injEq]
    have hA' : ¬ ∃ c ∈ A, f c = none := by simpa using hA
    have hB' : ¬ ∃ d ∈ B, g d = none := by simpa using hB
    simp only [hA',hB',false_and,false_or]
    constructor
    · intro hEq
      refine ⟨hA,hB,?_,?_⟩
      · intro c hc
        have hm : (f c).getD base ∈ B.image (fun d => (g d).getD base) :=
          hEq ▸ Finset.mem_image.mpr ⟨c,hc,rfl⟩
        obtain ⟨d,hd,heq⟩ := Finset.mem_image.mp hm
        exact ⟨d,hd,(getD_eq_iff base _ _ (hA c hc) (hB d hd)).mp heq.symm⟩
      · intro d hd
        have hm : (g d).getD base ∈ A.image (fun c => (f c).getD base) :=
          hEq.symm ▸ Finset.mem_image.mpr ⟨d,hd,rfl⟩
        obtain ⟨c,hc,heq⟩ := Finset.mem_image.mp hm
        exact ⟨c,hc,(getD_eq_iff base _ _ (hA c hc) (hB d hd)).mp heq⟩
    · rintro ⟨_,_,hfg,hgf⟩
      apply Finset.ext
      intro z
      constructor
      · rintro hz
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨d,hd,heq⟩ := hfg c hc
        exact Finset.mem_image.mpr ⟨d,hd,congrArg (fun o => o.getD base) heq.symm⟩
      · rintro hz
        obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨c,hc,heq⟩ := hgf d hd
        exact Finset.mem_image.mpr ⟨c,hc,congrArg (fun o => o.getD base) heq⟩
  · rw [liftFinite_some base f A hA,
      (liftFinite_none_iff base g B).mpr (hbadG.mpr hB)]
    constructor
    · intro hEq; cases hEq
    · rintro (⟨hbad,_⟩ | ⟨_,hgood,_,_⟩)
      · obtain ⟨c,hc,hn⟩ := hbad
        exact False.elim (hA c hc hn)
      · exact False.elim (hB hgood)
  · rw [(liftFinite_none_iff base f A).mpr (hbadF.mpr hA),liftFinite_some base g B hB]
    constructor
    · intro hEq; cases hEq
    · rintro (⟨_,hbad⟩ | ⟨hgood,_,_,_⟩)
      · obtain ⟨d,hd,hn⟩ := hbad
        exact False.elim (hB d hd hn)
      · exact False.elim (hA hgood)
  · rw [(liftFinite_none_iff base f A).mpr (hbadF.mpr hA),
      (liftFinite_none_iff base g B).mpr (hbadG.mpr hB)]
    exact ⟨fun _ => Or.inl ⟨hbadF.mpr hA,hbadG.mpr hB⟩,fun _ => rfl⟩

theorem measurableSet_liftFinite_none {X C Z : Type} [MeasurableSpace X] [Countable C]
    (base : Z) (F : C → X → Option Z)
    (hnone : ∀ c, MeasurableSet {x | F c x = none}) (A : Finset C) :
    MeasurableSet {x | liftFinite base (fun c => F c x) A = none} := by
  simp only [liftFinite_none_iff,← exists_prop,setOf_exists]
  exact MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun _ : c∈A => hnone c))

theorem measurableSet_liftFinite_eq {X Y C D Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [Countable C] [Countable D]
    (base : Z) (F : C → X → Option Z) (G : D → Y → Option Z)
    (hF : ∀ c, MeasurableSet {x | F c x = none})
    (hG : ∀ d, MeasurableSet {y | G d y = none})
    (heq : ∀ c d, MeasurableSet {p : X × Y | F c p.1 = G d p.2})
    (A : Finset C) (B : Finset D) :
    MeasurableSet {p : X × Y |
      liftFinite base (fun c => F c p.1) A = liftFinite base (fun d => G d p.2) B} := by
  simp only [liftFinite_eq_iff,setOf_or,setOf_and]
  apply MeasurableSet.union
  · simpa only [Set.preimage_setOf_eq,liftFinite_none_iff] using
      ((measurableSet_liftFinite_none base F hF A).preimage measurable_fst).inter
        ((measurableSet_liftFinite_none base G hG B).preimage measurable_snd)
  · have hpresentF : MeasurableSet {p : X × Y | ∀ c ∈ A, F c p.1 ≠ none} := by
      simp only [setOf_forall]
      exact MeasurableSet.iInter (fun c => MeasurableSet.iInter (fun _ =>
        ((hF c).preimage measurable_fst).compl))
    have hpresentG : MeasurableSet {p : X × Y | ∀ d ∈ B, G d p.2 ≠ none} := by
      simp only [setOf_forall]
      exact MeasurableSet.iInter (fun d => MeasurableSet.iInter (fun _ =>
        ((hG d).preimage measurable_snd).compl))
    have hfg : MeasurableSet {p : X × Y | ∀ c ∈ A, ∃ d ∈ B, F c p.1 = G d p.2} := by
      simp only [← exists_prop,setOf_forall,setOf_exists]
      exact MeasurableSet.iInter (fun c => MeasurableSet.iInter (fun _ =>
        MeasurableSet.iUnion (fun d => MeasurableSet.iUnion (fun _ => heq c d))))
    have hgf : MeasurableSet {p : X × Y | ∀ d ∈ B, ∃ c ∈ A, F c p.1 = G d p.2} := by
      simp only [← exists_prop,setOf_forall,setOf_exists]
      exact MeasurableSet.iInter (fun d => MeasurableSet.iInter (fun _ =>
        MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun _ => heq c d))))
    exact hpresentF.inter (hpresentG.inter (hfg.inter hgf))

theorem option_map_eq_iff_of_injective {Z W : Type} (k : Z → W) (hk : Function.Injective k)
    (u v : Option Z) : u.map k = v.map k ↔ u=v := by
  cases u <;> cases v <;> simp [hk.eq_iff]

theorem option_map_none_iff {Z W : Type} (k : Z → W) (u : Option Z) :
    u.map k = none ↔ u=none := by cases u <;> simp

theorem measurableSet_map_liftFinite_eq {X Y C D Z W : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [Countable C] [Countable D]
    (base : Z) (F : C → X → Option Z) (G : D → Y → Option Z)
    (hF : ∀ c, MeasurableSet {x | F c x = none})
    (hG : ∀ d, MeasurableSet {y | G d y = none})
    (heq : ∀ c d, MeasurableSet {p : X × Y | F c p.1 = G d p.2})
    (A : Finset C) (B : Finset D) (k : Finset Z → W) (hk : Function.Injective k) :
    MeasurableSet {p : X × Y |
      (liftFinite base (fun c => F c p.1) A).map k =
        (liftFinite base (fun d => G d p.2) B).map k} := by
  simpa only [option_map_eq_iff_of_injective k hk] using
    measurableSet_liftFinite_eq base F G hF hG heq A B

theorem measurableSet_finite_match {X Y C Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [Countable C]
    (F : C → X → Option Z) (G : Y → Option Z)
    (heq : ∀ c, MeasurableSet {p : X × Y | F c p.1 = G p.2}) (A : Finset C) :
    MeasurableSet {p : X × Y | ∃ c ∈ A, F c p.1 = G p.2} := by
  simp only [← exists_prop,setOf_exists]
  exact MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun _ : c∈A => heq c))

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionSeedFinite
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem seed_eq_finiteCollection_iff {C : Type} (a : Ordinal.{0}) (s : SeedIndex)
    (x : (fsTower eta).Carrier) (f : C → Option (Ambient eta heta)) (A : Finset C)
    (B : Finset (Ambient eta heta))
    (hB : liftFinite (extraAtom 0) f A = some B)
    (v : Ambient eta heta) (hv : evalSeed eta heta (a+1) s x = some v) :
    v = finiteCollection (level eta (a+1)) B ↔
      (∀ n, evalSeed eta heta a (childSeed s n) x = none ∨
        ∃ c ∈ A, evalSeed eta heta a (childSeed s n) x = f c) ∧
      (∀ c ∈ A, ∃ n, evalSeed eta heta a (childSeed s n) x = f c) := by
  have hnon (c) (hc : c ∈ A) : f c ≠ none := by
    unfold liftFinite at hB
    split_ifs at hB with h
    exact h c hc
  have hmem (u) : Member u v ↔ ∃ n, evalSeed eta heta a (childSeed s n) x = some u :=
    evalSeed_successor_member_all eta heta a s x v u hv
  constructor
  · intro heq
    constructor
    · intro n
      cases hn : evalSeed eta heta a (childSeed s n) x with
      | none => exact Or.inl rfl
      | some u =>
        have hu : Member u v := (hmem u).mpr ⟨n,hn⟩
        rw [heq,member_finiteCollection] at hu
        obtain ⟨c,hc,hfc⟩ := (liftFinite_mem_iff _ _ A B hB u).mp hu
        exact Or.inr ⟨c,hc,hfc.symm⟩
    · intro c hc
      cases hf : f c with
      | none => exact False.elim (hnon c hc hf)
      | some u =>
        have hu : u ∈ B := (liftFinite_mem_iff _ _ A B hB u).mpr ⟨c,hc,hf⟩
        have hm : Member u v := by simpa only [heq,member_finiteCollection] using hu
        exact (hmem u).mp hm
  · rintro ⟨hforward,hbackward⟩
    have hseed := (evalSeed_covers eta heta (a+1) x v).mpr ⟨s,hv⟩
    obtain ⟨z,hz⟩ := fullSeeds_successor_collection eta heta a x hseed
    obtain ⟨w,hw⟩ := finiteCollection_is_collection (level eta (a+1)) B
    rw [hz,hw]
    apply collection_ext
    intro u
    rw [←hz,←hw,member_finiteCollection,hmem,liftFinite_mem_iff _ _ A B hB u]
    constructor
    · rintro ⟨n,hn⟩
      rcases hforward n with hnnone|⟨c,hc,hfc⟩
      · rw [hn] at hnnone
        contradiction
      · exact ⟨c,hc,hfc.symm.trans hn⟩
    · rintro ⟨c,hc,hfc⟩
      obtain ⟨n,hn⟩ := hbackward c hc
      exact ⟨n,hn.trans hfc⟩

theorem seed_eq_mapFinite_iff {C : Type} (a : Ordinal.{0}) (s : SeedIndex)
    (x : (fsTower eta).Carrier) (f : C → Option (Ambient eta heta)) (A : Finset C) :
    evalSeed eta heta (a+1) s x =
        (liftFinite (extraAtom 0) f A).map (finiteCollection (level eta (a+1))) ↔
      (evalSeed eta heta (a+1) s x = none ∧ liftFinite (extraAtom 0) f A = none) ∨
      (evalSeed eta heta (a+1) s x ≠ none ∧ liftFinite (extraAtom 0) f A ≠ none ∧
        (∀ n, evalSeed eta heta a (childSeed s n) x = none ∨
          ∃ c ∈ A, evalSeed eta heta a (childSeed s n) x = f c) ∧
        (∀ c ∈ A, ∃ n, evalSeed eta heta a (childSeed s n) x = f c)) := by
  cases hv : evalSeed eta heta (a+1) s x with
  | none => cases hB : liftFinite (extraAtom 0) f A <;> simp [hB]
  | some v =>
    cases hB : liftFinite (extraAtom 0) f A with
    | none => simp
    | some B =>
      simp only [Option.map_some,Option.some.injEq,reduceCtorEq,false_and,false_or,
        Option.some_ne_none,not_false_eq_true,true_and]
      have hh := seed_eq_finiteCollection_iff eta heta a s x f A B hB v hv
      constructor
      · intro h
        refine ⟨?_,?_,hh.mp h⟩
        · intro hn
          cases hn
        · intro hn
          cases hn
      · intro h
        exact hh.mpr h.2.2

theorem measurableSet_seed_mapFinite_eq {C : Type} [Countable C]
    (a : Ordinal.{0}) (s : SeedIndex)
    (F : C → (fsTower eta).Carrier → Option (Ambient eta heta))
    (hnone : ∀ c, MeasurableSet {x | F c x = none})
    (heq : ∀ t c, MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      evalSeed eta heta a t p.1 = F c p.2}) (A : Finset C) :
    MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      evalSeed eta heta (a+1) s p.1 =
        (liftFinite (extraAtom 0) (fun c => F c p.2) A).map
          (finiteCollection (level eta (a+1)))} := by
  simp only [seed_eq_mapFinite_iff,setOf_or,setOf_and]
  have hsource := (measurableSet_evalSeed_absent eta heta (a+1) s).preimage
    (measurable_fst : Measurable (fun p : (fsTower eta).Carrier × (fsTower eta).Carrier => p.1))
  have hfinite := (measurableSet_liftFinite_none (extraAtom 0) F hnone A).preimage
    (measurable_snd : Measurable (fun p : (fsTower eta).Carrier × (fsTower eta).Carrier => p.2))
  apply (hsource.inter hfinite).union
  refine hsource.compl.inter (hfinite.compl.inter ?_)
  apply MeasurableSet.inter
  · simp only [setOf_forall,setOf_or,← exists_prop,setOf_exists]
    exact MeasurableSet.iInter (fun n =>
      ((measurableSet_evalSeed_absent eta heta a (childSeed s n)).preimage
        (measurable_fst : Measurable (fun p : (fsTower eta).Carrier × (fsTower eta).Carrier => p.1))).union
        (MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun _ => heq (childSeed s n) c))))
  · simp only [setOf_forall,setOf_exists]
    exact MeasurableSet.iInter (fun c => MeasurableSet.iInter (fun _ =>
      MeasurableSet.iUnion (fun n => heq (childSeed s n) c)))

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionPoolBorel
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- Only tests on the source code spaces are declared measurable. There is no
measurable-space instance on the semantic quotient of raw objects. -/
structure PoolCodesBorel {a : Ordinal.{0}} (P : PoolCodes eta heta a) : Prop where
  absent : ∀ c, MeasurableSet {x | P.value c x = none}
  equal : ∀ c d, MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
    P.value c p.1 = P.value d p.2}

theorem zeroPoolCodes_borel : PoolCodesBorel eta heta (zeroPoolCodes eta heta) where
  absent := by
    intro c
    cases c with
    | inl s => exact measurableSet_evalSeed_absent eta heta 0 s
    | inr n => simp only [zeroPoolCodes,Sum.elim_inr,reduceCtorEq,setOf_false]; exact MeasurableSet.empty
  equal := by
    intro c d
    cases c with
    | inl s =>
      cases d with
      | inl t => exact measurableSet_evalSeed_eq eta heta 0 s t
      | inr n =>
        change MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
          evalSeed eta heta 0 s p.1 = some (extraAtom n)}
        convert MeasurableSet.empty using 1
        ext p
        exact iff_false_intro (evalSeed_zero_ne_extra eta heta s p.1 n)
    | inr n =>
      cases d with
      | inl s =>
        change MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
          some (extraAtom n) = evalSeed eta heta 0 s p.2}
        convert MeasurableSet.empty using 1
        ext p
        exact iff_false_intro (fun h => evalSeed_zero_ne_extra eta heta s p.2 n h.symm)
      | inr m =>
        change MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
          some (extraAtom n) = some (extraAtom m)}
        exact MeasurableSet.const _

theorem successorPoolCodes_borel (a : Ordinal.{0}) (lower : PoolCodes eta heta a)
    (hlower : PoolCodesBorel eta heta lower) :
    PoolCodesBorel eta heta (successorPoolCodes eta heta a lower) where
  absent := by
    intro c
    cases c with
    | inl s => exact measurableSet_evalSeed_absent eta heta (a+1) s
    | inr A =>
      change MeasurableSet {x | (liftFinite (extraAtom 0) (fun c => lower.value c x) A).map
        (finiteCollection (level eta (a+1))) = none}
      simpa only [option_map_none_iff] using
        measurableSet_liftFinite_none (extraAtom 0) lower.value hlower.absent A
  equal := by
    have hseed (s : SeedIndex) (c : lower.Code) :
        MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
          evalSeed eta heta a s p.1 = lower.value c p.2} := by
      simpa only [lower.value_seed] using hlower.equal (lower.seed s) c
    intro c d
    cases c with
    | inl s =>
      cases d with
      | inl t => exact measurableSet_evalSeed_eq eta heta (a+1) s t
      | inr A =>
        exact measurableSet_seed_mapFinite_eq eta heta a s lower.value hlower.absent hseed A
    | inr A =>
      cases d with
      | inl s =>
        have h := (measurableSet_seed_mapFinite_eq eta heta a s lower.value hlower.absent hseed A).preimage
          (measurable_swap : Measurable (Prod.swap :
            (fsTower eta).Carrier × (fsTower eta).Carrier →
            (fsTower eta).Carrier × (fsTower eta).Carrier))
        simpa only [successorPoolCodes,Sum.elim_inl,Sum.elim_inr,Set.preimage_setOf_eq,
          Prod.swap,eq_comm] using h
      | inr B =>
        exact measurableSet_map_liftFinite_eq (extraAtom 0) lower.value lower.value
          hlower.absent hlower.absent hlower.equal A B
          (finiteCollection (level eta (a+1))) (finiteCollection_injective _)

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionBirthBorel
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

private theorem option_map_disjoint_eq_iff {A B Z : Type} (f : A → Z) (g : B → Z)
    (hfg : ∀ a b, f a ≠ g b) (u : Option A) (v : Option B) :
    u.map f = v.map g ↔ u = none ∧ v = none := by
  cases u <;> cases v <;> simp_all

private theorem option_map_ne_some {A Z : Type} (f : A → Z) (z : Z)
    (hf : ∀ a, f a ≠ z) (u : Option A) : u.map f ≠ some z := by
  cases u <;> simp_all

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b)

theorem measurableSet_evalBirthCode_none
    (hnone : ∀ b hb c, MeasurableSet {x | (lower b hb).value c x = none})
    (c : BirthCode eta heta lam hlam lower) :
    MeasurableSet {x | evalBirthCode eta heta lam hlam lower c x = none} := by
  rcases c with ⟨n,c⟩
  rcases c with c | ⟨⟨⟩⟩ | c
  · simpa only [evalBirthCode,option_map_none_iff] using hnone _ _ c
  · simp only [evalBirthCode,Option.some_ne_none,setOf_false]
    exact MeasurableSet.empty
  · simpa only [evalBirthCode,option_map_none_iff] using hnone _ _ c

private theorem evalBirthCode_some_index (c : BirthCode eta heta lam hlam lower)
    (x : (fsTower eta).Carrier) (p : ℕ × Ambient eta heta)
    (h : evalBirthCode eta heta lam hlam lower c x = some p) : p.1 = c.1 := by
  rcases c with ⟨n,c⟩
  rcases c with c | ⟨⟨⟩⟩ | c
  · change ((lower _ _).value c x).map _ = some p at h
    cases hv : (lower _ _).value c x with
    | none => simp only [hv,Option.map_none] at h; contradiction
    | some z =>
      have he : (n,dataColumn eta heta lam hlam n z) = p := by
        simpa only [hv,Option.map_some,Option.some.injEq] using h
      exact (congrArg Prod.fst he).symm
  · exact (congrArg Prod.fst (Option.some.inj h)).symm
  · change ((lower _ _).value c x).map _ = some p at h
    cases hv : (lower _ _).value c x with
    | none => simp only [hv,Option.map_none] at h; contradiction
    | some z =>
      have he : (n,singleton (level eta (Frame.delta eta lam hlam n)) z) = p := by
        simpa only [hv,Option.map_some,Option.some.injEq] using h
      exact (congrArg Prod.fst he).symm

theorem measurableSet_evalBirthCode_equal (htop : lam ≤ Frame.top eta)
    (hnone : ∀ b hb c, MeasurableSet {x | (lower b hb).value c x = none})
    (heq : ∀ b hb c d, MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      (lower b hb).value c p.1 = (lower b hb).value d p.2})
    (c d : BirthCode eta heta lam hlam lower) :
    MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      evalBirthCode eta heta lam hlam lower c p.1 =
        evalBirthCode eta heta lam hlam lower d p.2} := by
  rcases c with ⟨n,c⟩
  rcases d with ⟨m,d⟩
  by_cases hnm : n = m
  · subst m
    have hD : Function.Injective (fun z : Ambient eta heta =>
        (n,dataColumn eta heta lam hlam n z)) := by
      intro u v huv
      exact dataColumn_injective eta heta lam hlam htop n (congrArg Prod.snd huv)
    have hS : Function.Injective (fun z : Ambient eta heta =>
        (n,singleton (level eta (Frame.delta eta lam hlam n)) z)) := by
      intro u v huv
      exact (singleton_eq_iff _ _ _).mp (congrArg Prod.snd huv)
    have hDM (z : Ambient eta heta) :
        (n,dataColumn eta heta lam hlam n z) ≠ (n,markerColumn eta heta lam hlam n) :=
      fun h => dataColumn_ne_marker eta heta lam hlam htop n z (congrArg Prod.snd h)
    have hDS (u v : Ambient eta heta) :
        (n,dataColumn eta heta lam hlam n u) ≠
          (n,singleton (level eta (Frame.delta eta lam hlam n)) v) :=
      fun h => dataColumn_ne_singleton eta heta lam hlam htop n u v (congrArg Prod.snd h)
    have hMS (z : Ambient eta heta) :
        (n,markerColumn eta heta lam hlam n) ≠
          (n,singleton (level eta (Frame.delta eta lam hlam n)) z) :=
      fun h => markerColumn_ne_singleton eta heta lam hlam htop n z (congrArg Prod.snd h)
    rcases c with c | ⟨⟨⟩⟩ | c <;> rcases d with d | ⟨⟨⟩⟩ | d
    · simpa only [evalBirthCode,option_map_eq_iff_of_injective _ hD] using heq _ _ c d
    · simp only [evalBirthCode,option_map_ne_some _ _ hDM,setOf_false]
      exact MeasurableSet.empty
    · simpa only [evalBirthCode,option_map_disjoint_eq_iff _ _ hDS,setOf_and] using
        ((hnone _ _ c).preimage measurable_fst).inter ((hnone _ _ d).preimage measurable_snd)
    · have h : ∀ u, (n,markerColumn eta heta lam hlam n) ≠
          (n,dataColumn eta heta lam hlam n u) := fun u => (hDM u).symm
      have hfalse (p : (fsTower eta).Carrier × (fsTower eta).Carrier) :
          ¬ some (n,markerColumn eta heta lam hlam n) =
            ((lower _ _).value d p.2).map (fun z => (n,dataColumn eta heta lam hlam n z)) :=
        (option_map_ne_some _ _ hDM _).symm
      simpa only [evalBirthCode,hfalse,setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set ((fsTower eta).Carrier × (fsTower eta).Carrier)))
    · simp only [evalBirthCode,setOf_true]
      exact MeasurableSet.univ
    · have hfalse (p : (fsTower eta).Carrier × (fsTower eta).Carrier) :
          ¬ some (n,markerColumn eta heta lam hlam n) =
            ((lower _ _).value d p.2).map
              (fun z => (n,singleton (level eta (Frame.delta eta lam hlam n)) z)) :=
        (option_map_ne_some _ _ (fun z => (hMS z).symm) _).symm
      simpa only [evalBirthCode,hfalse,setOf_false] using
        (MeasurableSet.empty : MeasurableSet (∅ : Set ((fsTower eta).Carrier × (fsTower eta).Carrier)))
    · simpa only [evalBirthCode,
        option_map_disjoint_eq_iff _ _ (fun u v => (hDS v u).symm),setOf_and] using
        ((hnone _ _ c).preimage measurable_fst).inter ((hnone _ _ d).preimage measurable_snd)
    · simp only [evalBirthCode,option_map_ne_some _ _ (fun z => (hMS z).symm),setOf_false]
      exact MeasurableSet.empty
    · simpa only [evalBirthCode,option_map_eq_iff_of_injective _ hS] using heq _ _ c d
  · have hiff (p : (fsTower eta).Carrier × (fsTower eta).Carrier) :
        evalBirthCode eta heta lam hlam lower ⟨n,c⟩ p.1 =
          evalBirthCode eta heta lam hlam lower ⟨m,d⟩ p.2 ↔
        evalBirthCode eta heta lam hlam lower ⟨n,c⟩ p.1 = none ∧
          evalBirthCode eta heta lam hlam lower ⟨m,d⟩ p.2 = none := by
      constructor
      · intro h
        cases hc : evalBirthCode eta heta lam hlam lower ⟨n,c⟩ p.1 with
        | none => exact ⟨rfl,h.symm.trans hc⟩
        | some z =>
          have hd := h.symm.trans hc
          have hz := evalBirthCode_some_index eta heta lam hlam lower ⟨n,c⟩ p.1 z hc
          have hz' := evalBirthCode_some_index eta heta lam hlam lower ⟨m,d⟩ p.2 z hd
          exact False.elim (hnm (hz.symm.trans hz'))
      · rintro ⟨hc,hd⟩
        exact hc.trans hd.symm
    simpa only [hiff,setOf_and] using
      ((measurableSet_evalBirthCode_none eta heta lam hlam lower hnone ⟨n,c⟩).preimage measurable_fst).inter
        ((measurableSet_evalBirthCode_none eta heta lam hlam lower hnone ⟨m,d⟩).preimage measurable_snd)

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionPoolBorelLimit
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem seed_limit_eq_mapFinite_iff {C : Type}
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (s : SeedIndex)
    (x : (fsTower eta).Carrier) (f : C → Option (ℕ × Ambient eta heta)) (A : Finset C) :
    evalSeed eta heta lam s x =
        (liftFinite (0,extraAtom 0) f A).map (finiteFiller (level eta lam)) ↔
      evalSeed eta heta lam s x = none ∧ liftFinite (0,extraAtom 0) f A = none := by
  constructor
  · intro h
    cases hs : evalSeed eta heta lam s x with
    | none =>
      refine ⟨rfl,?_⟩
      cases hF : liftFinite (0,extraAtom 0) f A with
      | none => rfl
      | some B => simp only [hs,hF,Option.map_some] at h; contradiction
    | some v =>
      cases hF : liftFinite (0,extraAtom 0) f A with
      | none => simp only [hs,hF,Option.map_none] at h; contradiction
      | some B =>
        have hv : v = finiteFiller (level eta lam) B := by
          simpa only [hs,hF,Option.map_some,Option.some.injEq] using h
        exact False.elim (evalSeed_limit_ne_filler eta heta lam hlam s x B (hs.trans (congrArg some hv)))
  · rintro ⟨hs,hF⟩
    simp only [hs,hF,Option.map_none]

theorem limitPoolCodes_borel (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (lower : ∀ b, b < lam → PoolCodes eta heta b) (htop : lam ≤ Frame.top eta)
    (hlower : ∀ b hb, PoolCodesBorel eta heta (lower b hb)) :
    PoolCodesBorel eta heta (limitPoolCodes eta heta lam hlam lower) where
  absent := by
    intro c
    cases c with
    | inl s => exact measurableSet_evalSeed_absent eta heta lam s
    | inr A =>
      change MeasurableSet {x | (liftFinite (0,extraAtom 0)
        (fun c => evalBirthCode eta heta lam hlam lower c x) A).map
        (finiteFiller (level eta lam)) = none}
      simpa only [option_map_none_iff] using
        measurableSet_liftFinite_none (0,extraAtom 0)
          (evalBirthCode eta heta lam hlam lower)
          (measurableSet_evalBirthCode_none eta heta lam hlam lower (fun b hb => (hlower b hb).absent)) A
  equal := by
    have hnone := measurableSet_evalBirthCode_none eta heta lam hlam lower
      (fun b hb => (hlower b hb).absent)
    have heq := measurableSet_evalBirthCode_equal eta heta lam hlam lower htop
      (fun b hb => (hlower b hb).absent) (fun b hb => (hlower b hb).equal)
    have hmix (s : SeedIndex) (A : Finset (BirthCode eta heta lam hlam lower)) :
        MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
          evalSeed eta heta lam s p.1 =
            (liftFinite (0,extraAtom 0) (fun c => evalBirthCode eta heta lam hlam lower c p.2) A).map
              (finiteFiller (level eta lam))} := by
      simp only [seed_limit_eq_mapFinite_iff eta heta lam hlam,setOf_and]
      exact ((measurableSet_evalSeed_absent eta heta lam s).preimage measurable_fst).inter
        ((measurableSet_liftFinite_none (0,extraAtom 0)
          (evalBirthCode eta heta lam hlam lower) hnone A).preimage measurable_snd)
    intro c d
    cases c with
    | inl s =>
      cases d with
      | inl t => exact measurableSet_evalSeed_eq eta heta lam s t
      | inr A => exact hmix s A
    | inr A =>
      cases d with
      | inl s =>
        have h := (hmix s A).preimage (measurable_swap : Measurable (Prod.swap :
          (fsTower eta).Carrier × (fsTower eta).Carrier →
          (fsTower eta).Carrier × (fsTower eta).Carrier))
        simpa only [limitPoolCodes,Sum.elim_inl,Sum.elim_inr,Set.preimage_setOf_eq,
          Prod.swap,eq_comm] using h
      | inr B =>
        exact measurableSet_map_liftFinite_eq (0,extraAtom 0)
          (evalBirthCode eta heta lam hlam lower) (evalBirthCode eta heta lam hlam lower)
          hnone hnone heq A B (finiteFiller (level eta lam)) (finiteFiller_injective _)

theorem poolCodes_borel (a : Ordinal.{0}) (ha : a ≤ Frame.top eta) :
    PoolCodesBorel eta heta (poolCodes eta heta a) := by
  induction a using Ordinal.limitRecOn with
  | zero =>
    unfold poolCodes
    rw [Ordinal.limitRecOn_zero]
    exact zeroPoolCodes_borel eta heta
  | add_one a ih =>
    unfold poolCodes
    rw [Ordinal.limitRecOn_add_one]
    exact successorPoolCodes_borel eta heta a _ (ih ((show a ≤ a+1 from le_self_add).trans ha))
  | limit lam hlam ih =>
    unfold poolCodes
    rw [Ordinal.limitRecOn_limit _ _ _ _ hlam]
    exact limitPoolCodes_borel eta heta lam hlam _ ha
      (fun b hb => ih b hb (hb.le.trans ha))

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionEnumeration
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory

namespace FSCofinality.CosetConstruction

theorem measurable_nat_count {X : Type} [MeasurableSpace X]
    (P : X → ℕ → Prop) (hP : ∀ n, MeasurableSet {x | P x n}) (k : ℕ) :
    Measurable (fun x => Nat.count (P x) k) := by
  induction k with
  | zero => simpa only [Nat.count_zero] using
      (measurable_const : Measurable (fun _ : X => (0 : ℕ)))
  | succ k ih =>
    simp only [Nat.count_succ]
    exact ih.add (Measurable.ite (hP k) measurable_const measurable_const)

theorem measurable_nat_nth {X : Type} [MeasurableSpace X]
    (P : X → ℕ → Prop) (hP : ∀ n, MeasurableSet {x | P x n})
    (hinf : ∀ x, {n | P x n}.Infinite) (k : ℕ) :
    Measurable (fun x => Nat.nth (P x) k) := by
  apply measurable_to_countable'
  intro n
  have hcount := (measurable_nat_count P hP n) (measurableSet_singleton k)
  convert (hP n).inter hcount using 1
  ext x
  change Nat.nth (P x) k = n ↔ P x n ∧ Nat.count (P x) n = k
  constructor
  · intro h
    exact ⟨h ▸ Nat.nth_mem_of_infinite (hinf x) k,
      h ▸ Nat.count_nth_of_infinite (hinf x) k⟩
  · rintro ⟨hp,hcount⟩
    rw [←hcount]
    exact Nat.nth_count hp

def FirstOccurrence {Z : Type} (F : ℕ → Option Z) (n : ℕ) : Prop :=
  F n ≠ none ∧ ∀ m < n, F m ≠ F n

theorem firstOccurrence_some {Z : Type} (F : ℕ → Option Z) {u : Z}
    (h : ∃ n, F n = some u) :
    ∃ n, FirstOccurrence F n ∧ F n = some u := by
  let n := Nat.find h
  have hn : F n = some u := Nat.find_spec h
  refine ⟨n,⟨?_,?_⟩,hn⟩
  · rw [hn]
    exact Option.some_ne_none _
  · intro m hm heq
    exact (Nat.find_min h hm) (heq.trans hn)

theorem firstOccurrence_injOn {Z : Type} (base : Z) (F : ℕ → Option Z) :
    Set.InjOn (fun n => (F n).getD base) {n | FirstOccurrence F n} := by
  intro m hm n hn heq
  have hvalue : F m = F n := by
    cases hfm : F m with
    | none => exact False.elim (hm.1 hfm)
    | some u =>
      cases hfn : F n with
      | none => exact False.elim (hn.1 hfn)
      | some v =>
        have huv : u = v := by simpa only [hfm,hfn,Option.getD_some] using heq
        exact congrArg some huv
  exact le_antisymm (le_of_not_gt (fun hlt => hm.2 n hlt hvalue.symm))
    (le_of_not_gt (fun hlt => hn.2 m hlt hvalue))

theorem firstOccurrence_infinite {Z : Type} (base : Z) (F : ℕ → Option Z)
    (hinf : {u | ∃ n, F n = some u}.Infinite) : {n | FirstOccurrence F n}.Infinite := by
  intro hfin
  have hsub : {u | ∃ n, F n = some u} ⊆
      (fun n => (F n).getD base) '' {n | FirstOccurrence F n} := by
    intro u hu
    obtain ⟨n,hn,hvalue⟩ := firstOccurrence_some F hu
    exact ⟨n,hn,by simp only [hvalue,Option.getD_some]⟩
  exact hinf ((hfin.image _).subset hsub)

theorem measurableSet_firstOccurrence {X Z : Type} [MeasurableSpace X]
    (F : ℕ → X → Option Z)
    (hnone : ∀ n, MeasurableSet {x | F n x = none})
    (heq : ∀ m n, MeasurableSet {x | F m x = F n x}) (n : ℕ) :
    MeasurableSet {x | FirstOccurrence (fun m => F m x) n} := by
  simp only [FirstOccurrence,setOf_and,setOf_forall]
  exact (hnone n).compl.inter (MeasurableSet.iInter (fun m =>
    MeasurableSet.iInter (fun _ => (heq m n).compl)))

def enumerateValues {Z : Type} (base : Z) (F : ℕ → Option Z) (k : ℕ) : Z :=
  (F (Nat.nth (FirstOccurrence F) k)).getD base

theorem enumerateValues_injective {Z : Type} (base : Z) (F : ℕ → Option Z)
    (hinf : {u | ∃ n, F n = some u}.Infinite) :
    Function.Injective (enumerateValues base F) := by
  have hg := firstOccurrence_infinite base F hinf
  intro m n h
  apply Nat.nth_injective hg
  exact firstOccurrence_injOn base F (Nat.nth_mem_of_infinite hg m)
    (Nat.nth_mem_of_infinite hg n) h

theorem enumerateValues_range {Z : Type} (base : Z) (F : ℕ → Option Z)
    (hinf : {u | ∃ n, F n = some u}.Infinite) :
    Set.range (enumerateValues base F) = {u | ∃ n, F n = some u} := by
  have hg := firstOccurrence_infinite base F hinf
  ext u
  constructor
  · rintro ⟨k,rfl⟩
    have hgood := Nat.nth_mem_of_infinite hg k
    cases hv : F (Nat.nth (FirstOccurrence F) k) with
    | none => exact False.elim (hgood.1 hv)
    | some z => exact ⟨Nat.nth (FirstOccurrence F) k,by
        simpa only [enumerateValues,hv,Option.getD_some] using hv⟩
  · intro hu
    obtain ⟨n,hn,hvalue⟩ := firstOccurrence_some F hu
    obtain ⟨k,hk⟩ := (Nat.range_nth_of_infinite hg).symm.subset hn
    exact ⟨k,by simp only [enumerateValues,hk,hvalue,Option.getD_some]⟩

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionPoolEnumeration
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def poolCodeList (a : Ordinal.{0}) : ℕ → (poolCodes eta heta a).Code := by
  letI : Nonempty (poolCodes eta heta a).Code := ⟨(poolCodes eta heta a).seed none⟩
  exact Classical.choose (exists_surjective_nat (poolCodes eta heta a).Code)

theorem poolCodeList_surjective (a : Ordinal.{0}) :
    Function.Surjective (poolCodeList eta heta a) := by
  letI : Nonempty (poolCodes eta heta a).Code := ⟨(poolCodes eta heta a).seed none⟩
  exact Classical.choose_spec (exists_surjective_nat (poolCodes eta heta a).Code)

def poolPartialList (a : Ordinal.{0}) (n : ℕ) (x : (fsTower eta).Carrier) :
    Option (Ambient eta heta) := (poolCodes eta heta a).value (poolCodeList eta heta a n) x

theorem poolPartialList_range (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    {u | ∃ n, poolPartialList eta heta a n x = some u} =
      Pool eta heta (fun b => fullSeeds eta heta b x) a := by
  ext u
  rw [←(poolCodes eta heta a).covers x u]
  constructor
  · rintro ⟨n,hn⟩
    exact ⟨_,hn⟩
  · rintro ⟨c,hc⟩
    obtain ⟨n,rfl⟩ := poolCodeList_surjective eta heta a c
    exact ⟨n,hc⟩

theorem poolPartialList_range_infinite (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    {u | ∃ n, poolPartialList eta heta a n x = some u}.Infinite := by
  rw [poolPartialList_range]
  exact Set.infinite_coe_iff.mp (pool_infinite eta heta _ a)

def poolEnumeration (a : Ordinal.{0}) (x : (fsTower eta).Carrier) (k : ℕ) : Ambient eta heta :=
  enumerateValues (extraAtom 0) (fun n => poolPartialList eta heta a n x) k

theorem poolEnumeration_injective (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    Function.Injective (poolEnumeration eta heta a x) :=
  enumerateValues_injective _ _ (poolPartialList_range_infinite eta heta a x)

theorem poolEnumeration_range (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    Set.range (poolEnumeration eta heta a x) =
      Pool eta heta (fun b => fullSeeds eta heta b x) a :=
  (enumerateValues_range _ _ (poolPartialList_range_infinite eta heta a x)).trans
    (poolPartialList_range eta heta a x)

def poolEnumerationEquiv (a : Ordinal.{0}) (x : (fsTower eta).Carrier) :
    ℕ ≃ Pool eta heta (fun b => fullSeeds eta heta b x) a :=
  Equiv.ofBijective
    (fun n => ⟨poolEnumeration eta heta a x n,(poolEnumeration_range eta heta a x).le ⟨n,rfl⟩⟩)
    ⟨fun _ _ h => poolEnumeration_injective eta heta a x (congrArg Subtype.val h),by
      intro u
      obtain ⟨n,hn⟩ := (poolEnumeration_range eta heta a x).symm.le u.property
      exact ⟨n,Subtype.ext hn⟩⟩

def poolEnumerationIndex (a : Ordinal.{0}) (x : (fsTower eta).Carrier) (k : ℕ) : ℕ :=
  Nat.nth (FirstOccurrence (fun n => poolPartialList eta heta a n x)) k

theorem measurable_poolEnumerationIndex (a : Ordinal.{0}) (ha : a ≤ Frame.top eta) (k : ℕ) :
    Measurable (fun x => poolEnumerationIndex eta heta a x k) := by
  apply measurable_nat_nth
  · intro n
    apply measurableSet_firstOccurrence
    · intro m
      exact (poolCodes_borel eta heta a ha).absent (poolCodeList eta heta a m)
    · intro m n
      exact ((poolCodes_borel eta heta a ha).equal
        (poolCodeList eta heta a m) (poolCodeList eta heta a n)).preimage
        (measurable_id.prodMk measurable_id)
  · intro x
    exact firstOccurrence_infinite (extraAtom 0) _ (poolPartialList_range_infinite eta heta a x)

theorem poolEnumerationIndex_value (a : Ordinal.{0}) (x : (fsTower eta).Carrier) (k : ℕ) :
    poolPartialList eta heta a (poolEnumerationIndex eta heta a x k) x =
      some (poolEnumeration eta heta a x k) := by
  have hgood := Nat.nth_mem_of_infinite
    (firstOccurrence_infinite (extraAtom 0) _ (poolPartialList_range_infinite eta heta a x)) k
  cases h : poolPartialList eta heta a (poolEnumerationIndex eta heta a x k) x with
  | none => exact False.elim (hgood.1 h)
  | some z => simp only [poolEnumeration,enumerateValues,poolEnumerationIndex] at *
              simp only [h,Option.getD_some]

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionBottomValues
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

/-- The genuine standard Borel bottom raw space, with its two tagged kinds
of atoms. No measurable structure is placed on the semantic universe. -/
abbrev BottomValueSpace := (ℕ → Bool) ⊕ ℕ

instance bottomValueSpace_standardBorel : StandardBorelSpace BottomValueSpace := standardBorel_sum

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def atomObject : BottomValueSpace → Ambient eta heta := Sum.elim sourceAtom extraAtom

theorem atomObject_injective : Function.Injective (atomObject eta heta) := by
  intro u v h
  rcases u with u | u <;> rcases v with v | v
  · exact congrArg Sum.inl (sourceAtom_injective h)
  · exact False.elim (sourceAtom_ne_extraAtom u v h)
  · exact False.elim (sourceAtom_ne_extraAtom v u h.symm)
  · exact congrArg Sum.inr (extraAtom_injective h)

theorem atomObject_mem_valid (v : BottomValueSpace) : atomObject eta heta v ∈ Valid eta heta 0 := by
  rw [valid_zero]
  cases v with
  | inl r => exact Or.inl ⟨r,rfl⟩
  | inr n => exact Or.inr ⟨n,rfl⟩

def atomEquiv : BottomValueSpace ≃ Valid eta heta 0 :=
  Equiv.ofBijective (fun v => ⟨atomObject eta heta v,atomObject_mem_valid eta heta v⟩)
    ⟨fun _ _ h => atomObject_injective eta heta (congrArg Subtype.val h),by
      intro u
      have hu : u.val ∈ (range sourceAtom ∪ range extraAtom : Set (Ambient eta heta)) := by
        simpa only [valid_zero] using u.property
      rcases hu with ⟨r,hr⟩ | ⟨n,hn⟩
      · exact ⟨Sum.inl r,Subtype.ext hr⟩
      · exact ⟨Sum.inr n,Subtype.ext hn⟩⟩

@[simp] theorem atomEquiv_apply_val (v : BottomValueSpace) :
    (atomEquiv eta heta v).val = atomObject eta heta v := rfl

def bottomValue : Valid eta heta 0 → BottomValueSpace := (atomEquiv eta heta).symm

theorem bottomValue_injective : Function.Injective (bottomValue eta heta) :=
  (atomEquiv eta heta).symm.injective

@[simp] theorem bottomValue_atomObject (v : BottomValueSpace) :
    bottomValue eta heta ⟨atomObject eta heta v,atomObject_mem_valid eta heta v⟩ = v :=
  (atomEquiv eta heta).symm_apply_apply v

@[simp] theorem atomObject_bottomValue (u : Valid eta heta 0) :
    atomObject eta heta (bottomValue eta heta u) = u.val :=
  congrArg Subtype.val ((atomEquiv eta heta).apply_symm_apply u)

/-- A total semantic decoder, whose values outside the bottom layer are
irrelevant to the construction. -/
def decodeAtom (u : Ambient eta heta) : BottomValueSpace :=
  if h : u ∈ Valid eta heta 0 then bottomValue eta heta ⟨u,h⟩ else .inr 0

@[simp] theorem decodeAtom_atomObject (v : BottomValueSpace) :
    decodeAtom eta heta (atomObject eta heta v) = v := by
  rw [decodeAtom,dif_pos (atomObject_mem_valid eta heta v)]
  exact bottomValue_atomObject eta heta v

@[simp] theorem decodeAtom_sourceAtom (r : ℕ → Bool) :
    decodeAtom eta heta (sourceAtom r) = .inl r := decodeAtom_atomObject eta heta (.inl r)

@[simp] theorem decodeAtom_extraAtom (n : ℕ) :
    decodeAtom eta heta (extraAtom n) = .inr n := decodeAtom_atomObject eta heta (.inr n)

theorem decodeAtom_eq_bottomValue (u : Valid eta heta 0) :
    decodeAtom eta heta u.val = bottomValue eta heta u := by
  simp only [decodeAtom,dif_pos u.property]

theorem atomObject_decodeAtom_of_valid (u : Ambient eta heta) (hu : u ∈ Valid eta heta 0) :
    atomObject eta heta (decodeAtom eta heta u) = u := by
  rw [decodeAtom_eq_bottomValue eta heta ⟨u,hu⟩]
  exact atomObject_bottomValue eta heta ⟨u,hu⟩

theorem decodeAtom_injOn : InjOn (decodeAtom eta heta) (Valid eta heta 0) := by
  intro u hu v hv huv
  exact (atomObject_decodeAtom_of_valid eta heta u hu).symm.trans
    ((congrArg (atomObject eta heta) huv).trans (atomObject_decodeAtom_of_valid eta heta v hv))

def decodeOptionalAtom : Option (Ambient eta heta) → Unit ⊕ BottomValueSpace
  | none => .inl ()
  | some u => .inr (decodeAtom eta heta u)

theorem measurable_decodeOptional_optionalTranslate_zero :
    Measurable (fun z : Unit ⊕ (fsTower 0).Carrier =>
      decodeOptionalAtom eta heta (optionalTranslate eta heta 0 z)) := by
  have hm : Measurable (fun y : (fsTower 0).Carrier =>
      (Sum.inr (Sum.inl (codeCast fsTower_zero y)) : Unit ⊕ BottomValueSpace)) :=
    measurable_inr.comp (measurable_inl.comp (codeCast fsTower_zero).measurable)
  have h := (measurable_const : Measurable (fun _ : Unit =>
    (Sum.inl () : Unit ⊕ BottomValueSpace))).sumElim hm
  convert h using 1
  funext z
  cases z with
  | inl u => cases u; rfl
  | inr y =>
    simp only [optionalTranslate,translate_zero,decodeOptionalAtom,decodeAtom_sourceAtom,codeCast_apply]
    rfl

theorem measurable_decodeOptional_sourcePathValue (p : List ℕ)
    (hp : (sourcePath eta p).rank = 0) :
    Measurable (fun x => decodeOptionalAtom eta heta (sourcePathValue eta heta p x)) := by
  let f := Sum.map id (codeCast (congrArg fsTower hp)) ∘ (sourcePath eta p).get
  have hf : Measurable f :=
    (measurable_id.sumMap (codeCast _).measurable).comp (sourcePath eta p).measurable_get
  convert (measurable_decodeOptional_optionalTranslate_zero eta heta).comp hf using 1
  funext x
  exact congrArg (decodeOptionalAtom eta heta)
    (optionalTranslate_cast eta heta hp ((sourcePath eta p).get x)).symm

theorem measurable_decodeOptional_evalSeed_zero (s : SeedIndex) :
    Measurable (fun x => decodeOptionalAtom eta heta (evalSeed eta heta 0 s x)) := by
  cases s with
  | none =>
    have ht : (0 : Ordinal.{0}) ≠ Frame.top eta :=
      ne_of_lt (lt_of_le_of_lt zero_le (Frame.lt_top eta))
    simpa only [evalSeed,if_neg ht,decodeOptionalAtom] using
      (measurable_const : Measurable (fun _ : (fsTower eta).Carrier =>
        (Sum.inl () : Unit ⊕ BottomValueSpace)))
  | some p =>
    by_cases hp : (sourcePath eta p).rank = 0
    · simpa only [evalSeed,if_pos hp] using measurable_decodeOptional_sourcePathValue eta heta p hp
    · simpa only [evalSeed,if_neg hp,decodeOptionalAtom] using
        (measurable_const : Measurable (fun _ : (fsTower eta).Carrier =>
          (Sum.inl () : Unit ⊕ BottomValueSpace)))

theorem measurable_decodeOptional_zeroPoolCodes (c : (zeroPoolCodes eta heta).Code) :
    Measurable (fun x => decodeOptionalAtom eta heta ((zeroPoolCodes eta heta).value c x)) := by
  cases c with
  | inl s => exact measurable_decodeOptional_evalSeed_zero eta heta s
  | inr n => exact measurable_const

theorem measurable_decodeOptional_poolCodes_zero (c : (poolCodes eta heta 0).Code) :
    Measurable (fun x => decodeOptionalAtom eta heta ((poolCodes eta heta 0).value c x)) := by
  have htransfer (P : PoolCodes eta heta 0) (hP : P = zeroPoolCodes eta heta) :
      ∀ c : P.Code, Measurable (fun x => decodeOptionalAtom eta heta (P.value c x)) := by
    cases hP
    exact measurable_decodeOptional_zeroPoolCodes eta heta
  exact htransfer _ (poolCodes_zero eta heta) c

theorem measurable_decodeOptional_poolPartialList_zero (n : ℕ) :
    Measurable (fun x => decodeOptionalAtom eta heta (poolPartialList eta heta 0 n x)) :=
  measurable_decodeOptional_poolCodes_zero eta heta _

/-- The actual bottom pool enumeration has a Borel native bottom value. -/
theorem measurable_decodeAtom_poolEnumeration_zero (k : ℕ) :
    Measurable (fun x => decodeAtom eta heta (poolEnumeration eta heta 0 x k)) := by
  let f : (fsTower eta).Carrier × ℕ → Unit ⊕ BottomValueSpace :=
    fun p => decodeOptionalAtom eta heta (poolPartialList eta heta 0 p.2 p.1)
  have hf : Measurable f := measurable_from_prod_countable_left
    (fun n => measurable_decodeOptional_poolPartialList_zero eta heta n)
  have hs : Measurable (fun x => (x,poolEnumerationIndex eta heta 0 x k)) :=
    measurable_id.prodMk (measurable_poolEnumerationIndex eta heta 0 zero_le k)
  let getValue : Unit ⊕ BottomValueSpace → BottomValueSpace := Sum.elim (fun _ => .inr 0) id
  have hg : Measurable getValue := measurable_const.sumElim measurable_id
  convert hg.comp (hf.comp hs) using 1
  funext x
  change decodeAtom eta heta (poolEnumeration eta heta 0 x k) =
    getValue (decodeOptionalAtom eta heta
      (poolPartialList eta heta 0 (poolEnumerationIndex eta heta 0 x k) x))
  rw [poolEnumerationIndex_value]
  rfl

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionTokenModelProperties
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem bottom_raw_valid (x : (fsTower eta).Carrier) (u : raw eta heta x (zeroSort eta)) :
    u.val ∈ Valid eta heta 0 := by
  have h := pool_subset_valid eta heta _ (fun a => fullSeeds_typed eta heta a x)
    (Frame.rank (Frame.ofOrdinal eta 0 zero_le)) u.property
  simpa only [Frame.rank_ofOrdinal] using h

def decodedBottom (x : (fsTower eta).Carrier) (v : Token (raw eta heta x (zeroSort eta))) :
    Token BottomValueSpace := (v.1.map (fun u => decodeAtom eta heta u.val),v.2)

def bottom (x : (fsTower eta).Carrier) (v : Token (raw eta heta x (zeroSort eta))) : ℕ → Bool :=
  bottomListMap (decodedBottom eta heta x v).1 v.2

def rawName (x : (fsTower eta).Carrier) : (s : TokenSort eta) → raw eta heta x s → Ambient eta heta
  | .inl _,u => u.val
  | .inr (lam,n),u => encodeColumn eta heta _ lam.property (lowerPools eta heta x _) n u

def tokenName (x : (fsTower eta).Carrier) (s : TokenSort eta) (v : Token (raw eta heta x s)) :
    Token (Ambient eta heta) := mapToken (rawName eta heta x s) v

theorem rawName_injective (x : (fsTower eta).Carrier) (s : TokenSort eta) :
    Function.Injective (rawName eta heta x s) := by
  cases s with
  | inl a => exact Subtype.val_injective
  | inr c => exact encodeColumn_injective eta heta _ c.1.property _ (Frame.rank_le_top c.1.val) c.2

theorem tokenName_injective (x : (fsTower eta).Carrier) (s : TokenSort eta) :
    Function.Injective (tokenName eta heta x s) := by
  intro v w h
  apply Prod.ext
  · exact List.map_injective_iff.mpr (rawName_injective eta heta x s) (congrArg Prod.fst h)
  · exact congrArg (fun z : Token (Ambient eta heta) => z.2) h

theorem decodedBottom_reencode (x : (fsTower eta).Carrier)
    (v : Token (raw eta heta x (zeroSort eta))) :
    mapToken (atomObject eta heta) (decodedBottom eta heta x v) =
      tokenName eta heta x (zeroSort eta) v := by
  apply Prod.ext
  · simp only [mapToken,decodedBottom,tokenName,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro u _
    exact atomObject_decodeAtom_of_valid eta heta u.val (bottom_raw_valid eta heta x u)
  · rfl

theorem bottom_recovers_name (x y : (fsTower eta).Carrier)
    (v : Token (raw eta heta x (zeroSort eta))) (w : Token (raw eta heta y (zeroSort eta)))
    (h : bottom eta heta x v = bottom eta heta y w) :
    tokenName eta heta x (zeroSort eta) v = tokenName eta heta y (zeroSort eta) w := by
  have hd : decodedBottom eta heta x v = decodedBottom eta heta y w := bottomListMap_injective h
  exact (decodedBottom_reencode eta heta x v).symm.trans
    ((congrArg (mapToken (atomObject eta heta)) hd).trans (decodedBottom_reencode eta heta y w))

@[simp] theorem tokenAt_inr (x : (fsTower eta).Carrier) (s : TokenSort eta)
    (v : Token (raw eta heta x s)) : tokenAt eta heta s (.inr ⟨s,v⟩) = some v := by
  simp [tokenAt]

@[simp] theorem tokenAt_inl (x : (fsTower eta).Carrier) (s : TokenSort eta) (n : ℕ) :
    tokenAt eta heta s (.inl n : Vertex eta heta x) = none := rfl

@[simp] theorem edgeAt_inr (x : (fsTower eta).Carrier) (s t : TokenSort eta)
    (f : Token (raw eta heta x s) → Token (raw eta heta x t) → Bool)
    (v : Token (raw eta heta x s)) (w : Token (raw eta heta x t)) :
    edgeAt eta heta s t f (.inr ⟨s,v⟩) (.inr ⟨t,w⟩) = f v w := by simp [edgeAt]

def tokenFiberEquiv (x : (fsTower eta).Carrier) (s : TokenSort eta) :
    Token (raw eta heta x s) ≃ {v : Vertex eta heta x // sortOf eta heta v = some s} :=
  Equiv.ofBijective (fun v => ⟨.inr ⟨s,v⟩,rfl⟩) ⟨by
    intro v w h
    have h' := Sum.inr.inj (congrArg Subtype.val h)
    exact eq_of_heq (Sigma.mk.inj_iff.mp h').2,by
    rintro ⟨v,hv⟩
    cases v with
    | inl n => simp [sortOf] at hv
    | inr v =>
      rcases v with ⟨t,v⟩
      have ht : t=s := Option.some.inj hv
      subst t
      exact ⟨v,rfl⟩⟩

def sortedTokenEquiv {x y : (fsTower eta).Carrier} (e : Vertex eta heta x ≃ Vertex eta heta y)
    (hsort : ∀ v, sortOf eta heta (e v) = sortOf eta heta v) (s : TokenSort eta) :
    Token (raw eta heta x s) ≃ Token (raw eta heta y s) :=
  ((tokenFiberEquiv eta heta x s).trans
    (e.subtypeEquiv (fun v => by rw [hsort v]))).trans (tokenFiberEquiv eta heta y s).symm

theorem sortedTokenEquiv_commutes {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (hsort : ∀ v, sortOf eta heta (e v) = sortOf eta heta v) (s : TokenSort eta)
    (v : Token (raw eta heta x s)) :
    e (.inr ⟨s,v⟩) = .inr ⟨s,sortedTokenEquiv eta heta e hsort s v⟩ := by
  have h := (tokenFiberEquiv eta heta y s).apply_symm_apply
    ((e.subtypeEquiv (fun v => by rw [hsort v])) (tokenFiberEquiv eta heta x s v))
  exact (congrArg Subtype.val h).symm

theorem preserves_sort {x y : (fsTower eta).Carrier}
    (b : ∀ x : (fsTower eta).Carrier, Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : ∀ s a, diagram eta heta b x s a = diagram eta heta b y s (e ∘ a))
    (v : Vertex eta heta x) : sortOf eta heta (e v) = sortOf eta heta v := by
  have h := he (.inl (sortOf eta heta v)) (fun _ => v)
  change decide (sortOf eta heta v = sortOf eta heta v) =
    decide (sortOf eta heta (e v) = sortOf eta heta v) at h
  exact of_decide_eq_true (h.symm.trans (decide_eq_true rfl))

theorem preserves_ordinary {x y : (fsTower eta).Carrier}
    (b : ∀ x : (fsTower eta).Carrier, Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : ∀ s a, diagram eta heta b x s a = diagram eta heta b y s (e ∘ a))
    (r : OrdinaryRole eta) (v : Token (raw eta heta x (rowSort eta r)))
    (w : Token (raw eta heta x (colSort eta r))) :
    ordinary eta heta x r v w = ordinary eta heta y r
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (rowSort eta r) v)
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (colSort eta r) w) := by
  have h := he (.inr (.inl r)) ![.inr ⟨rowSort eta r,v⟩,.inr ⟨colSort eta r,w⟩]
  change edgeAt eta heta _ _ (ordinary eta heta x r) (.inr ⟨_,v⟩) (.inr ⟨_,w⟩) =
    edgeAt eta heta _ _ (ordinary eta heta y r) (e (.inr ⟨_,v⟩)) (e (.inr ⟨_,w⟩)) at h
  rw [sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he),
    sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he)] at h
  simpa only [edgeAt_inr] using h

theorem preserves_branch {x y : (fsTower eta).Carrier}
    (b : ∀ x : (fsTower eta).Carrier, Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : ∀ s a, diagram eta heta b x s a = diagram eta heta b y s (e ∘ a))
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inl lam.val)))
    (w : Token (raw eta heta x (.inr (lam,n)))) :
    branch eta heta x lam n v w = branch eta heta y lam n
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (.inl lam.val) v)
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (.inr (lam,n)) w) := by
  have h := he (.inr (.inr (.inl (lam,n)))) ![.inr ⟨.inl lam.val,v⟩,.inr ⟨.inr (lam,n),w⟩]
  change edgeAt eta heta _ _ (branch eta heta x lam n) (.inr ⟨_,v⟩) (.inr ⟨_,w⟩) =
    edgeAt eta heta _ _ (branch eta heta y lam n) (e (.inr ⟨_,v⟩)) (e (.inr ⟨_,w⟩)) at h
  rw [sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he),
    sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he)] at h
  simpa only [edgeAt_inr] using h

theorem preserves_limit_R {x y : (fsTower eta).Carrier}
    (b : ∀ x : (fsTower eta).Carrier, Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : ∀ s a, diagram eta heta b x s a = diagram eta heta b y s (e ∘ a))
    (lam : LimitIndex eta) (n : ℕ) (v w : Token (raw eta heta x (.inl lam.val))) :
    R (limitProfile eta heta x lam) n v w ↔ R (limitProfile eta heta y lam) n
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (.inl lam.val) v)
      (sortedTokenEquiv eta heta e (preserves_sort eta heta b e he) (.inl lam.val) w) := by
  have h := he (.inr (.inr (.inr (.inl (lam,n))))) ![.inr ⟨.inl lam.val,v⟩,.inr ⟨.inl lam.val,w⟩]
  change edgeAt eta heta _ _ (fun r t => decide (R (limitProfile eta heta x lam) n r t))
      (.inr ⟨_,v⟩) (.inr ⟨_,w⟩) =
    edgeAt eta heta _ _ (fun r t => decide (R (limitProfile eta heta y lam) n r t))
      (e (.inr ⟨_,v⟩)) (e (.inr ⟨_,w⟩)) at h
  rw [sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he),
    sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta b e he)] at h
  exact decide_eq_decide.mp (by simpa only [edgeAt_inr] using h)

theorem qFixed_bottom_name {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : ∀ s a, diagram eta heta (bottom eta heta) x s a =
      diagram eta heta (bottom eta heta) y s (e ∘ a))
    (hQ : ∀ n, e (.inl n) = .inl n)
    (v : Token (raw eta heta x (zeroSort eta))) :
    tokenName eta heta x (zeroSort eta) v = tokenName eta heta y (zeroSort eta)
      (sortedTokenEquiv eta heta e (preserves_sort eta heta (bottom eta heta) e he) (zeroSort eta) v) := by
  apply bottom_recovers_name
  funext n
  have h := he (.inr (.inr (.inr (.inr ())))) ![.inr ⟨zeroSort eta,v⟩,.inl n]
  change (tokenAt eta heta (zeroSort eta) (.inr ⟨_,v⟩)).elim false
      (fun r => (coordinateAt eta heta (.inl n)).elim false (bottom eta heta x r)) =
    (tokenAt eta heta (zeroSort eta) (e (.inr ⟨_,v⟩))).elim false
      (fun r => (coordinateAt eta heta (e (.inl n))).elim false (bottom eta heta y r)) at h
  rw [sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta (bottom eta heta) e he),hQ] at h
  simpa only [tokenAt_inr,coordinateAt,Option.elim_some] using h

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.CosetConstructionModelEnumeration
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

abbrev Template := ℕ ⊕ Σ s : TokenSort eta, Token ℕ

instance template_countable : Countable (Template eta) := by
  letI := sort_countable eta heta
  exact inferInstanceAs (Countable (ℕ ⊕ Σ _s : TokenSort eta, List ℕ × ℕ))

instance template_infinite : Infinite (Template eta) :=
  Infinite.of_injective (Sum.inl : ℕ → Template eta) Sum.inl_injective

def templateEnumeration : ℕ ≃ Template eta := by
  letI := template_countable eta heta
  exact Classical.choice (inferInstanceAs (Nonempty (ℕ ≃ Template eta)))

def tokenEquiv {U V : Type} (e : U ≃ V) : Token U ≃ Token V :=
  Equiv.prodCongr (Equiv.listEquivOfEquiv e) (Equiv.refl ℕ)

theorem tokenEquiv_apply {U V : Type} (e : U ≃ V) (v : Token U) :
    tokenEquiv e v = mapToken e v := rfl

def templateVertexEquiv (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) : Template eta ≃ Vertex eta heta x :=
  Equiv.sumCongr (Equiv.refl ℕ) (Equiv.sigmaCongrRight (fun s => tokenEquiv (e s)))

theorem templateVertexEquiv_coordinate (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) (n : ℕ) :
    templateVertexEquiv eta heta x e (.inl n) = .inl n := rfl

theorem templateVertexEquiv_token (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) (s : TokenSort eta) (v : Token ℕ) :
    templateVertexEquiv eta heta x e (.inr ⟨s,v⟩) = .inr ⟨s,mapToken (e s) v⟩ := rfl

def vertexEnumeration (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (x : (fsTower eta).Carrier) : ℕ ≃ Vertex eta heta x :=
  (templateEnumeration eta heta).trans (templateVertexEquiv eta heta x (e x))

theorem vertexEnumeration_coordinate_preimage
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (x : (fsTower eta).Carrier) (n : ℕ) :
    (vertexEnumeration eta heta e x).symm (.inl n) =
      (templateEnumeration eta heta).symm (.inl n) := by
  apply (vertexEnumeration eta heta e x).injective
  simp only [Equiv.apply_symm_apply,vertexEnumeration,Equiv.trans_apply,
    Equiv.apply_symm_apply,templateVertexEquiv_coordinate]

theorem measurable_vertexEnumeration_coordinate_preimage
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s) (n : ℕ) :
    Measurable (fun x => (vertexEnumeration eta heta e x).symm (.inl n)) := by
  simp only [vertexEnumeration_coordinate_preimage]
  exact measurable_const

def templateTokenAt (s : TokenSort eta) : Template eta → Option (Token ℕ)
  | .inl _ => none
  | .inr ⟨t,v⟩ => if t=s then some v else none

def templateCoordinateAt : Template eta → Option ℕ
  | .inl n => some n
  | .inr _ => none

def templateSortOf : Template eta → Option (TokenSort eta)
  | .inl _ => none
  | .inr ⟨s,_⟩ => some s

theorem tokenAt_templateVertexEquiv (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) (s : TokenSort eta) (v : Template eta) :
    tokenAt eta heta s (templateVertexEquiv eta heta x e v) =
      (templateTokenAt eta s v).map (mapToken (e s)) := by
  rcases v with n|⟨t,v⟩
  · rfl
  · by_cases h : t=s
    · subst t
      simp [templateVertexEquiv_token,tokenAt,templateTokenAt]
    · simp only [templateVertexEquiv_token,tokenAt,templateTokenAt,dif_neg h,if_neg h,Option.map_none]

theorem coordinateAt_templateVertexEquiv (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) (v : Template eta) :
    coordinateAt eta heta (templateVertexEquiv eta heta x e v) = templateCoordinateAt eta v := by
  rcases v with n|⟨s,v⟩ <;> rfl

theorem sortOf_templateVertexEquiv (x : (fsTower eta).Carrier)
    (e : ∀ s, ℕ ≃ raw eta heta x s) (v : Template eta) :
    sortOf eta heta (templateVertexEquiv eta heta x e v) = templateSortOf eta v := by
  rcases v with n|⟨s,v⟩ <;> rfl

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.CosetConstructionSelectionBorel
section


set_option autoImplicit false
noncomputable section
open Set

namespace FSCofinality.CosetConstruction

theorem measurableSet_selected {X C : Type} [MeasurableSpace X]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]
    (P : C → X → Prop) (hP : ∀ c, MeasurableSet {x | P c x})
    (f : X → C) (hf : Measurable f) : MeasurableSet {x | P (f x) x} := by
  have heq : {x | P (f x) x} = ⋃ c, ({x | f x = c} ∩ {x | P c x}) := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion,mem_inter_iff]
    exact ⟨fun h => ⟨f x,rfl,h⟩,fun ⟨c,hc,h⟩ => hc ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun c => (hf (measurableSet_singleton c)).inter (hP c))

theorem measurableSet_selected₂ {X C D : Type} [MeasurableSpace X]
    [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D]
    (P : C → D → X → Prop) (hP : ∀ c d, MeasurableSet {x | P c d x})
    (f : X → C) (g : X → D) (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | P (f x) (g x) x} := by
  apply measurableSet_selected (fun c x => P c (g x) x) _ f hf
  intro c
  exact measurableSet_selected (P c) (hP c) g hg

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionModelBorel
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem boolMatrix_ext (M N : BoolMatrix) (hl : M.1=N.1) (hm : M.2.1=N.2.1)
    (he : ∀ i j, M.entry i j = N.entry i j) : M=N := by
  rcases M with ⟨l,m,f⟩
  rcases N with ⟨l',m',g⟩
  dsimp only at hl hm
  subst l'
  subst m'
  apply congrArg (fun k => (⟨l,m,k⟩ : BoolMatrix))
  funext i j
  have h := he i.val j.val
  simpa only [BoolMatrix.entry,dif_pos i.isLt,dif_pos j.isLt] using h

theorem contextMatrix_map_normal {U V : Type} (R : U → V → Bool) (v : List U) (w : List V) :
    contextMatrix (v.map R) w =
      ⟨v.length,w.length,fun i j => R v[i] w[j]⟩ := by
  apply boolMatrix_ext
  · exact List.length_map _
  · rfl
  · intro i j
    by_cases hi : i<v.length <;> by_cases hj : j<w.length <;>
      simp [contextMatrix,BoolMatrix.entry,hi,hj]

theorem ordinaryEdge_mapToken_both {U V W Z : Type}
    (A : Table) (e : ℕ) (R : W → Z → Bool) (f : U → W) (g : V → Z)
    (v : Token U) (w : Token V) :
    ordinaryEdge A e R (mapToken f v) (mapToken g w) =
      ordinaryEdge A e (fun u v => R (f u) (g v)) v w := by
  simp only [ordinaryEdge,mapToken]
  apply congrArg (fun M => A (e,M,w.2,v.2))
  apply boolMatrix_ext
  · simp [contextMatrix]
  · simp [contextMatrix]
  · intro i j
    by_cases hi : i<v.1.length <;> by_cases hj : j<w.1.length <;>
      simp [contextMatrix,BoolMatrix.entry,hi,hj]

theorem branchEdge_mapToken_both {U V : Type} {Col D : ℕ → Type}
    (A : Table) (e n : ℕ) (P : ∀ n, V → D n → Bool)
    (f : U → V) (g : ∀ n, Col n → D n) (v : Token U) (w : Token (Col n)) :
    branchEdge P A e n (mapToken f v) (mapToken (g n) w) =
      branchEdge (fun n u c => P n (f u) (g n c)) A e n v w := by
  simp only [branchEdge,activeProfiles]
  rw [activeTuple_mapToken,localCode_mapToken]
  simp only [mapToken]
  apply congrArg (fun M => A (e,M,w.2,localCode v n))
  apply boolMatrix_ext
  · simp [contextMatrix]
  · simp [contextMatrix]
  · intro i j
    by_cases hi : i<(activeTuple v n).length <;> by_cases hj : j<w.1.length <;>
      simp [contextMatrix,BoolMatrix.entry,hi,hj]

theorem measurable_ordinaryEdge {X : Type} [MeasurableSpace X]
    (A : Table) (e : ℕ) (R : X → ℕ → ℕ → Bool)
    (hR : ∀ i j, Measurable (fun x => R x i j)) (v w : Token ℕ) :
    Measurable (fun x => ordinaryEdge A e (R x) v w) := by
  let M (x : X) : Fin v.1.length → Fin w.1.length → Bool := fun i j => R x v.1[i] w.1[j]
  have hM : Measurable M := measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => hR _ _))
  let F (m : Fin v.1.length → Fin w.1.length → Bool) := A (e,⟨v.1.length,w.1.length,m⟩,w.2,v.2)
  convert (measurable_of_countable F).comp hM using 1
  funext x
  simp only [ordinaryEdge,contextMatrix_map_normal]
  rfl

theorem measurable_branchEdge {X : Type} [MeasurableSpace X]
    (A : Table) (e n : ℕ) (P : X → ℕ → ℕ → ℕ → Bool)
    (hP : ∀ n i j, Measurable (fun x => P x n i j)) (v w : Token ℕ) :
    Measurable (fun x => branchEdge (P x) A e n v w) := by
  let M (x : X) : Fin (activeTuple v n).length → Fin w.1.length → Bool :=
    fun i j => P x n (activeTuple v n)[i] w.1[j]
  have hM : Measurable M := measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => hP _ _ _))
  let F (m : Fin (activeTuple v n).length → Fin w.1.length → Bool) :=
    A (e,⟨(activeTuple v n).length,w.1.length,m⟩,w.2,localCode v n)
  convert (measurable_of_countable F).comp hM using 1
  funext x
  simp only [branchEdge,activeProfiles,contextMatrix_map_normal]
  rfl

theorem measurable_edgeAt_templates
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (s t : TokenSort eta)
    (f : ∀ x, Token (raw eta heta x s) → Token (raw eta heta x t) → Bool)
    (hf : ∀ v w : Token ℕ, Measurable (fun x => f x (mapToken (e x s) v) (mapToken (e x t) w)))
    (u v : Template eta) :
    Measurable (fun x => edgeAt eta heta s t (f x)
      (templateVertexEquiv eta heta x (e x) u) (templateVertexEquiv eta heta x (e x) v)) := by
  simp only [edgeAt,tokenAt_templateVertexEquiv]
  cases hu : templateTokenAt eta s u with
  | none => simpa only [Option.map_none,Option.elim_none] using
      (measurable_const : Measurable (fun _ : (fsTower eta).Carrier => false))
  | some a =>
    cases hv : templateTokenAt eta t v with
    | none => simpa only [Option.map_some,Option.map_none,Option.elim_some,Option.elim_none] using
        (measurable_const : Measurable (fun _ : (fsTower eta).Carrier => false))
    | some b => simpa only [Option.map_some,Option.elim_some] using hf a b

theorem measurable_ordinary_templates
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (hO : ∀ r i j, Measurable (fun x => ordinaryMatrix eta heta x r
      (e x (rowSort eta r) i) (e x (colSort eta r) j)))
    (r : OrdinaryRole eta) (v w : Token ℕ) :
    Measurable (fun x => ordinary eta heta x r
      (mapToken (e x (rowSort eta r)) v) (mapToken (e x (colSort eta r)) w)) := by
  simp only [ordinary,ordinaryEdge_mapToken_both]
  exact measurable_ordinaryEdge genericTable _ _ (hO r) v w

theorem measurable_branch_templates
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (hP : ∀ lam n i j, Measurable (fun x => limitProfile eta heta x lam n
      (e x (.inl lam.val) i) (e x (.inr (lam,n)) j)))
    (lam : LimitIndex eta) (n : ℕ) (v w : Token ℕ) :
    Measurable (fun x => branch eta heta x lam n
      (mapToken (e x (.inl lam.val)) v) (mapToken (e x (.inr (lam,n))) w)) := by
  have h := measurable_branchEdge genericTable (roleNumber eta heta (.inr (lam,n))) n
    (fun x m i j => limitProfile eta heta x lam m
      (e x (.inl lam.val) i) (e x (.inr (lam,m)) j)) (hP lam) v w
  convert h using 1
  funext x
  exact branchEdge_mapToken_both genericTable _ n (limitProfile eta heta x lam)
    (e x (.inl lam.val)) (fun m => e x (.inr (lam,m))) v w

theorem measurable_R_templates
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (hP : ∀ lam n i j, Measurable (fun x => limitProfile eta heta x lam n
      (e x (.inl lam.val) i) (e x (.inr (lam,n)) j)))
    (lam : LimitIndex eta) (n : ℕ) (v w : Token ℕ) :
    Measurable (fun x => decide (R (limitProfile eta heta x lam) n
      (mapToken (e x (.inl lam.val)) v) (mapToken (e x (.inl lam.val)) w))) := by
  apply measurable_to_bool
  change MeasurableSet {x : (fsTower eta).Carrier | decide (R (limitProfile eta heta x lam) n
    (mapToken (e x (.inl lam.val)) v) (mapToken (e x (.inl lam.val)) w)) = true}
  simp only [decide_eq_true_eq]
  have hiff (x : (fsTower eta).Carrier) :
      R (limitProfile eta heta x lam) n (mapToken (e x (.inl lam.val)) v)
        (mapToken (e x (.inl lam.val)) w) ↔
      ∀ c : Token ℕ, branch eta heta x lam n (mapToken (e x (.inl lam.val)) v)
          (mapToken (e x (.inr (lam,n))) c) =
        branch eta heta x lam n (mapToken (e x (.inl lam.val)) w)
          (mapToken (e x (.inr (lam,n))) c) := by
    rw [R_iff_branch_neighborhood _ genericTable_generic (roleNumber eta heta (.inr (lam,n))) n]
    constructor
    · exact fun h c => h (mapToken (e x (.inr (lam,n))) c)
    · intro h c
      obtain ⟨d,hd⟩ := (tokenEquiv (e x (.inr (lam,n)))).surjective c
      change mapToken (e x (.inr (lam,n))) d = c at hd
      simpa only [branch,hd] using h d
  simp only [hiff,setOf_forall]
  exact MeasurableSet.iInter (fun c => measurableSet_eq_fun
    (measurable_branch_templates eta heta e hP lam n v c)
    (measurable_branch_templates eta heta e hP lam n w c))

theorem measurable_diagram_templates
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (hO : ∀ r i j, Measurable (fun x => ordinaryMatrix eta heta x r
      (e x (rowSort eta r) i) (e x (colSort eta r) j)))
    (hP : ∀ lam n i j, Measurable (fun x => limitProfile eta heta x lam n
      (e x (.inl lam.val) i) (e x (.inr (lam,n)) j)))
    (hB : ∀ v : Token ℕ, ∀ n, Measurable (fun x => bottom eta heta x
      (mapToken (e x (zeroSort eta)) v) n))
    (s : Symbol eta) (a : Fin (arity eta s) → Template eta) :
    Measurable (fun x => diagram eta heta (bottom eta heta) x s
      (templateVertexEquiv eta heta x (e x) ∘ a)) := by
  rcases s with s|r|⟨lam,n⟩|⟨lam,n⟩|unit
  · simp only [diagram,Function.comp_apply,sortOf_templateVertexEquiv]
    exact measurable_const
  · change Fin 2 → Template eta at a
    exact measurable_edgeAt_templates eta heta e _ _ (fun x => ordinary eta heta x r)
      (measurable_ordinary_templates eta heta e hO r) (a 0) (a 1)
  · change Fin 2 → Template eta at a
    exact measurable_edgeAt_templates eta heta e _ _ (fun x => branch eta heta x lam n)
      (measurable_branch_templates eta heta e hP lam n) (a 0) (a 1)
  · change Fin 2 → Template eta at a
    exact measurable_edgeAt_templates eta heta e _ _
      (fun x v w => decide (R (limitProfile eta heta x lam) n v w))
      (measurable_R_templates eta heta e hP lam n) (a 0) (a 1)
  · change Fin 2 → Template eta at a
    simp only [diagram,Function.comp_apply,tokenAt_templateVertexEquiv,coordinateAt_templateVertexEquiv]
    cases ht : templateTokenAt eta (zeroSort eta) (a 0) with
    | none => simpa only [Option.map_none,Option.elim_none] using
        (measurable_const : Measurable (fun _ : (fsTower eta).Carrier => false))
    | some v =>
      cases hn : templateCoordinateAt eta (a 1) with
      | none => simpa only [Option.map_some,Option.elim_some,Option.elim_none] using
          (measurable_const : Measurable (fun _ : (fsTower eta).Carrier => false))
      | some n => simpa only [Option.map_some,Option.elim_some] using hB v n

theorem measurable_modelWithTemplateEnumeration
    (e : ∀ x : (fsTower eta).Carrier, ∀ s, ℕ ≃ raw eta heta x s)
    (hO : ∀ r i j, Measurable (fun x => ordinaryMatrix eta heta x r
      (e x (rowSort eta r) i) (e x (colSort eta r) j)))
    (hP : ∀ lam n i j, Measurable (fun x => limitProfile eta heta x lam n
      (e x (.inl lam.val) i) (e x (.inr (lam,n)) j)))
    (hB : ∀ v : Token ℕ, ∀ n, Measurable (fun x => bottom eta heta x
      (mapToken (e x (zeroSort eta)) v) n)) :
    Measurable (fun x => modelWithEnumeration eta heta (bottom eta heta) x
      (vertexEnumeration eta heta e x)) := by
  change @Measurable (fsTower eta).Carrier (Coordinate (language eta heta) → Bool)
    (fsTower eta).measurableSpace (borel (Coordinate (language eta heta) → Bool)) _
  rw [← BorelSpace.measurable_eq (α := Coordinate (language eta heta) → Bool)]
  apply measurable_pi_iff.mpr
  intro c
  exact measurable_diagram_templates eta heta e hO hP hB c.1
    (templateEnumeration eta heta ∘ c.2)

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.CosetConstructionCodeOperations
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- A single code, fixed before the source input is supplied, realizes the
specified partial semantic operation. -/
def CodeRep (a : Ordinal.{0}) (F : (fsTower eta).Carrier → Option (Ambient eta heta)) : Prop :=
  ∃ c : (poolCodes eta heta a).Code, ∀ x, (poolCodes eta heta a).value c x = F x

theorem codeRep_value (a : Ordinal.{0}) (c : (poolCodes eta heta a).Code) :
    CodeRep eta heta a ((poolCodes eta heta a).value c) := ⟨c,fun _ => rfl⟩

theorem codeRep_congr (a : Ordinal.{0})
    {F G : (fsTower eta).Carrier → Option (Ambient eta heta)}
    (hF : CodeRep eta heta a F) (h : ∀ x, F x = G x) : CodeRep eta heta a G := by
  obtain ⟨c,hc⟩ := hF
  exact ⟨c,fun x => (hc x).trans (h x)⟩

theorem codeRep_seed (a : Ordinal.{0}) (s : SeedIndex) :
    CodeRep eta heta a (evalSeed eta heta a s) :=
  ⟨(poolCodes eta heta a).seed s,(poolCodes eta heta a).value_seed s⟩

theorem codeRep_none (a : Ordinal.{0}) :
    CodeRep eta heta a (fun _ => none) := by
  by_cases ha : a = Frame.top eta
  · apply codeRep_congr eta heta a (codeRep_seed eta heta a (some []))
    intro x
    have hne : eta ≠ a := by rw [ha]; exact ne_of_lt (Frame.lt_top eta)
    simp only [evalSeed,sourcePath,if_neg hne]
  · apply codeRep_congr eta heta a (codeRep_seed eta heta a none)
    intro x
    simp only [evalSeed,if_neg ha]

theorem codeRep_extra (n : ℕ) :
    CodeRep eta heta 0 (fun _ => some (extraAtom n)) := by
  unfold CodeRep
  rw [poolCodes_zero]
  exact ⟨.inr n,fun _ => rfl⟩

theorem codeRep_singleton (a : Ordinal.{0})
    (F : (fsTower eta).Carrier → Option (Ambient eta heta)) (hF : CodeRep eta heta a F) :
    CodeRep eta heta (a+1) (fun x => (F x).map (singleton (level eta (a+1)))) := by
  obtain ⟨c,hc⟩ := hF
  unfold CodeRep
  rw [poolCodes_add_one]
  refine ⟨.inr {c},?_⟩
  intro x
  change (liftFinite (extraAtom 0) (fun d => (poolCodes eta heta a).value d x) {c}).map _ = _
  cases h : F x <;> simp [liftFinite,hc x,h,finiteCollection_singleton]

theorem codeRep_doubleton (a : Ordinal.{0})
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (G : (fsTower eta).Carrier → Ambient eta heta)
    (hF : CodeRep eta heta a F) (hG : CodeRep eta heta a (fun x => some (G x))) :
    CodeRep eta heta (a+1) (fun x => (F x).map (fun u => doubleton (level eta (a+1)) u (G x))) := by
  obtain ⟨c,hc⟩ := hF
  obtain ⟨d,hd⟩ := hG
  unfold CodeRep
  rw [poolCodes_add_one]
  refine ⟨.inr {c,d},?_⟩
  intro x
  change (liftFinite (extraAtom 0) (fun e => (poolCodes eta heta a).value e x) {c,d}).map _ = _
  cases h : F x <;> simp [liftFinite,hc x,hd x,h,finiteCollection_doubleton]

theorem codeRep_limit_singleton (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (n : ℕ)
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (hF : CodeRep eta heta (Frame.rho eta lam hlam n) F) :
    CodeRep eta heta lam (fun x => (F x).map (fun u => finiteFiller (level eta lam)
      {(n,singleton (level eta (Frame.delta eta lam hlam n)) u)})) := by
  obtain ⟨c,hc⟩ := hF
  unfold CodeRep
  rw [poolCodes_limit eta heta lam hlam]
  let b : BirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) := ⟨n,.inr (.inr c)⟩
  refine ⟨.inr {b},?_⟩
  intro x
  change (liftFinite (0,extraAtom 0) (fun e => evalBirthCode eta heta lam hlam _ e x) {b}).map _ = _
  have hb : evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) b x =
      (F x).map (fun u => (n,singleton (level eta (Frame.delta eta lam hlam n)) u)) := by
    change ((poolCodes eta heta (Frame.rho eta lam hlam n)).value c x).map _ = _
    rw [hc]
  cases h : F x <;> simp [liftFinite,hb,h]

theorem codeRep_lift (b a : Ordinal.{0}) (hba : b ≤ a) (ha : a ≤ Frame.top eta)
    (F : (fsTower eta).Carrier → Option (Ambient eta heta)) (hF : CodeRep eta heta b F) :
    CodeRep eta heta a (fun x => (F x).map (lift eta heta b a)) := by
  induction a using Ordinal.limitRecOn generalizing b with
  | zero =>
    have hb : b = 0 := le_antisymm hba zero_le
    subst b
    simpa only [lift_self,Option.map_id] using hF
  | add_one a ih =>
    by_cases hb : b = a+1
    · subst b
      simpa only [lift_self,Option.map_id] using hF
    · have hba' : b ≤ a := lt_add_one_iff.mp (lt_of_le_of_ne hba hb)
      have ha' : a ≤ Frame.top eta := (show a ≤ a+1 from le_self_add).trans ha
      have hrec := ih b hba' ha' hF
      have hs := codeRep_singleton eta heta a _ hrec
      simpa only [RawObjects.lift_add_one,if_neg hb,Option.map_map,Function.comp_def] using hs
  | limit lam hlam ih =>
    by_cases hb : b = lam
    · subst b
      simpa only [lift_self,Option.map_id] using hF
    · have hblt : b < lam := lt_of_le_of_ne hba hb
      let n := liftIndex eta heta lam hlam ha b hblt
      have hrec := ih (Frame.rho eta lam hlam n) (Frame.rho_lt eta lam hlam n)
        b (liftIndex_spec eta heta lam hlam ha b hblt)
        ((Frame.rho_lt eta lam hlam n).le.trans ha) hF
      have hs := codeRep_limit_singleton eta heta lam hlam n _ hrec
      simpa only [lift_limit eta heta lam hlam ha b hblt,Option.map_map,Function.comp_def] using hs

theorem codeRep_tag (a : Ordinal.{0}) (ha : a ≤ Frame.top eta) (n : ℕ) :
    CodeRep eta heta a (fun _ => some (tag eta heta a n)) := by
  simpa only [Option.map_some,tag] using
    codeRep_lift eta heta 0 a zero_le ha (fun _ => some (extraAtom n)) (codeRep_extra eta heta n)

theorem codeRep_doubleton_left (a : Ordinal.{0})
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (G : (fsTower eta).Carrier → Ambient eta heta)
    (hF : CodeRep eta heta a F) (hG : CodeRep eta heta a (fun x => some (G x))) :
    CodeRep eta heta (a+1) (fun x => (F x).map (fun u => doubleton (level eta (a+1)) (G x) u)) := by
  apply codeRep_congr eta heta (a+1) (codeRep_doubleton eta heta a F G hF hG)
  intro x
  exact congrArg (fun f => (F x).map f) (funext (fun u => doubleton_comm _ u (G x)))

theorem codeRep_enc (a : Ordinal.{0})
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (T B : (fsTower eta).Carrier → Ambient eta heta)
    (hF : CodeRep eta heta a F)
    (hT : CodeRep eta heta a (fun x => some (T x)))
    (hB : CodeRep eta heta a (fun x => some (B x))) :
    CodeRep eta heta (a+2) (fun x => (F x).map
      (Enc (level eta (a+1)) (level eta (a+2)) (T x) (B x))) := by
  have hpair := codeRep_doubleton_left eta heta a F B hF hB
  have htag : CodeRep eta heta (a+1) (fun x => some (singleton (level eta (a+1)) (T x))) := by
    simpa only [Option.map_some] using codeRep_singleton eta heta a (fun x => some (T x)) hT
  have hout := codeRep_doubleton_left eta heta (a+1) _ _ hpair htag
  have hstage : a+1+1 = a+2 := by rw [add_assoc,one_add_one_eq_two]
  simpa only [hstage,Option.map_map,Function.comp_def,Enc] using hout

theorem codeRep_dataColumn (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta) (n : ℕ)
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (hF : CodeRep eta heta (Frame.q eta lam hlam n) F) :
    CodeRep eta heta (Frame.delta eta lam hlam n)
      (fun x => (F x).map (dataColumn eta heta lam hlam n)) := by
  have hs : Frame.sigma eta lam hlam n ≤ Frame.top eta := (Frame.sigma_lt eta lam hlam n).le.trans htop
  have hlift := codeRep_lift eta heta _ _ (Frame.q_le_sigma eta lam hlam n) hs F hF
  have henc := codeRep_enc eta heta (Frame.sigma eta lam hlam n) _
    (fun _ => tag eta heta (Frame.sigma eta lam hlam n) 1)
    (fun _ => tag eta heta (Frame.sigma eta lam hlam n) 3) hlift
    (codeRep_tag eta heta _ hs 1) (codeRep_tag eta heta _ hs 3)
  simpa only [Frame.delta,Frame.rho,Option.map_map,Function.comp_def,dataColumn] using henc

theorem codeRep_markerColumn (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta) (n : ℕ) :
    CodeRep eta heta (Frame.delta eta lam hlam n)
      (fun _ => some (markerColumn eta heta lam hlam n)) := by
  have hs : Frame.sigma eta lam hlam n ≤ Frame.top eta := (Frame.sigma_lt eta lam hlam n).le.trans htop
  simpa only [Frame.delta,Frame.rho,Option.map_some,markerColumn] using
    codeRep_enc eta heta (Frame.sigma eta lam hlam n) (fun _ => some (tag eta heta _ 3))
      (fun _ => tag eta heta _ 2) (fun _ => tag eta heta _ 3)
      (codeRep_tag eta heta _ hs 3) (codeRep_tag eta heta _ hs 2) (codeRep_tag eta heta _ hs 3)

theorem codeRep_oldColumn (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta) (n : ℕ)
    (F : (fsTower eta).Carrier → Option (Ambient eta heta))
    (hF : CodeRep eta heta (Frame.delta eta lam hlam n) F) :
    CodeRep eta heta (Frame.delta eta lam hlam (n+1))
      (fun x => (F x).map (oldColumn eta heta lam hlam n)) := by
  have hs : Frame.sigma eta lam hlam (n+1) ≤ Frame.top eta :=
    (Frame.sigma_lt eta lam hlam (n+1)).le.trans htop
  have hlift := codeRep_lift eta heta _ _ (Frame.delta_le_sigma_next eta lam hlam n) hs F hF
  have henc := codeRep_enc eta heta (Frame.sigma eta lam hlam (n+1)) _
    (fun _ => tag eta heta (Frame.sigma eta lam hlam (n+1)) 0)
    (fun _ => tag eta heta (Frame.sigma eta lam hlam (n+1)) 3) hlift
    (codeRep_tag eta heta _ hs 0) (codeRep_tag eta heta _ hs 3)
  simpa only [Frame.delta,Frame.rho,Option.map_map,Function.comp_def,oldColumn] using henc

theorem codeRep_birthColumn (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta)
    (c : BirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a)) :
    CodeRep eta heta (Frame.delta eta lam hlam c.1) (fun x =>
      (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c x).map Prod.snd) := by
  rcases c with ⟨n,c⟩
  rcases c with c|⟨⟨⟩⟩|c
  · simpa only [evalBirthCode,Option.map_map,Function.comp_def] using
      codeRep_dataColumn eta heta lam hlam htop n _ (codeRep_value eta heta _ c)
  · simpa only [evalBirthCode,Option.map_some] using
      codeRep_markerColumn eta heta lam hlam htop n
  · have hstage : Frame.rho eta lam hlam n + 1 = Frame.delta eta lam hlam n := by
      simp only [Frame.rho,Frame.delta,add_assoc,one_add_one_eq_two]
    simpa only [evalBirthCode,Option.map_map,Function.comp_def,hstage] using
      codeRep_singleton eta heta (Frame.rho eta lam hlam n) _ (codeRep_value eta heta _ c)

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionCodeRepBorel
section


noncomputable section
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem measurableSet_codeRep_none (a : Ordinal.{0}) (ha : a ≤ Frame.top eta)
    {F : (fsTower eta).Carrier → Option (Ambient eta heta)} (hF : CodeRep eta heta a F) :
    MeasurableSet {x | F x = none} := by
  obtain ⟨c,hc⟩ := hF
  simpa only [hc] using (poolCodes_borel eta heta a ha).absent c

theorem measurableSet_codeRep_eq (a : Ordinal.{0}) (ha : a ≤ Frame.top eta)
    {F G : (fsTower eta).Carrier → Option (Ambient eta heta)}
    (hF : CodeRep eta heta a F) (hG : CodeRep eta heta a G) :
    MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier | F p.1 = G p.2} := by
  obtain ⟨c,hc⟩ := hF
  obtain ⟨d,hd⟩ := hG
  simpa only [hc,hd] using (poolCodes_borel eta heta a ha).equal c d

theorem measurableSet_codeRep_eq_diagonal (a : Ordinal.{0}) (ha : a ≤ Frame.top eta)
    {F G : (fsTower eta).Carrier → Option (Ambient eta heta)}
    (hF : CodeRep eta heta a F) (hG : CodeRep eta heta a G) :
    MeasurableSet {x : (fsTower eta).Carrier | F x = G x} :=
  (measurableSet_codeRep_eq eta heta a ha hF hG).preimage (measurable_id.prodMk measurable_id)

theorem measurableSet_codeRep_eq_poolEnumeration (a : Ordinal.{0}) (ha : a ≤ Frame.top eta)
    {F : (fsTower eta).Carrier → Option (Ambient eta heta)} (hF : CodeRep eta heta a F) (k : ℕ) :
    MeasurableSet {x : (fsTower eta).Carrier | F x = some (poolEnumeration eta heta a x k)} := by
  have h := measurableSet_selected (fun n x => F x = poolPartialList eta heta a n x)
    (fun n => measurableSet_codeRep_eq_diagonal eta heta a ha hF
      (codeRep_value eta heta a (poolCodeList eta heta a n)))
    (fun x => poolEnumerationIndex eta heta a x k)
    (measurable_poolEnumerationIndex eta heta a ha k)
  simpa only [poolEnumerationIndex_value] using h

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionColumnCodes
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)

abbrev ColumnCode (n : ℕ) :=
  {c : BirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) // c.1 ≤ n}

instance columnCode_countable (n : ℕ) : Countable (ColumnCode eta heta lam hlam n) := inferInstance
instance columnCode_nonempty (n : ℕ) : Nonempty (ColumnCode eta heta lam hlam n) :=
  ⟨⟨⟨0,.inr (.inl ())⟩,Nat.zero_le n⟩⟩

def evalColumnCode : (n : ℕ) → ColumnCode eta heta lam hlam n →
    (fsTower eta).Carrier → Option (Ambient eta heta)
  | 0,⟨⟨k,c⟩,hk⟩,x =>
      (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a)
        ⟨0,(Nat.eq_zero_of_le_zero hk) ▸ c⟩ x).map Prod.snd
  | n+1,c,x => if h : c.val.1 = n+1 then
      (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x).map Prod.snd
    else (evalColumnCode n ⟨c.val,by have hc := c.property; omega⟩ x).map
      (oldColumn eta heta lam hlam n)

theorem evalColumnCode_fresh (n : ℕ)
    (c : (poolCodes eta heta (Frame.q eta lam hlam n)).Code ⊕
      (Unit ⊕ (poolCodes eta heta (Frame.rho eta lam hlam n)).Code))
    (x : (fsTower eta).Carrier) :
    evalColumnCode eta heta lam hlam n ⟨⟨n,c⟩,le_rfl⟩ x =
      (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) ⟨n,c⟩ x).map Prod.snd := by
  cases n <;> simp [evalColumnCode]

theorem evalColumnCode_propagate (n : ℕ) (c : ColumnCode eta heta lam hlam n)
    (x : (fsTower eta).Carrier) :
    evalColumnCode eta heta lam hlam (n+1) ⟨c.val,Nat.le_succ_of_le c.property⟩ x =
      (evalColumnCode eta heta lam hlam n c x).map (oldColumn eta heta lam hlam n) := by
  have h : c.val.1 ≠ n+1 := Nat.ne_of_lt (Nat.lt_succ_of_le c.property)
  simp only [evalColumnCode,dif_neg h]

theorem codeRep_columnCode (htop : lam ≤ Frame.top eta) (n : ℕ)
    (c : ColumnCode eta heta lam hlam n) :
    CodeRep eta heta (Frame.delta eta lam hlam n) (evalColumnCode eta heta lam hlam n c) := by
  induction n with
  | zero =>
    rcases c with ⟨⟨k,c⟩,hk⟩
    have hk0 : k=0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact codeRep_birthColumn eta heta lam hlam htop ⟨0,c⟩
  | succ n ih =>
    by_cases h : c.val.1=n+1
    · have hb := codeRep_birthColumn eta heta lam hlam htop c.val
      simpa only [evalColumnCode,dif_pos h,h] using hb
    · let d : ColumnCode eta heta lam hlam n := ⟨c.val,by have hc := c.property; omega⟩
      have hb := codeRep_oldColumn eta heta lam hlam htop n _ (ih d)
      simpa only [evalColumnCode,dif_neg h] using hb

private theorem evalBirthCode_map_snd (n : ℕ)
    (c : (poolCodes eta heta (Frame.q eta lam hlam n)).Code ⊕
      (Unit ⊕ (poolCodes eta heta (Frame.rho eta lam hlam n)).Code))
    (x : (fsTower eta).Carrier) (z : Ambient eta heta) :
    (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) ⟨n,c⟩ x).map Prod.snd = some z ↔
      evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) ⟨n,c⟩ x = some (n,z) := by
  rcases c with c | ⟨⟨⟩⟩ | c
  · cases h : (poolCodes eta heta (Frame.q eta lam hlam n)).value c x <;>
      simp only [evalBirthCode,h,Option.map_none,Option.map_some,Option.some.injEq,
        reduceCtorEq,Prod.mk.injEq,true_and]
  · simp only [evalBirthCode,Option.map_some,Option.some.injEq,Prod.mk.injEq,true_and]
  · cases h : (poolCodes eta heta (Frame.rho eta lam hlam n)).value c x <;>
      simp only [evalBirthCode,h,Option.map_none,Option.map_some,Option.some.injEq,
        reduceCtorEq,Prod.mk.injEq,true_and]

theorem evalBirthCode_some_fst (c : BirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a))
    (x : (fsTower eta).Carrier) (p : ℕ × Ambient eta heta)
    (h : evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c x = some p) : p.1=c.1 := by
  rcases c with ⟨n,c⟩
  rcases c with c | ⟨⟨⟩⟩ | c
  · cases hv : (poolCodes eta heta (Frame.q eta lam hlam n)).value c x with
    | none => simp only [evalBirthCode,hv,Option.map_none] at h; contradiction
    | some z =>
      have he : (n,dataColumn eta heta lam hlam n z)=p := by
        simpa only [evalBirthCode,hv,Option.map_some,Option.some.injEq] using h
      exact (congrArg Prod.fst he).symm
  · exact (congrArg Prod.fst (Option.some.inj h)).symm
  · cases hv : (poolCodes eta heta (Frame.rho eta lam hlam n)).value c x with
    | none => simp only [evalBirthCode,hv,Option.map_none] at h; contradiction
    | some z =>
      have he : (n,singleton (level eta (Frame.delta eta lam hlam n)) z)=p := by
        simpa only [evalBirthCode,hv,Option.map_some,Option.some.injEq] using h
      exact (congrArg Prod.fst he).symm

theorem evalColumnCode_covers (n : ℕ) (x : (fsTower eta).Carrier) (z : Ambient eta heta) :
    (∃ c, evalColumnCode eta heta lam hlam n c x = some z) ↔
      z ∈ ColumnSet eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n := by
  induction n generalizing z with
  | zero =>
    rw [columnSet_zero]
    constructor
    · rintro ⟨⟨⟨k,c⟩,hk⟩,hc⟩
      have hk0 : k=0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact (evalBirthCode_covers eta heta lam hlam (fun a _ => poolCodes eta heta a) x (0,z)).mp
        ⟨⟨0,c⟩,(evalBirthCode_map_snd eta heta lam hlam 0 c x z).mp hc⟩
    · intro hz
      obtain ⟨⟨k,c⟩,hc⟩ :=
        (evalBirthCode_covers eta heta lam hlam (fun a _ => poolCodes eta heta a) x (0,z)).mpr hz
      have hk : 0=k := evalBirthCode_some_fst eta heta lam hlam ⟨k,c⟩ x (0,z) hc
      subst k
      exact ⟨⟨⟨0,c⟩,le_rfl⟩,(evalBirthCode_map_snd eta heta lam hlam 0 c x z).mpr hc⟩
  | succ n ih =>
    rw [columnSet_succ]
    constructor
    · rintro ⟨c,hc⟩
      by_cases h : c.val.1=n+1
      · have hbc : (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x).map
            Prod.snd = some z := by simpa only [evalColumnCode,dif_pos h] using hc
        rcases c with ⟨⟨k,c⟩,hk⟩
        change k=n+1 at h
        subst k
        exact Or.inr ((evalBirthCode_covers eta heta lam hlam (fun a _ => poolCodes eta heta a)
          x (n+1,z)).mp ⟨⟨n+1,c⟩,(evalBirthCode_map_snd eta heta lam hlam _ c x z).mp hbc⟩)
      · let d : ColumnCode eta heta lam hlam n := ⟨c.val,by have hd := c.property; omega⟩
        rw [evalColumnCode,dif_neg h] at hc
        change (evalColumnCode eta heta lam hlam n d x).map _ = some z at hc
        cases hv : evalColumnCode eta heta lam hlam n d x with
        | none => simp only [hv,Option.map_none] at hc; contradiction
        | some u =>
          have hu : oldColumn eta heta lam hlam n u=z := by
            simpa only [hv,Option.map_some,Option.some.injEq] using hc
          exact Or.inl ⟨u,(ih u).mp ⟨d,hv⟩,hu⟩
    · rintro (⟨u,hu,rfl⟩ | hz)
      · obtain ⟨c,hc⟩ := (ih u).mpr hu
        exact ⟨⟨c.val,Nat.le_succ_of_le c.property⟩,by rw [evalColumnCode_propagate,hc]; rfl⟩
      · obtain ⟨⟨k,c⟩,hc⟩ :=
          (evalBirthCode_covers eta heta lam hlam (fun a _ => poolCodes eta heta a) x (n+1,z)).mpr hz
        have hk : n+1=k := evalBirthCode_some_fst eta heta lam hlam ⟨k,c⟩ x (n+1,z) hc
        subst k
        exact ⟨⟨⟨n+1,c⟩,le_rfl⟩,by
          rw [evalColumnCode_fresh]
          exact (evalBirthCode_map_snd eta heta lam hlam _ c x z).mpr hc⟩

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionColumnEnumeration
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta) (n : ℕ)

def columnCodeList : ℕ → ColumnCode eta heta lam hlam n :=
  Classical.choose (exists_surjective_nat (ColumnCode eta heta lam hlam n))

theorem columnCodeList_surjective : Function.Surjective (columnCodeList eta heta lam hlam n) :=
  Classical.choose_spec (exists_surjective_nat (ColumnCode eta heta lam hlam n))

def columnPartialList (i : ℕ) (x : (fsTower eta).Carrier) : Option (Ambient eta heta) :=
  evalColumnCode eta heta lam hlam n (columnCodeList eta heta lam hlam n i) x

theorem columnPartialList_range (x : (fsTower eta).Carrier) :
    {u | ∃ i, columnPartialList eta heta lam hlam n i x = some u} =
      ColumnSet eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n := by
  ext u
  rw [← evalColumnCode_covers]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨_,hi⟩
  · rintro ⟨c,hc⟩
    obtain ⟨i,rfl⟩ := columnCodeList_surjective eta heta lam hlam n c
    exact ⟨i,hc⟩

theorem column_infinite (x : (fsTower eta).Carrier) :
    Infinite (Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) := by
  letI : Infinite (TokenModel.mainPool eta heta x (Frame.rho eta lam hlam n)) :=
    pool_infinite eta heta (fun b => fullSeeds eta heta b x) (Frame.rho eta lam hlam n)
  let f : TokenModel.mainPool eta heta x (Frame.rho eta lam hlam n) →
      Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n :=
    fun c => freshColumn eta heta lam hlam _ n (.inr (.inr c))
  apply Infinite.of_injective f
  intro c d h
  have he := congrArg (encodeColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) h
  simp only [f,encodeColumn_fresh,encodeNew] at he
  exact Subtype.ext ((singleton_eq_iff _ _ _).mp he)

include htop

theorem columnPartialList_range_infinite (x : (fsTower eta).Carrier) :
    {u | ∃ i, columnPartialList eta heta lam hlam n i x = some u}.Infinite := by
  rw [columnPartialList_range]
  letI := column_infinite eta heta lam hlam n x
  exact Set.infinite_range_of_injective (encodeColumn_injective eta heta lam hlam _ htop n)

def columnEnumeration (x : (fsTower eta).Carrier) (k : ℕ) : Ambient eta heta :=
  enumerateValues (extraAtom 0) (fun i => columnPartialList eta heta lam hlam n i x) k

theorem columnEnumeration_injective (x : (fsTower eta).Carrier) :
    Function.Injective (columnEnumeration eta heta lam hlam n x) :=
  enumerateValues_injective _ _ (columnPartialList_range_infinite eta heta lam hlam htop n x)

theorem columnEnumeration_range (x : (fsTower eta).Carrier) :
    range (columnEnumeration eta heta lam hlam n x) =
      ColumnSet eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n :=
  (enumerateValues_range _ _ (columnPartialList_range_infinite eta heta lam hlam htop n x)).trans
    (columnPartialList_range eta heta lam hlam n x)

def columnEnumerationRaw (x : (fsTower eta).Carrier) (k : ℕ) :
    Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n :=
  ((columnEnumeration_range eta heta lam hlam htop n x).le ⟨k,rfl⟩).choose

theorem encodeColumn_columnEnumerationRaw (x : (fsTower eta).Carrier) (k : ℕ) :
    encodeColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n
      (columnEnumerationRaw eta heta lam hlam htop n x k) = columnEnumeration eta heta lam hlam n x k :=
  ((columnEnumeration_range eta heta lam hlam htop n x).le ⟨k,rfl⟩).choose_spec

def columnEnumerationEquiv (x : (fsTower eta).Carrier) :
    ℕ ≃ Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n :=
  Equiv.ofBijective (columnEnumerationRaw eta heta lam hlam htop n x)
    ⟨by
      intro i j hij
      apply columnEnumeration_injective eta heta lam hlam htop n x
      exact (encodeColumn_columnEnumerationRaw eta heta lam hlam htop n x i).symm.trans
        ((congrArg (encodeColumn eta heta lam hlam _ n) hij).trans
          (encodeColumn_columnEnumerationRaw eta heta lam hlam htop n x j)),by
      intro c
      obtain ⟨k,hk⟩ := (columnEnumeration_range eta heta lam hlam htop n x).symm.le ⟨c,rfl⟩
      refine ⟨k,encodeColumn_injective eta heta lam hlam _ htop n ?_⟩
      exact (encodeColumn_columnEnumerationRaw eta heta lam hlam htop n x k).trans hk⟩

def columnEnumerationIndex (x : (fsTower eta).Carrier) (k : ℕ) : ℕ :=
  Nat.nth (FirstOccurrence (fun i => columnPartialList eta heta lam hlam n i x)) k

theorem measurable_columnEnumerationIndex (k : ℕ) :
    Measurable (fun x => columnEnumerationIndex eta heta lam hlam n x k) := by
  have hd : Frame.delta eta lam hlam n ≤ Frame.top eta := (Frame.delta_lt eta lam hlam n).le.trans htop
  apply measurable_nat_nth
  · intro i
    apply measurableSet_firstOccurrence
    · intro j
      exact measurableSet_codeRep_none eta heta _ hd
        (codeRep_columnCode eta heta lam hlam htop n (columnCodeList eta heta lam hlam n j))
    · intro j k
      exact measurableSet_codeRep_eq_diagonal eta heta _ hd
        (codeRep_columnCode eta heta lam hlam htop n (columnCodeList eta heta lam hlam n j))
        (codeRep_columnCode eta heta lam hlam htop n (columnCodeList eta heta lam hlam n k))
  · intro x
    exact firstOccurrence_infinite (extraAtom 0) _ (columnPartialList_range_infinite eta heta lam hlam htop n x)

theorem columnEnumerationIndex_value (x : (fsTower eta).Carrier) (k : ℕ) :
    columnPartialList eta heta lam hlam n (columnEnumerationIndex eta heta lam hlam n x k) x =
      some (columnEnumeration eta heta lam hlam n x k) := by
  have hgood := Nat.nth_mem_of_infinite
    (firstOccurrence_infinite (extraAtom 0) _ (columnPartialList_range_infinite eta heta lam hlam htop n x)) k
  cases h : columnPartialList eta heta lam hlam n (columnEnumerationIndex eta heta lam hlam n x k) x with
  | none => exact False.elim (hgood.1 h)
  | some z =>
    simp only [columnEnumeration,enumerateValues,columnEnumerationIndex] at *
    simp only [h,Option.getD_some]

theorem measurableSet_codeRep_eq_columnEnumeration
    {F : (fsTower eta).Carrier → Option (Ambient eta heta)}
    (hF : CodeRep eta heta (Frame.delta eta lam hlam n) F) (k : ℕ) :
    MeasurableSet {x | F x = some (columnEnumeration eta heta lam hlam n x k)} := by
  have hd : Frame.delta eta lam hlam n ≤ Frame.top eta := (Frame.delta_lt eta lam hlam n).le.trans htop
  have h := measurableSet_selected (fun i x => F x = columnPartialList eta heta lam hlam n i x)
    (fun i => measurableSet_codeRep_eq_diagonal eta heta _ hd hF
      (codeRep_columnCode eta heta lam hlam htop n (columnCodeList eta heta lam hlam n i)))
    (fun x => columnEnumerationIndex eta heta lam hlam n x k)
    (measurable_columnEnumerationIndex eta heta lam hlam htop n k)
  simpa only [columnEnumerationIndex_value eta heta lam hlam htop n] using h

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionSeedCoordinates
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def seedCoordinate (lam : Ordinal.{0}) (s : SeedIndex) (n : ℕ)
    (x : (fsTower eta).Carrier) : Option (Ambient eta heta) :=
  match s with
  | none => if lam = Frame.top eta then some (topCoordinates eta heta x n) else none
  | some p => if (sourcePath eta p).rank = lam then sourcePathValue eta heta (n::p) x else none

theorem sourcePathValue_child (p : List ℕ) (x : (fsTower eta).Carrier)
    (y : (fsTower (sourcePath eta p).rank).Carrier)
    (hy : (sourcePath eta p).get x = .inr y) (n : ℕ) :
    sourcePathValue eta heta (n::p) x = codeChildValue eta heta (sourcePath eta p).rank n y := by
  simp only [sourcePathValue,sourcePath,Function.comp_apply,hy,Sum.elim_inr,codeChildValue]

theorem codeRep_seedCoordinate (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta) (s : SeedIndex) (n : ℕ) :
    CodeRep eta heta (Frame.q eta lam hlam n) (seedCoordinate eta heta lam s n) := by
  cases s with
  | none =>
    by_cases ha : lam = Frame.top eta
    · subst lam
      rw [Frame.q_top]
      by_cases hn : n = 0
      · subst n
        simp only [Nat.cast_zero,add_zero]
        apply codeRep_congr eta heta eta (codeRep_seed eta heta eta (some []))
        intro x
        simp [seedCoordinate,topCoordinates,evalSeed,sourcePath,sourcePathValue,optionalTranslate]
      · apply codeRep_congr eta heta (eta+n)
          (codeRep_tag eta heta (eta+n) (eta_add_nat_le_top eta n) 4)
        intro x
        simp [seedCoordinate,topCoordinates,hn]
    · apply codeRep_congr eta heta _ (codeRep_none eta heta _)
      intro x
      simp only [seedCoordinate,if_neg ha]
  | some p =>
    by_cases hp : (sourcePath eta p).rank = lam
    · have hle : lam ≤ eta := hp ▸ (sourcePath eta p).rank_le
      have hq : Frame.q eta lam hlam n = fundamentalSequence lam hlam n :=
        congrFun (Frame.q_of_le_source eta lam hlam hle) n
      have hchild : (sourcePath eta (n::p)).rank = Frame.q eta lam hlam n := by
        change (codeChildren (sourcePath eta p).rank).rank n = _
        rw [hp,codeChildren_limit_rank,hq]
      apply codeRep_congr eta heta _ (codeRep_seed eta heta _ (some (n::p)))
      intro x
      simp only [evalSeed,if_pos hchild,seedCoordinate,if_pos hp]
    · apply codeRep_congr eta heta _ (codeRep_none eta heta _)
      intro x
      simp only [seedCoordinate,if_neg hp]

theorem seedCoordinate_absent_iff (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (s : SeedIndex) (n : ℕ) (x : (fsTower eta).Carrier) :
    seedCoordinate eta heta lam s n x = none ↔ evalSeed eta heta lam s x = none := by
  cases s with
  | none => by_cases ha : lam = Frame.top eta <;> simp [seedCoordinate,evalSeed,ha]
  | some p =>
    by_cases hp : (sourcePath eta p).rank = lam
    · simp only [seedCoordinate,evalSeed,if_pos hp]
      cases hy : (sourcePath eta p).get x with
      | inl unit => simp [sourcePathValue,sourcePath,optionalTranslate,hy]
      | inr y =>
        obtain ⟨z,hz,hchildren⟩ := limit_value_children eta heta _ lam hp hlam y
        rw [sourcePathValue_child eta heta p x y hy n,(hchildren n).1]
        simp [sourcePathValue,optionalTranslate,hy]
    · simp only [seedCoordinate,evalSeed,if_neg hp]

theorem seedCoordinate_source (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (s : SeedIndex) (n : ℕ) (x : (fsTower eta).Carrier) (z : ℕ → Ambient eta heta)
    (hv : evalSeed eta heta lam s x = some (sourceSequence (level eta lam) z)) :
    seedCoordinate eta heta lam s n x = some (z n) := by
  cases s with
  | none =>
    by_cases ha : lam = Frame.top eta
    · have heq : topSource eta heta x = sourceSequence (level eta lam) z := by
        simpa only [evalSeed,if_pos ha,Option.some.injEq] using hv
      have hz : topCoordinates eta heta x = z :=
        sourceSequence_injective (level eta lam) (by simpa only [topSource,←ha] using heq)
      simp only [seedCoordinate,if_pos ha,hz]
    · simp only [evalSeed,if_neg ha] at hv
      contradiction
  | some p =>
    have hp : (sourcePath eta p).rank = lam := by
      by_contra h
      simp only [evalSeed,if_neg h] at hv
      contradiction
    have hvalue : sourcePathValue eta heta p x = some (sourceSequence (level eta lam) z) := by
      simpa only [evalSeed,if_pos hp] using hv
    unfold sourcePathValue optionalTranslate at hvalue
    split at hvalue
    · contradiction
    · rename_i y hy
      obtain ⟨w,hw,hchildren⟩ := limit_value_children eta heta _ lam hp hlam y
      have hwz : w = z := sourceSequence_injective (level eta lam)
        (hw.symm.trans (Option.some.inj hvalue))
      simp only [seedCoordinate,if_pos hp,sourcePathValue_child eta heta p x y hy n,
        (hchildren n).1,hwz]

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionProfileDecoders
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)

def freshBirthCodeValue (n : ℕ)
    (c : (poolCodes eta heta (Frame.q eta lam hlam n)).Code ⊕
      (Unit ⊕ (poolCodes eta heta (Frame.rho eta lam hlam n)).Code))
    (x : (fsTower eta).Carrier) :
    Option (BirthData eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) :=
  match c with
  | .inl d => match h : (poolCodes eta heta (Frame.q eta lam hlam n)).value d x with
      | none => none
      | some u => some (.inl ⟨u,((poolCodes eta heta _).covers x u).mp ⟨d,h⟩⟩)
  | .inr (.inl _) => some (.inr (.inl ()))
  | .inr (.inr d) => match h : (poolCodes eta heta (Frame.rho eta lam hlam n)).value d x with
      | none => none
      | some u => some (.inr (.inr ⟨u,((poolCodes eta heta _).covers x u).mp ⟨d,h⟩⟩))

def columnCodeValue (n : ℕ) (c : ColumnCode eta heta lam hlam n)
    (x : (fsTower eta).Carrier) :
    Option (Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) :=
  (freshBirthCodeValue eta heta lam hlam c.val.1 c.val.2 x).map
    (fun d => ⟨⟨c.val.1,d⟩,c.property⟩)

theorem encodeNew_freshBirthCodeValue (n : ℕ)
    (c : (poolCodes eta heta (Frame.q eta lam hlam n)).Code ⊕
      (Unit ⊕ (poolCodes eta heta (Frame.rho eta lam hlam n)).Code))
    (x : (fsTower eta).Carrier) :
    (freshBirthCodeValue eta heta lam hlam n c x).map
      (encodeNew eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) =
    (evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) ⟨n,c⟩ x).map Prod.snd := by
  rcases c with c|⟨⟨⟩⟩|c
  · dsimp only [freshBirthCodeValue]
    split <;> simp_all [evalBirthCode,encodeNew]
  · rfl
  · dsimp only [freshBirthCodeValue]
    split <;> simp_all [evalBirthCode,encodeNew]

theorem encodeBirth_freshBirthCodeValue (n : ℕ)
    (c : (poolCodes eta heta (Frame.q eta lam hlam n)).Code ⊕
      (Unit ⊕ (poolCodes eta heta (Frame.rho eta lam hlam n)).Code))
    (x : (fsTower eta).Carrier) :
    (freshBirthCodeValue eta heta lam hlam n c x).map
      (fun d => encodeBirth eta heta lam hlam (TokenModel.lowerPools eta heta x lam) ⟨n,d⟩) =
    evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) ⟨n,c⟩ x := by
  rcases c with c|⟨⟨⟩⟩|c
  · dsimp only [freshBirthCodeValue]
    split <;> simp_all [evalBirthCode,encodeBirth,encodeNew]
  · rfl
  · dsimp only [freshBirthCodeValue]
    split <;> simp_all [evalBirthCode,encodeBirth,encodeNew]

theorem encodeColumn_columnCodeValue (n : ℕ) (c : ColumnCode eta heta lam hlam n)
    (x : (fsTower eta).Carrier) :
    (columnCodeValue eta heta lam hlam n c x).map
      (encodeColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) =
    evalColumnCode eta heta lam hlam n c x := by
  induction n with
  | zero =>
    rcases c with ⟨⟨k,c⟩,hk⟩
    have hk0 : k=0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp only [columnCodeValue,Option.map_map]
    change (freshBirthCodeValue eta heta lam hlam 0 c x).map
      (encodeNew eta heta lam hlam (TokenModel.lowerPools eta heta x lam) 0) = _
    exact encodeNew_freshBirthCodeValue eta heta lam hlam 0 c x
  | succ n ih =>
    by_cases h : c.val.1=n+1
    · rcases c with ⟨⟨k,c⟩,hk⟩
      change k=n+1 at h
      subst k
      simp only [columnCodeValue,Option.map_map,Function.comp_def,encodeColumn_fresh,evalColumnCode_fresh]
      change (freshBirthCodeValue eta heta lam hlam (n+1) c x).map
        (fun d => encodeColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) (n+1)
          (freshColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) (n+1) d)) = _
      simp only [encodeColumn_fresh]
      exact encodeNew_freshBirthCodeValue eta heta lam hlam _ c x
    · let d : ColumnCode eta heta lam hlam n := ⟨c.val,by have hc := c.property; omega⟩
      have hval : columnCodeValue eta heta lam hlam (n+1) c x =
          (columnCodeValue eta heta lam hlam n d x).map
            (propagate eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) := by
        simp only [columnCodeValue,Option.map_map]
        rfl
      have hc : evalColumnCode eta heta lam hlam (n+1) c x =
          (evalColumnCode eta heta lam hlam n d x).map (oldColumn eta heta lam hlam n) :=
        evalColumnCode_propagate eta heta lam hlam n d x
      rw [hval,hc]
      simpa only [Option.map_map,Function.comp_def,encodeColumn_propagate] using
        congrArg (Option.map (oldColumn eta heta lam hlam n)) (ih d)

theorem encodeBirth_columnCodeValue (n : ℕ) (c : ColumnCode eta heta lam hlam n)
    (x : (fsTower eta).Carrier) :
    (columnCodeValue eta heta lam hlam n c x).map
      (fun d => encodeBirth eta heta lam hlam (TokenModel.lowerPools eta heta x lam) d.val) =
    evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x := by
  rcases c with ⟨⟨k,c⟩,hk⟩
  simp only [columnCodeValue,Option.map_map,Function.comp_def]
  exact encodeBirth_freshBirthCodeValue eta heta lam hlam k c x

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionProfileShapes
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta)

theorem codeRep_mem_pool (a : Ordinal.{0})
    {F : (fsTower eta).Carrier → Option (Ambient eta heta)} (hF : CodeRep eta heta a F)
    (x : (fsTower eta).Carrier) (u : Ambient eta heta) (hu : F x = some u) :
    u ∈ TokenModel.mainPool eta heta x a := by
  obtain ⟨c,hc⟩ := hF
  exact ((poolCodes eta heta a).covers x u).mp ⟨c,(hc x).trans hu⟩

def seedSourceTuple (s : SeedIndex) (x : (fsTower eta).Carrier) (z : ℕ → Ambient eta heta)
    (hv : evalSeed eta heta lam s x = some (sourceSequence (level eta lam) z)) :
    SourceTuple eta heta lam hlam (TokenModel.lowerPools eta heta x lam) :=
  fun n => ⟨z n,codeRep_mem_pool eta heta _ (codeRep_seedCoordinate eta heta lam hlam htop s n) x (z n)
    (seedCoordinate_source eta heta lam hlam s n x z hv)⟩

theorem ambientProfile_source_shape (x : (fsTower eta).Carrier)
    (s : SourceTuple eta heta lam hlam (TokenModel.lowerPools eta heta x lam))
    (n : ℕ) (c : Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) :
    ambientProfile eta heta lam hlam htop n
        (sourceSequence (level eta lam) (fun k => (s k).val))
        (mapColumn eta heta lam hlam (TokenModel.ambientLower eta heta x lam) n c) =
      sourceBit eta heta lam hlam (TokenModel.lowerPools eta heta x lam) s c.val :=
  ambientProfile_restricted eta heta lam hlam htop (TokenModel.ambientLower eta heta x lam)
    n (.inl s) c

theorem ambientProfile_filler_shape (x : (fsTower eta).Carrier)
    (B : Finset (ℕ × Ambient eta heta))
    (hB : ∀ b ∈ B, NewColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) b.1 b.2)
    (n : ℕ) (c : Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n) :
    ambientProfile eta heta lam hlam htop n (finiteFiller (level eta lam) B)
        (mapColumn eta heta lam hlam (TokenModel.ambientLower eta heta x lam) n c) =
      decide (encodeBirth eta heta lam hlam (TokenModel.lowerPools eta heta x lam) c.val ∈ B) := by
  obtain ⟨r,hr⟩ := exists_rowObject_of_mem_limitSet eta heta lam hlam
    (TokenModel.lowerPools eta heta x lam) htop (Or.inr ⟨B,rfl,hB⟩)
  rcases r with s|A
  · exact False.elim (sourceSequence_ne_finiteFiller _ _ _ _ hr)
  · have hsupport : A.map (birthEmbedding eta heta lam hlam (TokenModel.lowerPools eta heta x lam) htop) = B :=
      finiteFiller_injective (level eta lam) hr
    have hp := ambientProfile_restricted eta heta lam hlam htop
      (TokenModel.ambientLower eta heta x lam) n (.inr A) c
    rw [hr] at hp
    rw [hp]
    change decide (c.val ∈ A) = decide (encodeBirth eta heta lam hlam
      (TokenModel.lowerPools eta heta x lam) c.val ∈ B)
    congr 1
    rw [←hsupport]
    apply propext
    constructor
    · intro hc
      exact Finset.mem_map.mpr ⟨c.val,hc,rfl⟩
    · intro hc
      obtain ⟨b,hb,heq⟩ := Finset.mem_map.mp hc
      have hbc := encodeBirth_injective eta heta lam hlam
        (TokenModel.lowerPools eta heta x lam) htop heq
      exact hbc ▸ hb

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionProfileBorel
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta)

abbrev LimitCode := SeedIndex ⊕ Finset (BirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a))

def ProfileCodeTrue (row : LimitCode eta heta lam hlam) {n : ℕ}
    (c : ColumnCode eta heta lam hlam n) (x : (fsTower eta).Carrier) : Prop :=
  match row with
  | .inl s => evalSeed eta heta lam s x ≠ none ∧
      match c.val.2 with
      | .inl d => (poolCodes eta heta (Frame.q eta lam hlam c.val.1)).value d x ≠ none ∧
          seedCoordinate eta heta lam s c.val.1 x =
            (poolCodes eta heta (Frame.q eta lam hlam c.val.1)).value d x
      | .inr (.inl _) => True
      | .inr (.inr _) => False
  | .inr A =>
      liftFinite (0,extraAtom 0)
        (fun b => evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) b x) A ≠ none ∧
      evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x ≠ none ∧
      ∃ b ∈ A, evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) b x =
        evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x

include htop in
theorem measurableSet_profileCodeTrue (row : LimitCode eta heta lam hlam) {n : ℕ}
    (c : ColumnCode eta heta lam hlam n) : MeasurableSet {x | ProfileCodeTrue eta heta lam hlam row c x} := by
  have hnone := measurableSet_evalBirthCode_none eta heta lam hlam (fun a _ => poolCodes eta heta a)
    (fun a ha => (poolCodes_borel eta heta a (ha.le.trans htop)).absent)
  have heq := measurableSet_evalBirthCode_equal eta heta lam hlam (fun a _ => poolCodes eta heta a) htop
    (fun a ha => (poolCodes_borel eta heta a (ha.le.trans htop)).absent)
    (fun a ha => (poolCodes_borel eta heta a (ha.le.trans htop)).equal)
  cases row with
  | inl s =>
    rcases c with ⟨⟨k,c⟩,hk⟩
    rcases c with d|⟨⟨⟩⟩|d
    · change MeasurableSet {x | evalSeed eta heta lam s x ≠ none ∧
        (poolCodes eta heta (Frame.q eta lam hlam k)).value d x ≠ none ∧
        seedCoordinate eta heta lam s k x = (poolCodes eta heta (Frame.q eta lam hlam k)).value d x}
      simp only [setOf_and]
      exact (measurableSet_evalSeed_absent eta heta lam s).compl.inter
        (((poolCodes_borel eta heta _ ((Frame.q_lt eta lam hlam k).le.trans htop)).absent d).compl.inter
          (measurableSet_codeRep_eq_diagonal eta heta _ ((Frame.q_lt eta lam hlam k).le.trans htop)
            (codeRep_seedCoordinate eta heta lam hlam htop s k) (codeRep_value eta heta _ d)))
    · simpa only [ProfileCodeTrue,and_true] using (measurableSet_evalSeed_absent eta heta lam s).compl
    · simp only [ProfileCodeTrue,and_false,setOf_false]
      exact MeasurableSet.empty
  | inr A =>
    simp only [ProfileCodeTrue,setOf_and]
    refine (measurableSet_liftFinite_none (0,extraAtom 0) _ hnone A).compl.inter
      ((hnone c.val).compl.inter ?_)
    simp only [←exists_prop,setOf_exists]
    exact MeasurableSet.iUnion (fun b => MeasurableSet.iUnion (fun _ =>
      (heq b c.val).preimage (measurable_id.prodMk measurable_id)))

theorem profileCodeTrue_spec (x : (fsTower eta).Carrier)
    (row : LimitCode eta heta lam hlam) (v : Ambient eta heta)
    (hr : (limitPoolCodes eta heta lam hlam (fun a _ => poolCodes eta heta a)).value row x = some v)
    (n : ℕ) (c : ColumnCode eta heta lam hlam n)
    (d : Column eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n)
    (hc : columnCodeValue eta heta lam hlam n c x = some d) :
    ambientProfile eta heta lam hlam htop n v
      (mapColumn eta heta lam hlam (TokenModel.ambientLower eta heta x lam) n d) =
      decide (ProfileCodeTrue eta heta lam hlam row c x) := by
  cases row with
  | inl s =>
    change evalSeed eta heta lam s x = some v at hr
    obtain ⟨z,hz⟩ := evalSeed_limit_source eta heta lam hlam s x v hr
    have hsource : evalSeed eta heta lam s x = some (sourceSequence (level eta lam) z) :=
      hr.trans (congrArg some hz)
    let t := seedSourceTuple eta heta lam hlam htop s x z hsource
    have hcoord (k) := seedCoordinate_source eta heta lam hlam s k x z hsource
    rw [hz]
    have hshape := ambientProfile_source_shape eta heta lam hlam htop x t n d
    change ambientProfile eta heta lam hlam htop n (sourceSequence (level eta lam) (fun k => (t k).val))
      (mapColumn eta heta lam hlam (TokenModel.ambientLower eta heta x lam) n d) = _
    rw [hshape]
    rcases c with ⟨⟨k,c⟩,hk⟩
    rcases c with c|⟨⟨⟩⟩|c
    · dsimp only [columnCodeValue,freshBirthCodeValue] at hc
      split at hc
      · simp at hc
      · rename_i u hu
        cases hc
        simp [sourceBit,ProfileCodeTrue,hr,hu,hcoord,t,seedSourceTuple]
    · cases hc
      simp [sourceBit,ProfileCodeTrue,hr]
    · dsimp only [columnCodeValue,freshBirthCodeValue] at hc
      split at hc
      · simp at hc
      · rename_i u hu
        cases hc
        simp [sourceBit,ProfileCodeTrue]
  | inr A =>
    change (liftFinite (0,extraAtom 0)
      (fun b => evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) b x) A).map
        (finiteFiller (level eta lam)) = some v at hr
    cases hA : liftFinite (0,extraAtom 0)
        (fun b => evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) b x) A with
    | none => simp only [hA,Option.map_none] at hr; contradiction
    | some B =>
      have hv : finiteFiller (level eta lam) B = v := by
        simpa only [hA,Option.map_some,Option.some.injEq] using hr
      have hB : ∀ b ∈ B, NewColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) b.1 b.2 := by
        intro b hb
        obtain ⟨e,_,he⟩ := liftFinite_mem _ _ A B hA b hb
        exact (evalBirthCode_covers eta heta lam hlam (fun a _ => poolCodes eta heta a) x b).mp ⟨e,he⟩
      have hbirth : evalBirthCode eta heta lam hlam (fun a _ => poolCodes eta heta a) c.val x =
          some (encodeBirth eta heta lam hlam (TokenModel.lowerPools eta heta x lam) d.val) := by
        have h := encodeBirth_columnCodeValue eta heta lam hlam n c x
        rw [hc,Option.map_some] at h
        exact h.symm
      rw [←hv,ambientProfile_filler_shape eta heta lam hlam htop x B hB n d]
      congr 1
      simp only [ProfileCodeTrue,hA,hbirth]
      apply propext
      simpa using liftFinite_mem_iff _ _ A B hA
        (encodeBirth eta heta lam hlam (TokenModel.lowerPools eta heta x lam) d.val)

theorem poolCodes_cast_value {a : Ordinal.{0}} {P Q : PoolCodes eta heta a}
    (h : P=Q) (c : P.Code) (x : (fsTower eta).Carrier) :
    Q.value (cast (congrArg PoolCodes.Code h) c) x = P.value c x := by
  cases h
  rfl

def limitCodeOfPoolCode (c : (poolCodes eta heta lam).Code) : LimitCode eta heta lam hlam :=
  cast (congrArg PoolCodes.Code (poolCodes_limit eta heta lam hlam)) c

theorem limitCodeOfPoolCode_value (c : (poolCodes eta heta lam).Code) (x : (fsTower eta).Carrier) :
    (limitPoolCodes eta heta lam hlam (fun a _ => poolCodes eta heta a)).value
      (limitCodeOfPoolCode eta heta lam hlam c) x = (poolCodes eta heta lam).value c x :=
  poolCodes_cast_value eta heta (poolCodes_limit eta heta lam hlam) c x

theorem columnCodeValue_enumerated (n : ℕ) (x : (fsTower eta).Carrier) (k : ℕ) :
    columnCodeValue eta heta lam hlam n
      (columnCodeList eta heta lam hlam n (columnEnumerationIndex eta heta lam hlam n x k)) x =
      some (columnEnumerationRaw eta heta lam hlam htop n x k) := by
  apply (option_map_eq_iff_of_injective
    (encodeColumn eta heta lam hlam (TokenModel.lowerPools eta heta x lam) n)
    (encodeColumn_injective eta heta lam hlam _ htop n) _ _).mp
  rw [encodeColumn_columnCodeValue,Option.map_some,encodeColumn_columnEnumerationRaw]
  exact columnEnumerationIndex_value eta heta lam hlam htop n x k

theorem measurable_profile_pool_columnEnumeration (n i j : ℕ) :
    Measurable (fun x : (fsTower eta).Carrier =>
      ambientProfile eta heta lam hlam htop n (poolEnumeration eta heta lam x i)
        (mapColumn eta heta lam hlam (TokenModel.ambientLower eta heta x lam) n
          (columnEnumerationRaw eta heta lam hlam htop n x j))) := by
  let P (r c : ℕ) (x : (fsTower eta).Carrier) := ProfileCodeTrue eta heta lam hlam
    (limitCodeOfPoolCode eta heta lam hlam (poolCodeList eta heta lam r))
    (columnCodeList eta heta lam hlam n c) x
  have hP (r c : ℕ) : MeasurableSet {x | P r c x} :=
    measurableSet_profileCodeTrue eta heta lam hlam htop _ _
  have hselected := measurableSet_selected₂ P hP
    (fun x => poolEnumerationIndex eta heta lam x i)
    (fun x => columnEnumerationIndex eta heta lam hlam n x j)
    (measurable_poolEnumerationIndex eta heta lam htop i)
    (measurable_columnEnumerationIndex eta heta lam hlam htop n j)
  have hbool : Measurable (fun x => decide (P (poolEnumerationIndex eta heta lam x i)
      (columnEnumerationIndex eta heta lam hlam n x j) x)) := by
    apply measurable_to_bool
    change MeasurableSet {x | decide (P (poolEnumerationIndex eta heta lam x i)
      (columnEnumerationIndex eta heta lam hlam n x j) x) = true}
    simpa only [decide_eq_true_eq] using hselected
  convert hbool using 1
  funext x
  apply profileCodeTrue_spec eta heta lam hlam htop x _ _ _ n _ _
    (columnCodeValue_enumerated eta heta lam hlam htop n x j)
  rw [limitCodeOfPoolCode_value]
  exact poolEnumerationIndex_value eta heta lam x i

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionMemberBorel
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def OptionalMember (col row : Option (Ambient eta heta)) : Prop :=
  match col,row with
  | some c,some r => Member c r
  | _,_ => False

theorem optionalMember_seed_iff (a : Ordinal.{0}) (s : SeedIndex)
    (x : (fsTower eta).Carrier) (col : Option (Ambient eta heta)) :
    OptionalMember eta heta col (evalSeed eta heta (a+1) s x) ↔
      evalSeed eta heta (a+1) s x ≠ none ∧ col ≠ none ∧
        ∃ n, evalSeed eta heta a (childSeed s n) x = col := by
  cases hr : evalSeed eta heta (a+1) s x with
  | none => simp [OptionalMember]
  | some v =>
    cases hc : col with
    | none => simp [OptionalMember]
    | some u =>
      simpa [OptionalMember] using evalSeed_successor_member_all eta heta a s x v u hr

theorem optionalMember_finite_iff {C : Type}
    (a : Ordinal.{0}) (F : C → Option (Ambient eta heta)) (A : Finset C)
    (col : Option (Ambient eta heta)) :
    OptionalMember eta heta col
        ((liftFinite (extraAtom 0) F A).map (finiteCollection (level eta (a+1)))) ↔
      liftFinite (extraAtom 0) F A ≠ none ∧ col ≠ none ∧
        ∃ c ∈ A, F c = col := by
  cases hF : liftFinite (extraAtom 0) F A with
  | none => simp [OptionalMember]
  | some B =>
    cases hc : col with
    | none => simp [OptionalMember]
    | some u =>
      simpa [OptionalMember,member_finiteCollection] using liftFinite_mem_iff _ F A B hF u

theorem measurableSet_optionalMember_successorCodes (a : Ordinal.{0})
    (lower : PoolCodes eta heta a) (hlower : PoolCodesBorel eta heta lower)
    (row : (successorPoolCodes eta heta a lower).Code) (col : lower.Code) :
    MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      OptionalMember eta heta (lower.value col p.2)
        ((successorPoolCodes eta heta a lower).value row p.1)} := by
  cases row with
  | inl s =>
    simp only [successorPoolCodes,Sum.elim_inl,optionalMember_seed_iff,setOf_and,setOf_exists]
    refine ((measurableSet_evalSeed_absent eta heta (a+1) s).preimage measurable_fst).compl.inter
      (((hlower.absent col).preimage measurable_snd).compl.inter ?_)
    exact MeasurableSet.iUnion (fun n => by
      simpa only [lower.value_seed] using hlower.equal (lower.seed (childSeed s n)) col)
  | inr A =>
    simp only [successorPoolCodes,Sum.elim_inr,optionalMember_finite_iff,setOf_and]
    refine ((measurableSet_liftFinite_none (extraAtom 0) lower.value hlower.absent A).preimage
      measurable_fst).compl.inter (((hlower.absent col).preimage measurable_snd).compl.inter ?_)
    simp only [← exists_prop,setOf_exists]
    exact MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun _ => hlower.equal c col))

theorem measurableSet_optionalMember_poolCodes (a : Ordinal.{0}) (ha : a ≤ Frame.top eta) :
    ∀ (row : (poolCodes eta heta (a+1)).Code) (col : (poolCodes eta heta a).Code),
    MeasurableSet {p : (fsTower eta).Carrier × (fsTower eta).Carrier |
      OptionalMember eta heta ((poolCodes eta heta a).value col p.2)
        ((poolCodes eta heta (a+1)).value row p.1)} := by
  rw [poolCodes_add_one]
  exact measurableSet_optionalMember_successorCodes eta heta a _ (poolCodes_borel eta heta a ha)

theorem measurableSet_member_poolEnumeration (a : Ordinal.{0})
    (ha : a+1 ≤ Frame.top eta) (i j : ℕ) :
    MeasurableSet {x : (fsTower eta).Carrier |
      Member (poolEnumeration eta heta a x j) (poolEnumeration eta heta (a+1) x i)} := by
  have hsmall : a ≤ Frame.top eta := (show a ≤ a+1 from le_self_add).trans ha
  have hcodes (r c : ℕ) : MeasurableSet {x : (fsTower eta).Carrier |
      OptionalMember eta heta (poolPartialList eta heta a c x)
        (poolPartialList eta heta (a+1) r x)} :=
    (measurableSet_optionalMember_poolCodes eta heta a hsmall
      (poolCodeList eta heta (a+1) r) (poolCodeList eta heta a c)).preimage
      (measurable_id.prodMk measurable_id)
  have h := measurableSet_selected₂ (fun r c x =>
    OptionalMember eta heta (poolPartialList eta heta a c x) (poolPartialList eta heta (a+1) r x))
    hcodes (fun x => poolEnumerationIndex eta heta (a+1) x i)
    (fun x => poolEnumerationIndex eta heta a x j)
    (measurable_poolEnumerationIndex eta heta (a+1) ha i)
    (measurable_poolEnumerationIndex eta heta a hsmall j)
  simpa only [poolEnumerationIndex_value,OptionalMember] using h

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionColumnMemberBorel
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction
open RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem measurableSet_member_codeRep_poolEnumeration (a : Ordinal.{0})
    (ha : a ≤ Frame.top eta) {F : (fsTower eta).Carrier → Option (Ambient eta heta)}
    (hF : CodeRep eta heta (a+1) F) (j : ℕ) :
    MeasurableSet {x | OptionalMember eta heta (some (poolEnumeration eta heta a x j)) (F x)} := by
  obtain ⟨r,hr⟩ := hF
  have hcodes (c : ℕ) : MeasurableSet {x : (fsTower eta).Carrier |
      OptionalMember eta heta (poolPartialList eta heta a c x) (F x)} := by
    have h := (measurableSet_optionalMember_poolCodes eta heta a ha r
      (poolCodeList eta heta a c)).preimage (measurable_id.prodMk measurable_id)
    simpa only [hr] using h
  have h := measurableSet_selected (fun c x =>
    OptionalMember eta heta (poolPartialList eta heta a c x) (F x)) hcodes
    (fun x => poolEnumerationIndex eta heta a x j)
    (measurable_poolEnumerationIndex eta heta a ha j)
  simpa only [poolEnumerationIndex_value] using h

theorem measurableSet_member_column_poolEnumeration (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    (htop : lam ≤ Frame.top eta) (n i j : ℕ) :
    MeasurableSet {x : (fsTower eta).Carrier |
      Member (poolEnumeration eta heta (Frame.rho eta lam hlam n) x j)
        (columnEnumeration eta heta lam hlam n x i)} := by
  have hr : Frame.rho eta lam hlam n ≤ Frame.top eta := (Frame.rho_lt eta lam hlam n).le.trans htop
  have hcodes (c : ℕ) : MeasurableSet {x : (fsTower eta).Carrier |
      OptionalMember eta heta (some (poolEnumeration eta heta (Frame.rho eta lam hlam n) x j))
        (columnPartialList eta heta lam hlam n c x)} := by
    apply measurableSet_member_codeRep_poolEnumeration eta heta _ hr
    have hc := codeRep_columnCode eta heta lam hlam htop n (columnCodeList eta heta lam hlam n c)
    simpa only [Frame.rho,Frame.delta,add_assoc,one_add_one_eq_two] using hc
  have h := measurableSet_selected (fun c x =>
    OptionalMember eta heta (some (poolEnumeration eta heta (Frame.rho eta lam hlam n) x j))
      (columnPartialList eta heta lam hlam n c x)) hcodes
    (fun x => columnEnumerationIndex eta heta lam hlam n x i)
    (measurable_columnEnumerationIndex eta heta lam hlam htop n i)
  simpa only [columnEnumerationIndex_value eta heta lam hlam htop n,OptionalMember] using h

end FSCofinality.CosetConstruction

end
end

-- Original module: FSCofinalityProof.CosetConstructionNativeModel
section


noncomputable section
attribute [local instance] Classical.propDecidable
open Set MeasureTheory Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def rawEnumeration (x : (fsTower eta).Carrier) : (s : TokenSort eta) → ℕ ≃ raw eta heta x s
  | .inl a => poolEnumerationEquiv eta heta (Frame.rank a) x
  | .inr (lam,n) => columnEnumerationEquiv eta heta (Frame.rank lam.val) lam.property
      (Frame.rank_le_top lam.val) n x

def nativeEnumeration (x : (fsTower eta).Carrier) : ℕ ≃ Vertex eta heta x :=
  vertexEnumeration eta heta (rawEnumeration eta heta) x

def nativeModel (x : (fsTower eta).Carrier) : Structures (language eta heta) :=
  modelWithEnumeration eta heta (bottom eta heta) x (nativeEnumeration eta heta x)

theorem measurable_ordinaryMatrix_rawEnumeration (r : OrdinaryRole eta) (i j : ℕ) :
    Measurable (fun x => ordinaryMatrix eta heta x r
      (rawEnumeration eta heta x (rowSort eta r) i) (rawEnumeration eta heta x (colSort eta r) j)) := by
  cases r with
  | inl a =>
    have h : Measurable (fun x : (fsTower eta).Carrier =>
        ordinaryRaw (poolEnumeration eta heta (Frame.rank a.val+1) x i)
          (poolEnumeration eta heta (Frame.rank a.val) x j)) := by
      apply measurable_to_bool
      change MeasurableSet {x | decide (Member (poolEnumeration eta heta (Frame.rank a.val) x j)
        (poolEnumeration eta heta (Frame.rank a.val+1) x i)) = true}
      simpa only [decide_eq_true_eq] using
        measurableSet_member_poolEnumeration eta heta (Frame.rank a.val) a.property i j
    simpa only [ordinaryMatrix,rawEnumeration,rowSort,colSort,mainSort,Frame.rank_ofOrdinal,
      poolEnumerationEquiv,Equiv.ofBijective_apply] using h
  | inr c =>
    rcases c with ⟨lam,n⟩
    have h : Measurable (fun x : (fsTower eta).Carrier =>
        ordinaryRaw (columnEnumeration eta heta (Frame.rank lam.val) lam.property n x i)
          (poolEnumeration eta heta (Frame.rho eta (Frame.rank lam.val) lam.property n) x j)) := by
      apply measurable_to_bool
      change MeasurableSet {x | decide (Member
        (poolEnumeration eta heta (Frame.rho eta (Frame.rank lam.val) lam.property n) x j)
        (columnEnumeration eta heta (Frame.rank lam.val) lam.property n x i)) = true}
      simpa only [decide_eq_true_eq] using measurableSet_member_column_poolEnumeration eta heta
        (Frame.rank lam.val) lam.property (Frame.rank_le_top lam.val) n i j
    convert h using 1
    funext x
    change ordinaryRaw (encodeColumn eta heta (Frame.rank lam.val) lam.property
      (lowerPools eta heta x (Frame.rank lam.val)) n
      (columnEnumerationRaw eta heta (Frame.rank lam.val) lam.property (Frame.rank_le_top lam.val) n x i))
      (poolEnumeration eta heta (Frame.rank (Frame.ofOrdinal eta
        (Frame.rho eta (Frame.rank lam.val) lam.property n) _)) x j) = _
    rw [Frame.rank_ofOrdinal,encodeColumn_columnEnumerationRaw]

theorem measurable_limitProfile_rawEnumeration (lam : LimitIndex eta) (n i j : ℕ) :
    Measurable (fun x => limitProfile eta heta x lam n
      (rawEnumeration eta heta x (.inl lam.val) i) (rawEnumeration eta heta x (.inr (lam,n)) j)) := by
  exact measurable_profile_pool_columnEnumeration eta heta (Frame.rank lam.val) lam.property
    (Frame.rank_le_top lam.val) n i j

theorem measurable_bottom_rawEnumeration (v : Token ℕ) (n : ℕ) :
    Measurable (fun x => bottom eta heta x
      (mapToken (rawEnumeration eta heta x (zeroSort eta)) v) n) := by
  let C (x : (fsTower eta).Carrier) : Bottom.Context BottomValueSpace :=
    ⟨v.1.length,fun i => decodeAtom eta heta (poolEnumeration eta heta 0 x v.1[i])⟩
  have hmk : Measurable (fun z : Fin v.1.length → BottomValueSpace =>
      (⟨v.1.length,z⟩ : Bottom.Context BottomValueSpace)) := by
    intro s hs
    exact MeasurableSpace.measurableSet_iInf.mp hs v.1.length
  have hC : Measurable C := hmk.comp (measurable_pi_lambda _ (fun i =>
    measurable_decodeAtom_poolEnumeration_zero eta heta v.1[i]))
  have h := (measurable_pi_apply n).comp (Bottom.measurable_bottomMap.comp
    (hC.prodMk (measurable_const : Measurable (fun _ : (fsTower eta).Carrier => v.2))))
  convert h using 1
  funext x
  unfold bottom bottomListMap decodedBottom contextOfList
  apply congrArg (fun c : Bottom.Context BottomValueSpace => Bottom.bottomMap c v.2 n)
  have hctx {V : Type} (c d : Bottom.Context V)
      (h : List.ofFn c.2 = List.ofFn d.2) : c=d := by
    rcases c with ⟨l,c⟩
    rcases d with ⟨m,d⟩
    have hl : l=m := by simpa only [List.length_ofFn] using congrArg List.length h
    subst m
    apply congrArg (fun f => (⟨l,f⟩ : Bottom.Context V))
    funext i
    have hi := congrArg (fun t : List V => t[i.val]?) h
    simpa only [List.getElem?_ofFn,dif_pos i.isLt,Option.some.injEq] using hi
  apply hctx
  change List.ofFn (List.get _) = List.ofFn (C x).2
  rw [List.ofFn_get]
  apply List.ext_getElem
  · simp [C,mapToken]
  · intro i hi hj
    simp [C,mapToken,rawEnumeration,zeroSort,mainSort,Frame.rank_ofOrdinal,poolEnumerationEquiv]
    rfl

theorem measurable_nativeModel : Measurable (nativeModel eta heta) :=
  measurable_modelWithTemplateEnumeration eta heta (rawEnumeration eta heta)
    (measurable_ordinaryMatrix_rawEnumeration eta heta)
    (measurable_limitProfile_rawEnumeration eta heta) (measurable_bottom_rawEnumeration eta heta)

theorem nativeEnumeration_coordinate_preimage (x : (fsTower eta).Carrier) (n : ℕ) :
    (nativeEnumeration eta heta x).symm (.inl n) = (templateEnumeration eta heta).symm (.inl n) :=
  vertexEnumeration_coordinate_preimage eta heta (rawEnumeration eta heta) x n

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.RawObjectsPoolProfileSeparation
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects

/-- Every finite birth support gives a filler row in the actual countable
pool, independently of the source seeds. -/
theorem pool_fillerRow (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient eta heta))
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta)
    (A : Finset (Birth eta heta lam hlam (fun b _ => Pool eta heta seeds b))) :
    rowObject eta heta lam hlam (fun b _ => Pool eta heta seeds b) htop (.inr A) ∈
      Pool eta heta seeds lam := by
  rw [pool_limit eta heta seeds lam hlam]
  apply Or.inr
  apply (mem_finiteImages_iff _ _ _).mpr
  refine ⟨A.map (birthEmbedding eta heta lam hlam (fun b _ => Pool eta heta seeds b) htop),?_,rfl⟩
  intro p hp
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hp
  exact encodeNew_mem eta heta lam hlam (fun b _ => Pool eta heta seeds b) b.1 b.2

/-- Restricting rows and columns to the same actual pool retains column
separation: a singleton birth-support filler distinguishes each column. -/
theorem pool_profile_column_separating (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (seeds : Ordinal.{0} → Set (Ambient eta heta))
    (hseeds : ∀ a, seeds a ⊆ Valid eta heta a)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta) (n : ℕ) :
    Function.Injective (fun c : Column eta heta lam hlam (fun b _ => Pool eta heta seeds b) n =>
      fun u : Pool eta heta seeds lam => ambientProfile eta heta lam hlam htop n u.val
        (mapColumn eta heta lam hlam
          (fun b _ => pool_subset_valid eta heta seeds hseeds b) n c)) := by
  intro c d hcd
  let A : Finset (Birth eta heta lam hlam (fun b _ => Pool eta heta seeds b)) := {c.val}
  let r : LimitRow eta heta lam hlam (fun b _ => Pool eta heta seeds b) := .inr A
  have hr : rowObject eta heta lam hlam (fun b _ => Pool eta heta seeds b) htop r ∈
      Pool eta heta seeds lam := pool_fillerRow eta heta seeds lam hlam htop A
  have hquery := congrFun hcd ⟨rowObject eta heta lam hlam (fun b _ => Pool eta heta seeds b) htop r,hr⟩
  have hlocal := (ambientProfile_restricted eta heta lam hlam htop
      (fun b _ => pool_subset_valid eta heta seeds hseeds b) n r c).symm.trans
    (hquery.trans (ambientProfile_restricted eta heta lam hlam htop
      (fun b _ => pool_subset_valid eta heta seeds hseeds b) n r d))
  have hm : d.val ∈ ({c.val} : Finset (Birth eta heta lam hlam (fun b _ => Pool eta heta seeds b))) := by
    by_contra hn
    simp only [r,A,profile,rowBit,Finset.mem_singleton,decide_true] at hlocal
    simp only [Finset.mem_singleton] at hn
    simp only [decide_eq_false hn] at hlocal
    contradiction
  exact Subtype.ext (Finset.mem_singleton.mp hm).symm

end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.CosetConstructionRawProperties
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem mainPool_ordinary_union_injOn (x y : (fsTower eta).Carrier) (a : Ordinal.{0}) :
    InjOn (fun r => fun c : (mainPool eta heta x a ∪ mainPool eta heta y a : Set (Ambient eta heta)) =>
      ordinaryRaw r c.val) (mainPool eta heta x (a+1) ∪ mainPool eta heta y (a+1)) :=
  ordinary_pool_union_injOn eta heta _ _
    (fun b => fullSeeds_typed eta heta b x) (fun b => fullSeeds_typed eta heta b y) a
    (fun _ h _ hm => fullSeeds_successor_downward eta heta a x h hm)
    (fun _ h _ hm => fullSeeds_successor_downward eta heta a y h hm)

theorem mainPool_ordinary_injective (x : (fsTower eta).Carrier) (a : Ordinal.{0}) :
    Function.Injective (fun r : mainPool eta heta x (a+1) =>
      fun c : mainPool eta heta x a => ordinaryRaw r.val c.val) := by
  intro r s hrs
  apply Subtype.ext
  apply ordinary_role_injOn (level eta (a+1)) (mainPool eta heta x (a+1))
    (mainPool eta heta x a) ?_ ?_ r.property s.property hrs
  · intro u hu
    exact pool_successor_collection eta heta _ (fun b => fullSeeds_typed eta heta b x) a hu
  · intro u hu c hc
    exact pool_member_lower eta heta _ a
      (fun _ h _ hm => fullSeeds_successor_downward eta heta a x h hm) hu hc

theorem column_ordinary_injective (x : (fsTower eta).Carrier)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta) (n : ℕ) :
    Function.Injective (fun r : Column eta heta lam hlam (lowerPools eta heta x lam) n =>
      fun c : mainPool eta heta x (Frame.rho eta lam hlam n) =>
        ordinaryRaw (encodeColumn eta heta lam hlam (lowerPools eta heta x lam) n r) c.val) := by
  intro r s hrs
  apply encodeColumn_injective eta heta lam hlam _ htop n
  let P := range (encodeColumn eta heta lam hlam (lowerPools eta heta x lam) n)
  have hdelta : Frame.delta eta lam hlam n = Frame.rho eta lam hlam n + 1 := by
    simp only [Frame.delta,Frame.rho,add_assoc,one_add_one_eq_two]
  apply ordinary_role_injOn (level eta (Frame.delta eta lam hlam n)) P
    (mainPool eta heta x (Frame.rho eta lam hlam n)) ?_ ?_ (mem_range_self r) (mem_range_self s) hrs
  · rintro u ⟨c,rfl⟩
    have hu := (pool_encodeColumn eta heta (fun b => fullSeeds eta heta b x) lam hlam htop n c).1
    have hm := pool_successor_collection eta heta (fun b => fullSeeds eta heta b x)
      (fun b => fullSeeds_typed eta heta b x) (Frame.rho eta lam hlam n) (by simpa only [hdelta] using hu)
    simpa only [hdelta] using hm
  · rintro u ⟨c,rfl⟩ v hv
    exact (pool_encodeColumn eta heta (fun b => fullSeeds eta heta b x) lam hlam htop n c).2 v hv

theorem column_ordinary_column_separating (x : (fsTower eta).Carrier)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta) (n : ℕ) :
    Function.Injective (fun c : mainPool eta heta x (Frame.rho eta lam hlam n) =>
      fun r : Column eta heta lam hlam (lowerPools eta heta x lam) n =>
        ordinaryRaw (encodeColumn eta heta lam hlam (lowerPools eta heta x lam) n r) c.val) := by
  intro c d hcd
  let r := freshColumn eta heta lam hlam (lowerPools eta heta x lam) n (.inr (.inr c))
  have hquery := congrFun hcd r
  have heq : d.val = c.val := by
    by_contra hne
    simp only [r,encodeColumn_fresh,encodeNew,ordinaryRaw,member_singleton,
      decide_true,decide_eq_false hne] at hquery
    contradiction
  exact Subtype.ext heq.symm

theorem ordinaryMatrix_row_injective (x : (fsTower eta).Carrier) (e : OrdinaryRole eta) :
    Function.Injective (ordinaryMatrix eta heta x e) := by
  cases e with
  | inl a =>
    intro r s hrs
    have hr : r.val ∈ mainPool eta heta x (Frame.rank a.val+1) := by
      simpa only [rowSort,raw,mainSort,Frame.rank_ofOrdinal] using r.property
    have hs : s.val ∈ mainPool eta heta x (Frame.rank a.val+1) := by
      simpa only [rowSort,raw,mainSort,Frame.rank_ofOrdinal] using s.property
    have he := mainPool_ordinary_injective eta heta x (Frame.rank a.val)
      (a₁ := ⟨r.val,hr⟩) (a₂ := ⟨s.val,hs⟩) hrs
    exact Subtype.ext (congrArg
      (fun u : mainPool eta heta x (Frame.rank a.val+1) => u.val) he)
  | inr c =>
    rcases c with ⟨lam,n⟩
    intro r s hrs
    apply column_ordinary_injective eta heta x (Frame.rank lam.val) lam.property (Frame.rank_le_top lam.val) n
    funext c
    let c' : raw eta heta x (colSort eta (.inr (lam,n))) := ⟨c.val,by
      simpa only [colSort,raw,mainSort,Frame.rank_ofOrdinal] using c.property⟩
    exact congrFun hrs c'

theorem ordinaryMatrix_column_separating (x : (fsTower eta).Carrier) (e : OrdinaryRole eta) :
    Function.Injective (fun c => fun r => ordinaryMatrix eta heta x e r c) := by
  cases e with
  | inl a =>
    intro c d hcd
    apply ordinary_pool_column_separating eta heta (fun b => fullSeeds eta heta b x) (Frame.rank a.val)
    funext r
    let r' : raw eta heta x (rowSort eta (.inl a)) := ⟨r.val,by
      simpa only [rowSort,raw,mainSort,Frame.rank_ofOrdinal,mainPool] using r.property⟩
    exact congrFun hcd r'
  | inr c =>
    rcases c with ⟨lam,n⟩
    intro c d hcd
    have hc : c.val ∈ mainPool eta heta x (Frame.rho eta (Frame.rank lam.val) lam.property n) := by
      simpa only [colSort,raw,mainSort,Frame.rank_ofOrdinal] using c.property
    have hd : d.val ∈ mainPool eta heta x (Frame.rho eta (Frame.rank lam.val) lam.property n) := by
      simpa only [colSort,raw,mainSort,Frame.rank_ofOrdinal] using d.property
    have he := column_ordinary_column_separating eta heta x (Frame.rank lam.val) lam.property
      (Frame.rank_le_top lam.val) n (a₁ := ⟨c.val,hc⟩) (a₂ := ⟨d.val,hd⟩) hcd
    exact Subtype.ext (congrArg
      (fun u : mainPool eta heta x (Frame.rho eta (Frame.rank lam.val) lam.property n) => u.val) he)

theorem mainPool_limit_subset_limitSet (x : (fsTower eta).Carrier)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) :
    mainPool eta heta x lam ⊆ LimitSet eta heta lam hlam (lowerPools eta heta x lam) := by
  intro u hu
  rw [mainPool,pool_limit eta heta _ lam hlam] at hu
  rcases hu with hs | hf
  · exact fullSeeds_limit_downward eta heta lam hlam x hs
  · obtain ⟨A,hA,rfl⟩ := (mem_finiteImages_iff _ _ _).mp hf
    exact Or.inr ⟨A,rfl,hA⟩

def localLimitRow (x : (fsTower eta).Carrier) (lam : LimitIndex eta)
    (r : raw eta heta x (.inl lam.val)) :
    LimitRow eta heta (Frame.rank lam.val) lam.property (lowerPools eta heta x (Frame.rank lam.val)) :=
  (exists_rowObject_of_mem_limitSet eta heta _ lam.property _ (Frame.rank_le_top lam.val)
    (mainPool_limit_subset_limitSet eta heta x _ lam.property r.property)).choose

theorem rowObject_localLimitRow (x : (fsTower eta).Carrier) (lam : LimitIndex eta)
    (r : raw eta heta x (.inl lam.val)) :
    rowObject eta heta _ lam.property _ (Frame.rank_le_top lam.val) (localLimitRow eta heta x lam r) = r.val :=
  (exists_rowObject_of_mem_limitSet eta heta _ lam.property _ (Frame.rank_le_top lam.val)
    (mainPool_limit_subset_limitSet eta heta x _ lam.property r.property)).choose_spec

theorem limitProfile_local (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (r : raw eta heta x (.inl lam.val)) (c : raw eta heta x (.inr (lam,n))) :
    limitProfile eta heta x lam n r c =
      profile eta heta _ lam.property _ n (localLimitRow eta heta x lam r) c := by
  have h := ambientProfile_restricted eta heta _ lam.property (Frame.rank_le_top lam.val)
    (ambientLower eta heta x _) n (localLimitRow eta heta x lam r) c
  rw [rowObject_localLimitRow] at h
  exact h

theorem limitProfile_full_injective (x : (fsTower eta).Carrier) (lam : LimitIndex eta) :
    Function.Injective (fun r => fun n => limitProfile eta heta x lam n r) := by
  intro r s hrs
  have hl : (fun n => profile eta heta _ lam.property _ n (localLimitRow eta heta x lam r)) =
      (fun n => profile eta heta _ lam.property _ n (localLimitRow eta heta x lam s)) := by
    funext n c
    exact (limitProfile_local eta heta x lam n r c).symm.trans
      ((congrFun (congrFun hrs n) c).trans (limitProfile_local eta heta x lam n s c))
  have he := fullProfile_injective eta heta _ lam.property _ hl
  apply Subtype.ext
  exact (rowObject_localLimitRow eta heta x lam r).symm.trans
    ((congrArg (rowObject eta heta _ lam.property _ (Frame.rank_le_top lam.val)) he).trans
      (rowObject_localLimitRow eta heta x lam s))

def limitPropagate (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ) :
    raw eta heta x (.inr (lam,n)) → raw eta heta x (.inr (lam,n+1)) :=
  propagate eta heta _ lam.property (lowerPools eta heta x _) n

theorem limitProfile_propagate (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (r : raw eta heta x (.inl lam.val)) (c : raw eta heta x (.inr (lam,n))) :
    limitProfile eta heta x lam (n+1) r (limitPropagate eta heta x lam n c) =
      limitProfile eta heta x lam n r c := by
  rw [limitProfile_local,limitProfile_local]
  exact profile_propagate eta heta _ lam.property _ n _ c

theorem limitProfile_column_separating (x : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ) :
    Function.Injective (fun c => fun r => limitProfile eta heta x lam n r c) :=
  pool_profile_column_separating eta heta (fun b => fullSeeds eta heta b x)
    (fun b => fullSeeds_typed eta heta b x) _ lam.property (Frame.rank_le_top lam.val) n

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.GenericTablesFiniteContexts
section


noncomputable section
open Set

namespace FSCofinality.GenericTables

/-- A finite subset of any separated family is separated by finitely many
actual tests. No choice of semantic quotient representatives occurs here. -/
theorem finite_separating_tests {X T Y : Type*} (f : T → X → Y)
    (hsep : ∀ x y, x ≠ y → ∃ t, f t x ≠ f t y) (F : Finset X) :
    ∃ S : Finset T, ∀ x ∈ F, ∀ y ∈ F,
      (∀ t ∈ S, f t x = f t y) → x = y := by
  classical
  let S : Finset T := F.biUnion (fun x => F.biUnion (fun y =>
    if h : x ≠ y then {Classical.choose (hsep x y h)} else ∅))
  refine ⟨S,fun x hx y hy htests => ?_⟩
  by_contra hxy
  have ht : Classical.choose (hsep x y hxy) ∈ S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,Finset.mem_biUnion.mpr ⟨y,hy,?_⟩⟩
    simp only [dif_pos hxy,Finset.mem_singleton]
  exact (Classical.choose_spec (hsep x y hxy)) (htests _ ht)

theorem context_ext_of_all_rows {U V : Type*} [Nonempty U] (R : U → V → Bool)
    (hcol : Function.Injective (fun v => fun u => R u v)) (s t : List V)
    (h : ∀ u, s.map (R u) = t.map (R u)) : s = t := by
  have hlen : s.length = t.length := by
    have hh := congrArg List.length (h (Classical.arbitrary U))
    simpa only [List.length_map] using hh
  apply List.ext_getElem hlen
  intro i hi hi'
  apply hcol
  funext u
  have hh := congrArg (fun l : List Bool => l[i]?) (h u)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi',Option.map_some,Option.some.injEq] using hh

theorem matrix_eq_implies_row_eq {U V : Type*} (R : U → V → Bool)
    (rows : List U) (u : U) (hu : u ∈ rows) (s t : List V)
    (hm : contextMatrix (rows.map R) s = contextMatrix (rows.map R) t) :
    s.map (R u) = t.map (R u) := by
  obtain ⟨i,hi,hu⟩ := List.mem_iff_getElem.mp hu
  have hlen : s.length = t.length := congrArg (fun M : BoolMatrix => M.2.1) hm
  apply List.ext_getElem (by simpa only [List.length_map] using hlen)
  intro j hj hj'
  have hs : j < s.length := by simpa only [List.length_map] using hj
  have ht : j < t.length := by simpa only [List.length_map] using hj'
  have hrow : i < (rows.map R).length := by simpa only [List.length_map] using hi
  have hh := congrArg (fun M : BoolMatrix => M.entry i j) hm
  simpa only [contextMatrix_entry _ _ i j hrow hs,contextMatrix_entry _ _ i j hrow ht,
    List.getElem_map,hu] using hh

/-- The witnesses may be appended to an already fixed context and combined
with witnesses for other roles: only their membership in the final tuple matters. -/
theorem finite_context_witnesses {U V ι : Type*} [Nonempty U] [Fintype ι]
    (R : U → V → Bool) (hcol : Function.Injective (fun v => fun u => R u v))
    (s : ι → List V) :
    ∃ S : Finset U, ∀ rows : List U, (∀ u ∈ S, u ∈ rows) → ∀ i j,
      contextMatrix (rows.map R) (s i) = contextMatrix (rows.map R) (s j) → s i = s j := by
  classical
  have hsep (a b : List V) (hab : a ≠ b) : ∃ u : U, a.map (R u) ≠ b.map (R u) := by
    by_contra! h
    exact hab (context_ext_of_all_rows R hcol a b h)
  obtain ⟨S,hS⟩ := finite_separating_tests (fun u a => a.map (R u)) hsep
    (Finset.univ.image s)
  refine ⟨S,fun rows hrows i j hm => ?_⟩
  apply hS (s i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    (s j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  intro u hu
  exact matrix_eq_implies_row_eq R rows u (hrows u hu) _ _ hm

end FSCofinality.GenericTables

end
end

-- Original module: FSCofinalityProof.GenericTablesTranspose
section


noncomputable section

namespace FSCofinality.GenericTables

def BoolMatrix.transpose (M : BoolMatrix) : BoolMatrix :=
  ⟨M.2.1,M.1,fun j i => M.2.2 i j⟩

@[simp] theorem BoolMatrix.transpose_transpose (M : BoolMatrix) : M.transpose.transpose = M := by
  cases M with | mk l rest => cases rest; rfl

theorem BoolMatrix.ext (M N : BoolMatrix) (hl : M.1 = N.1) (hm : M.2.1 = N.2.1)
    (he : ∀ i j, M.entry i j = N.entry i j) : M = N := by
  cases M with | mk l rest =>
    cases rest with | mk m f =>
      cases N with | mk l' rest' =>
        cases rest' with | mk m' g =>
          dsimp at hl hm
          subst l'
          subst m'
          have hfg : f = g := by
            funext i j
            have hh := he i j
            simpa only [BoolMatrix.entry,dif_pos i.isLt,dif_pos j.isLt] using hh
          rw [hfg]

theorem transpose_contextMatrix {U V : Type*} (R : U → V → Bool) (t : List U) (s : List V) :
    (contextMatrix (t.map R) s).transpose = contextMatrix (s.map (fun v u => R u v)) t := by
  apply BoolMatrix.ext
  · simp only [BoolMatrix.transpose,contextMatrix,List.length_map]
  · simp only [BoolMatrix.transpose,contextMatrix,List.length_map]
  · intro i j
    by_cases hi : i < s.length <;> by_cases hj : j < t.length
    all_goals simp [BoolMatrix.entry,BoolMatrix.transpose,contextMatrix,hi,hj]

/-- The dual witness lemma supplies columns distinguishing every finite
family of upper tuples. These are the same new raw context entries used
in the lower roles, so finite witness sets can be combined. -/
theorem finite_column_witnesses {U V ι : Type*} [Nonempty V] [Fintype ι]
    (R : U → V → Bool) (hrow : Function.Injective R) (t : ι → List U) :
    ∃ S : Finset V, ∀ columns : List V, (∀ v ∈ S, v ∈ columns) → ∀ i j,
      contextMatrix ((t i).map R) columns = contextMatrix ((t j).map R) columns → t i = t j := by
  obtain ⟨S,hS⟩ := finite_context_witnesses (fun v u => R u v) hrow t
  refine ⟨S,fun columns hcols i j hm => ?_⟩
  apply hS columns hcols i j
  have hh := congrArg BoolMatrix.transpose hm
  simpa only [transpose_contextMatrix] using hh

end FSCofinality.GenericTables

end
end

-- Original module: FSCofinalityProof.TokenNamedRecovery
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.Tokens
open GenericTables

theorem contextMatrix_map {U V W Z : Type} (R : W → Z → Bool)
    (f : U → W) (g : V → Z) (s : List U) (t : List V) :
    contextMatrix (s.map (fun u v => R (f u) (g v))) t =
      contextMatrix ((s.map f).map R) (t.map g) := by
  apply BoolMatrix.ext
  · simp only [contextMatrix,List.length_map]
  · simp only [contextMatrix,List.length_map]
  · intro i j
    by_cases hi : i < s.length <;> by_cases hj : j < t.length
    all_goals simp [BoolMatrix.entry,contextMatrix,hi,hj]

theorem ordinaryEdge_map {U V W Z : Type} (A : Table) (e : ℕ) (R : W → Z → Bool)
    (f : U → W) (g : V → Z) (v : Token U) (w : Token V) :
    ordinaryEdge A e (fun u v => R (f u) (g v)) v w =
      ordinaryEdge A e R (mapToken f v) (mapToken g w) := by
  unfold ordinaryEdge
  rw [contextMatrix_map]
  rfl

theorem named_ordinary_recovery {U X Y V W : Type}
    {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A) (e : ℕ)
    (nx : X → U) (ny : Y → U) (nv : V → U) (nw : W → U) (R : U → U → Bool)
    (f : Token V ≃ Token W) (hf : ∀ q, mapToken nw (f q) = mapToken nv q)
    (hinj : (range nx ∪ range ny).InjOn (fun u => fun q : V => R u (nv q)))
    (v : Token X) (w : Token Y)
    (hedge : ∀ q, ordinaryEdge A e (fun u t => R (nx u) (nv t)) v q =
      ordinaryEdge A e (fun u t => R (ny u) (nw t)) w (f q)) :
    mapToken nx v = mapToken ny w := by
  have hsig : (v.1.map (fun u => fun q : V => R (nx u) (nv q)),v.2) =
      (w.1.map (fun u => fun q : V => R (ny u) (nv q)),w.2) := by
    apply pointed_context_injective hA e
    funext q
    have h := hedge q
    rw [ordinaryEdge_map A e R ny nw, hf] at h
    rw [← ordinaryEdge_map A e R ny nv] at h
    exact h
  have hnames : (v.1.map nx).map (fun u => fun q : V => R u (nv q)) =
      (w.1.map ny).map (fun u => fun q : V => R u (nv q)) := by
    simpa only [List.map_map,Function.comp_def] using congrArg Prod.fst hsig
  apply Prod.ext
  · apply list_eq_of_injOn _ _ hinj _ _ _ _ hnames
    · intro u hu
      obtain ⟨z,_,rfl⟩ := List.mem_map.mp hu
      exact Or.inl (mem_range_self z)
    · intro u hu
      obtain ⟨z,_,rfl⟩ := List.mem_map.mp hu
      exact Or.inr (mem_range_self z)
  · exact congrArg (fun p : List (V → Bool) × ℕ => p.2) hsig

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.RawObjectsRestrictedRecovery
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.RawObjects
open Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
    (lam : Ordinal.{0}) (hlam : IsSuccLimit lam) (htop : lam ≤ Frame.top eta)

def restrictedProfile (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta))
    (hsub : ∀ b hb, lower b hb ⊆ fullLower eta heta lam b hb) (n : ℕ)
    (u : Ambient eta heta) (c : Column eta heta lam hlam lower n) : Bool :=
  ambientProfile eta heta lam hlam htop n u (mapColumn eta heta lam hlam hsub n c)

theorem restrictedProfile_rowObject
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta))
    (hsub : ∀ b hb, lower b hb ⊆ fullLower eta heta lam b hb) (n : ℕ)
    (r : LimitRow eta heta lam hlam lower) (c : Column eta heta lam hlam lower n) :
    restrictedProfile eta heta lam hlam htop lower hsub n
      (rowObject eta heta lam hlam lower htop r) c = profile eta heta lam hlam lower n r c :=
  ambientProfile_restricted eta heta lam hlam htop hsub n r c

theorem restrictedFullProfile_injOn
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta))
    (hsub : ∀ b hb, lower b hb ⊆ fullLower eta heta lam b hb) :
    (LimitSet eta heta lam hlam lower).InjOn
      (fun u => fun n => restrictedProfile eta heta lam hlam htop lower hsub n u) := by
  intro u hu v hv huv
  obtain ⟨r,rfl⟩ := exists_rowObject_of_mem_limitSet eta heta lam hlam lower htop hu
  obtain ⟨s,rfl⟩ := exists_rowObject_of_mem_limitSet eta heta lam hlam lower htop hv
  have heq : (fun n => profile eta heta lam hlam lower n r) =
      (fun n => profile eta heta lam hlam lower n s) := by
    funext n c
    have h := congrFun (congrFun huv n) c
    simpa only [restrictedProfile_rowObject] using h
  exact congrArg (rowObject eta heta lam hlam lower htop)
    (fullProfile_injective eta heta lam hlam lower heq)

theorem restrictedProfile_propagate
    (lower : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta))
    (hsub : ∀ b hb, lower b hb ⊆ fullLower eta heta lam b hb) (n : ℕ)
    (u : Ambient eta heta) (c : Column eta heta lam hlam lower n) :
    restrictedProfile eta heta lam hlam htop lower hsub (n+1) u
      (propagate eta heta lam hlam lower n c) =
        restrictedProfile eta heta lam hlam htop lower hsub n u c := by
  unfold restrictedProfile
  rw [mapColumn_propagate,ambientProfile_propagate]

theorem restricted_limit_recovery
    {D : ℕ → Set ℕ} {A : Table} (hA : GenericOn D A) (e : ℕ → ℕ)
    (lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta))
    (hsub : ∀ b hb, lower b hb ⊆ fullLower eta heta lam b hb)
    (hsub' : ∀ b hb, upper b hb ⊆ fullLower eta heta lam b hb)
    (hLU : lower=upper) (PX PY : Set (Ambient eta heta))
    (hPX : PX ⊆ LimitSet eta heta lam hlam lower)
    (hPY : PY ⊆ LimitSet eta heta lam hlam upper)
    (f : ∀ n, Token (Column eta heta lam hlam lower n) ≃ Token (Column eta heta lam hlam upper n))
    (hf : ∀ n q, mapToken (encodeColumn eta heta lam hlam upper n) (f n q) =
      mapToken (encodeColumn eta heta lam hlam lower n) q)
    (v : Token PX) (w : Token PY)
    (hedge : ∀ n q,
      branchEdge (fun n (u : PX) => restrictedProfile eta heta lam hlam htop lower hsub n u.val)
        A (e n) n v q =
      branchEdge (fun n (u : PY) => restrictedProfile eta heta lam hlam htop upper hsub' n u.val)
        A (e n) n w (f n q)) : name PX v = name PY w := by
  subst upper
  have hfId (n : ℕ) (q : Token (Column eta heta lam hlam lower n)) : f n q = q := by
    have h := hf n q
    apply Prod.ext
    · exact List.map_injective_iff.mpr (encodeColumn_injective eta heta lam hlam lower htop n)
        (congrArg Prod.fst h)
    · exact congrArg (fun p : Token (Ambient eta heta) => p.2) h
  apply limit_recovery_between_pools hA e PX PY
    (restrictedProfile eta heta lam hlam htop lower hsub)
    (propagate eta heta lam hlam lower)
  · intro n u _ c
    exact restrictedProfile_propagate eta heta lam hlam htop lower hsub n u c
  · apply (restrictedFullProfile_injOn eta heta lam hlam htop lower hsub).mono
    exact union_subset hPX hPY
  · intro n q
    simpa only [hfId] using hedge n q

end FSCofinality.RawObjects

end
end

-- Original module: FSCofinalityProof.CosetConstructionSemanticRecovery
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def PreservesDiagram {x y : (fsTower eta).Carrier} (e : Vertex eta heta x ≃ Vertex eta heta y) : Prop :=
  ∀ s a, diagram eta heta (bottom eta heta) x s a = diagram eta heta (bottom eta heta) y s (e ∘ a)

def inducedTokenEquiv {x y : (fsTower eta).Carrier} (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : PreservesDiagram eta heta e) (s : TokenSort eta) :
    Token (raw eta heta x s) ≃ Token (raw eta heta y s) :=
  sortedTokenEquiv eta heta e (preserves_sort eta heta (bottom eta heta) e he) s

def Recovers {x y : (fsTower eta).Carrier} (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : PreservesDiagram eta heta e) (s : TokenSort eta) : Prop :=
  ∀ v, tokenName eta heta y s (inducedTokenEquiv eta heta e he s v) = tokenName eta heta x s v

theorem recovers_zero {x y : (fsTower eta).Carrier} (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : PreservesDiagram eta heta e) (hQ : ∀ n, e (.inl n) = .inl n) :
    Recovers eta heta e he (zeroSort eta) := fun v => (qFixed_bottom_name eta heta e he hQ v).symm

theorem mainPool_eq_of_recovers {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (a : MainIndex eta) (hrec : Recovers eta heta e he (.inl a)) :
    mainPool eta heta x (Frame.rank a) = mainPool eta heta y (Frame.rank a) := by
  apply pools_eq_of_named_bijection _ _ (inducedTokenEquiv eta heta e he (.inl a))
  exact hrec

def sortRank : TokenSort eta → Ordinal.{0}
  | .inl a => Frame.rank a
  | .inr (lam,n) => Frame.delta eta (Frame.rank lam.val) lam.property n

theorem ordinary_rank_lt (r : OrdinaryRole eta) :
    sortRank eta (colSort eta r) < sortRank eta (rowSort eta r) := by
  cases r with
  | inl a =>
    simp only [sortRank,rowSort,colSort,mainSort,Frame.rank_ofOrdinal]
    exact lt_add_one _
  | inr c =>
    rcases c with ⟨lam,n⟩
    simp only [sortRank,rowSort,colSort,mainSort,Frame.rank_ofOrdinal]
    simpa only [Frame.rho,Frame.delta,add_assoc,one_add_one_eq_two] using
      lt_add_one (Frame.sigma eta (Frame.rank lam.val) lam.property n + 1)

theorem branch_rank_lt (lam : LimitIndex eta) (n : ℕ) :
    sortRank eta (.inr (lam,n)) < sortRank eta (.inl lam.val) := Frame.delta_lt eta _ lam.property n

theorem ordinaryMatrix_eq_names (x : (fsTower eta).Carrier) (r : OrdinaryRole eta)
    (u : raw eta heta x (rowSort eta r)) (v : raw eta heta x (colSort eta r)) :
    ordinaryMatrix eta heta x r u v =
      ordinaryRaw (rawName eta heta x (rowSort eta r) u) (rawName eta heta x (colSort eta r) v) := by
  cases r <;> rfl

theorem recovers_ordinary_row {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (r : OrdinaryRole eta) (hcol : Recovers eta heta e he (colSort eta r))
    (hinj : (range (rawName eta heta x (rowSort eta r)) ∪
      range (rawName eta heta y (rowSort eta r))).InjOn
        (fun u => fun q : raw eta heta x (colSort eta r) =>
          ordinaryRaw u (rawName eta heta x (colSort eta r) q))) :
    Recovers eta heta e he (rowSort eta r) := by
  intro v
  apply Eq.symm
  apply named_ordinary_recovery genericTable_generic (roleNumber eta heta (.inl r))
    (rawName eta heta x (rowSort eta r)) (rawName eta heta y (rowSort eta r))
    (rawName eta heta x (colSort eta r)) (rawName eta heta y (colSort eta r)) ordinaryRaw
    (inducedTokenEquiv eta heta e he (colSort eta r)) hcol hinj v
  intro q
  have hx : ordinaryMatrix eta heta x r = fun u v =>
      ordinaryRaw (rawName eta heta x (rowSort eta r) u) (rawName eta heta x (colSort eta r) v) :=
    funext (fun u => funext (ordinaryMatrix_eq_names eta heta x r u))
  have hy : ordinaryMatrix eta heta y r = fun u v =>
      ordinaryRaw (rawName eta heta y (rowSort eta r) u) (rawName eta heta y (colSort eta r) v) :=
    funext (fun u => funext (ordinaryMatrix_eq_names eta heta y r u))
  simpa only [ordinary,hx,hy] using
    preserves_ordinary eta heta (bottom eta heta) e he r v q

theorem ordinary_names_injOn {X Y V : Type} (l : Frame.Layer eta)
    (nx : X → Ambient eta heta) (ny : Y → Ambient eta heta) (nv : V → Ambient eta heta)
    (hcollection : ∀ u ∈ range nx ∪ range ny, ∃ z, u = collection l z)
    (hdown : ∀ u ∈ range nx ∪ range ny, ∀ c, Member c u → ∃ q, nv q = c) :
    (range nx ∪ range ny).InjOn (fun u => fun q => ordinaryRaw u (nv q)) := by
  intro u hu v hv huv
  obtain ⟨s,rfl⟩ := hcollection u hu
  obtain ⟨t,rfl⟩ := hcollection v hv
  apply collection_ext
  intro c
  constructor
  · intro hc
    obtain ⟨q,hq⟩ := hdown _ hu c hc
    have h := decide_eq_decide.mp (congrFun huv q)
    exact hq ▸ h.mp (hq.symm ▸ hc)
  · intro hc
    obtain ⟨q,hq⟩ := hdown _ hv c hc
    have h := decide_eq_decide.mp (congrFun huv q)
    exact hq ▸ h.mpr (hq.symm ▸ hc)

def colMainIndex : OrdinaryRole eta → MainIndex eta
  | .inl a => a.val
  | .inr (lam,n) => Frame.ofOrdinal eta (Frame.rho eta (Frame.rank lam.val) lam.property n)
      ((Frame.rho_lt eta _ lam.property n).le.trans (Frame.rank_le_top lam.val))

theorem colSort_eq (r : OrdinaryRole eta) : colSort eta r = .inl (colMainIndex eta r) := by
  cases r <;> rfl

theorem colMainIndex_rank (r : OrdinaryRole eta) :
    Frame.rank (colMainIndex eta r) = sortRank eta (colSort eta r) := by rw [colSort_eq]; rfl

theorem ordinary_rank_succ (r : OrdinaryRole eta) :
    sortRank eta (rowSort eta r) = sortRank eta (colSort eta r)+1 := by
  cases r with
  | inl a => simp only [rowSort,colSort,sortRank,mainSort,Frame.rank_ofOrdinal]
  | inr c =>
    simp only [rowSort,colSort,sortRank,mainSort,Frame.rank_ofOrdinal,
      Frame.delta,Frame.rho,add_assoc,one_add_one_eq_two]

theorem rawName_ordinary_row_mem (x : (fsTower eta).Carrier) (r : OrdinaryRole eta)
    (u : raw eta heta x (rowSort eta r)) :
    rawName eta heta x (rowSort eta r) u ∈ mainPool eta heta x (sortRank eta (rowSort eta r)) := by
  cases r with
  | inl a => simpa only [rowSort,rawName,sortRank,mainSort,Frame.rank_ofOrdinal] using u.property
  | inr c => exact (pool_encodeColumn eta heta _ _ c.1.property (Frame.rank_le_top c.1.val) c.2 u).1

theorem rawName_ordinary_member_lower (x : (fsTower eta).Carrier) (r : OrdinaryRole eta)
    (u : raw eta heta x (rowSort eta r)) {c : Ambient eta heta}
    (hc : Member c (rawName eta heta x (rowSort eta r) u)) :
    c ∈ mainPool eta heta x (sortRank eta (colSort eta r)) := by
  cases r with
  | inl a =>
    apply pool_member_lower eta heta _ (Frame.rank a.val)
      (fun _ h _ hm => fullSeeds_successor_downward eta heta (Frame.rank a.val) x h hm) ?_ hc
    simpa only [rowSort,raw,mainSort,Frame.rank_ofOrdinal] using u.property
  | inr q =>
    have h := (pool_encodeColumn eta heta _ _ q.1.property (Frame.rank_le_top q.1.val) q.2 u).2 c hc
    simpa only [colSort,sortRank,mainSort,Frame.rank_ofOrdinal] using h

theorem rawName_col_surjective (x : (fsTower eta).Carrier) (r : OrdinaryRole eta)
    {c : Ambient eta heta} (hc : c ∈ mainPool eta heta x (sortRank eta (colSort eta r))) :
    ∃ q : raw eta heta x (colSort eta r), rawName eta heta x (colSort eta r) q = c := by
  rw [colSort_eq] at hc ⊢
  exact ⟨⟨c,hc⟩,rfl⟩

theorem recovers_ordinary {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (r : OrdinaryRole eta) (hcol : Recovers eta heta e he (colSort eta r)) :
    Recovers eta heta e he (rowSort eta r) := by
  have hpool : mainPool eta heta x (sortRank eta (colSort eta r)) =
      mainPool eta heta y (sortRank eta (colSort eta r)) := by
    rw [colSort_eq] at hcol ⊢
    exact mainPool_eq_of_recovers eta heta e he _ hcol
  apply recovers_ordinary_row eta heta e he r hcol
  apply ordinary_names_injOn eta heta (level eta (sortRank eta (rowSort eta r)))
  · rintro u (⟨u,rfl⟩ | ⟨u,rfl⟩)
    · have hu := rawName_ordinary_row_mem eta heta x r u
      rw [ordinary_rank_succ] at hu
      have h := pool_successor_collection eta heta _ (fun b => fullSeeds_typed eta heta b x)
        (sortRank eta (colSort eta r)) hu
      simpa only [ordinary_rank_succ] using h
    · have hu := rawName_ordinary_row_mem eta heta y r u
      rw [ordinary_rank_succ] at hu
      have h := pool_successor_collection eta heta _ (fun b => fullSeeds_typed eta heta b y)
        (sortRank eta (colSort eta r)) hu
      simpa only [ordinary_rank_succ] using h
  · rintro u (⟨u,rfl⟩ | ⟨u,rfl⟩) c hc
    · exact rawName_col_surjective eta heta x r (rawName_ordinary_member_lower eta heta x r u hc)
    · apply rawName_col_surjective eta heta x r
      rw [hpool]
      exact rawName_ordinary_member_lower eta heta y r u hc

theorem recovers_limit {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (lam : LimitIndex eta)
    (hpool : ∀ b < Frame.rank lam.val, mainPool eta heta x b = mainPool eta heta y b)
    (hcols : ∀ n, Recovers eta heta e he (.inr (lam,n))) :
    Recovers eta heta e he (.inl lam.val) := by
  have hLU : lowerPools eta heta x (Frame.rank lam.val) =
      lowerPools eta heta y (Frame.rank lam.val) := funext (fun b => funext (hpool b))
  intro v
  apply Eq.symm
  apply restricted_limit_recovery eta heta (Frame.rank lam.val) lam.property (Frame.rank_le_top lam.val)
    genericTable_generic (fun n => roleNumber eta heta (.inr (lam,n)))
    (lowerPools eta heta x _) (lowerPools eta heta y _)
    (ambientLower eta heta x _) (ambientLower eta heta y _) hLU
    (mainPool eta heta x _) (mainPool eta heta y _)
    (mainPool_limit_subset_limitSet eta heta x _ lam.property)
    (mainPool_limit_subset_limitSet eta heta y _ lam.property)
    (fun n => inducedTokenEquiv eta heta e he (.inr (lam,n))) hcols v
  intro n q
  exact preserves_branch eta heta (bottom eta heta) e he lam n v q

theorem mainIndex_rank_injective : Function.Injective (Frame.rank : MainIndex eta → Ordinal.{0}) := by
  intro a b hab
  have ha := Frame.ofOrdinal_rank a
  have hb := Frame.ofOrdinal_rank b
  rw [← ha,← hb]
  congr 1

/-- Simultaneous recovery follows the actual semantic decoding ranks.
Dedicated column sorts are recovered at their own successor rank, before
the higher limit main sort can query them. -/
theorem recovers_all {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (hQ : ∀ n, e (.inl n) = .inl n) : ∀ s, Recovers eta heta e he s := by
  have hall (a : Ordinal.{0}) : ∀ s, sortRank eta s = a → Recovers eta heta e he s := by
    refine Ordinal.induction (p := fun a => ∀ s, sortRank eta s = a → Recovers eta heta e he s)
      a (fun gamma ih s hs => ?_)
    cases s with
    | inr c =>
      apply recovers_ordinary eta heta e he (.inr c)
      apply ih (sortRank eta (colSort eta (.inr c))) ?_ _ rfl
      rw [← hs]
      exact ordinary_rank_lt eta (.inr c)
    | inl l =>
      rcases Ordinal.zero_or_succ_or_isSuccLimit (Frame.rank l) with hzero | ⟨b,hb⟩ | hlim
      · have hl : l = Frame.ofOrdinal eta 0 zero_le :=
          mainIndex_rank_injective eta (hzero.trans (Frame.rank_ofOrdinal eta 0 zero_le).symm)
        subst l
        exact recovers_zero eta heta e he hQ
      · have hbl : Frame.rank l = b+1 := by simpa only [succ_eq_add_one] using hb.symm
        have hbtop : b+1 ≤ Frame.top eta := hbl ▸ Frame.rank_le_top l
        have hb' : b ≤ Frame.top eta := (le_self_add : b ≤ b+1).trans hbtop
        let r : SuccessorIndex eta := ⟨Frame.ofOrdinal eta b hb',by simpa using hbtop⟩
        have hrow : rowSort eta (.inl r) = .inl l := by
          apply congrArg Sum.inl
          apply mainIndex_rank_injective eta
          simp only [rowSort,mainSort,Frame.rank_ofOrdinal,r,hbl]
        rw [← hrow]
        apply recovers_ordinary eta heta e he (.inl r)
        apply ih (sortRank eta (colSort eta (.inl r))) ?_ _ rfl
        rw [← hs,← hrow]
        exact ordinary_rank_lt eta (.inl r)
      · let lam : LimitIndex eta := ⟨l,hlim⟩
        apply recovers_limit eta heta e he lam
        · intro b hb
          have hbtop : b ≤ Frame.top eta := hb.le.trans (Frame.rank_le_top l)
          let k := Frame.ofOrdinal eta b hbtop
          have hk : Recovers eta heta e he (.inl k) :=
            ih b (by rw [← hs]; exact hb) (.inl k) (Frame.rank_ofOrdinal eta b hbtop)
          simpa only [k,Frame.rank_ofOrdinal] using mainPool_eq_of_recovers eta heta e he k hk
        · intro n
          exact ih (sortRank eta (.inr (lam,n)))
            (by rw [← hs]; exact branch_rank_lt eta lam n) (.inr (lam,n)) rfl
  intro s
  exact hall (sortRank eta s) s rfl

theorem qFixed_reflects {x y : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta y) (he : PreservesDiagram eta heta e)
    (hQ : ∀ n, e (.inl n) = .inl n) : (fsTower eta).rel x y := by
  apply (topPool_eq_iff eta heta x y).mp
  let t := Frame.ofOrdinal eta (Frame.top eta) le_rfl
  have h := mainPool_eq_of_recovers eta heta e he t (recovers_all eta heta e he hQ (.inl t))
  simpa only [t,Frame.rank_ofOrdinal] using h

theorem qFixed_rigid {x : (fsTower eta).Carrier}
    (e : Vertex eta heta x ≃ Vertex eta heta x) (he : PreservesDiagram eta heta e)
    (hQ : ∀ n, e (.inl n) = .inl n) : e = Equiv.refl _ := by
  apply Equiv.ext
  intro v
  cases v with
  | inl n => exact hQ n
  | inr v =>
    rcases v with ⟨s,v⟩
    rw [sortedTokenEquiv_commutes eta heta e (preserves_sort eta heta (bottom eta heta) e he)]
    have hv := (tokenName_injective eta heta x s) (recovers_all eta heta e he hQ s v)
    exact congrArg (fun w : Token (raw eta heta x s) => (Sum.inr ⟨s,w⟩ : Vertex eta heta x)) hv

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.TokenEquivalences
section


set_option autoImplicit false
noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

def tokenCongr {U V : Type} (f : U ≃ V) : Token U ≃ Token V :=
  Equiv.prodCongr (Equiv.listEquivOfEquiv f) (Equiv.refl ℕ)

theorem tokenCongr_apply {U V : Type} (f : U ≃ V) (v : Token U) :
    tokenCongr f v = mapToken f v := rfl

theorem ordinaryEdge_congr {U V U' V' : Type} (R : U → V → Bool) (R' : U' → V' → Bool)
    (f : U → U') (g : V → V') (hR : ∀ u v, R u v = R' (f u) (g v))
    (A : Table) (e : ℕ) (v : Token U) (w : Token V) :
    ordinaryEdge A e R v w = ordinaryEdge A e R' (mapToken f v) (mapToken g w) := by
  have hh : R = fun u v => R' (f u) (g v) := funext (fun u => funext (hR u))
  rw [hh]
  exact ordinaryEdge_map A e R' f g v w

theorem activeProfiles_precompose {U U' : Type} {C C' : ℕ → Type}
    (p : ∀ n, U → C n → Bool) (p' : ∀ n, U' → C' n → Bool)
    (f : U → U') (g : ∀ n, C n → C' n)
    (hp : ∀ n u c, p n u c = p' n (f u) (g n c)) (v : Token U) (n : ℕ) :
    (activeProfiles p' (mapToken f v) n).map (fun q c => q (g n c)) = activeProfiles p v n := by
  simp only [activeProfiles,activeTuple_mapToken,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro u _
  exact funext (fun c => (hp n u c).symm)

theorem limit_R_congr {U U' : Type} {C C' : ℕ → Type}
    (p : ∀ n, U → C n → Bool) (p' : ∀ n, U' → C' n → Bool)
    (f : U → U') (g : ∀ n, C n ≃ C' n)
    (hp : ∀ n u c, p n u c = p' n (f u) (g n c)) (v w : Token U) (n : ℕ) :
    R p n v w ↔ R p' n (mapToken f v) (mapToken f w) := by
  have hinj : Function.Injective (fun q : C' n → Bool => fun c => q (g n c)) := by
    intro q r hqr
    funext c
    obtain ⟨c,rfl⟩ := (g n).surjective c
    exact congrFun hqr c
  have hi := List.map_injective_iff.mpr hinj
  have hv := activeProfiles_precompose p p' f (fun n => g n) hp v n
  have hw := activeProfiles_precompose p p' f (fun n => g n) hp w n
  simp only [R,localCode_mapToken]
  constructor
  · rintro ⟨hl,hp⟩
    exact ⟨hl,hi (hv.trans (hp.trans hw.symm))⟩
  · rintro ⟨hl,hp⟩
    exact ⟨hl,hv.symm.trans ((congrArg (List.map (fun q c => q (g n c))) hp).trans hw)⟩

theorem branchEdge_congr {U U' : Type} {C C' : ℕ → Type}
    (p : ∀ n, U → C n → Bool) (p' : ∀ n, U' → C' n → Bool)
    (f : U → U') (g : ∀ n, C n → C' n)
    (hp : ∀ n u c, p n u c = p' n (f u) (g n c))
    (A : Table) (e n : ℕ) (v : Token U) (w : Token (C n)) :
    branchEdge p A e n v w = branchEdge p' A e n (mapToken f v) (mapToken (g n) w) := by
  have hh : p n = fun u c => p' n (f u) (g n c) := funext (fun u => funext (hp n u))
  simp only [branchEdge,activeProfiles,activeTuple_mapToken,localCode_mapToken]
  rw [hh,contextMatrix_map]
  rfl

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.CosetConstructionPoolEquivalences
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open RawObjects Tokens GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def columnCongr (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta)}
    (h : lower=upper) (n : ℕ) : Column eta heta lam hlam lower n ≃ Column eta heta lam hlam upper n :=
  Equiv.cast (congrArg (fun L => Column eta heta lam hlam L n) h)

theorem columnCongr_encode (lam : Ordinal.{0}) (hlam : IsSuccLimit lam)
    {lower upper : ∀ b : Ordinal.{0}, b < lam → Set (Ambient eta heta)}
    (h : lower=upper) (n : ℕ) (c : Column eta heta lam hlam lower n) :
    encodeColumn eta heta lam hlam upper n (columnCongr eta heta lam hlam h n c) =
      encodeColumn eta heta lam hlam lower n c := by subst upper; rfl

def rawEquiv {x y : (fsTower eta).Carrier} (h : (fsTower eta).rel x y) :
    (s : TokenSort eta) → raw eta heta x s ≃ raw eta heta y s
  | .inl a => Equiv.setCongr (pools_congr eta heta (Frame.rank a) h)
  | .inr (lam,n) => columnCongr eta heta _ lam.property
      (funext (fun b => funext (fun _ => pools_congr eta heta b h))) n

theorem rawEquiv_names {x y : (fsTower eta).Carrier} (h : (fsTower eta).rel x y)
    (s : TokenSort eta) (u : raw eta heta x s) :
    rawName eta heta y s (rawEquiv eta heta h s u) = rawName eta heta x s u := by
  cases s with
  | inl a => rfl
  | inr c =>
    exact columnCongr_encode eta heta _ c.1.property
      (funext (fun b => funext (fun _ => pools_congr eta heta b h))) c.2 u

theorem limitProfile_semantic_congr (x y : (fsTower eta).Carrier)
    (lam : LimitIndex eta) (n : ℕ)
    (r : raw eta heta x (.inl lam.val)) (s : raw eta heta y (.inl lam.val))
    (c : raw eta heta x (.inr (lam,n))) (d : raw eta heta y (.inr (lam,n)))
    (hrow : r.val=s.val)
    (hcol : rawName eta heta x (.inr (lam,n)) c = rawName eta heta y (.inr (lam,n)) d) :
    limitProfile eta heta x lam n r c = limitProfile eta heta y lam n s d := by
  rw [limitProfile_local,limitProfile_local]
  apply profile_semantic_congr eta heta _ lam.property (Frame.rank_le_top lam.val) n
  · exact (rowObject_localLimitRow eta heta x lam r).trans
      (hrow.trans (rowObject_localLimitRow eta heta y lam s).symm)
  · exact hcol

theorem rawEquiv_profile {x y : (fsTower eta).Carrier} (h : (fsTower eta).rel x y)
    (lam : LimitIndex eta) (n : ℕ) (r : raw eta heta x (.inl lam.val))
    (c : raw eta heta x (.inr (lam,n))) :
    limitProfile eta heta x lam n r c = limitProfile eta heta y lam n
      (rawEquiv eta heta h (.inl lam.val) r) (rawEquiv eta heta h (.inr (lam,n)) c) := by
  apply limitProfile_semantic_congr eta heta x y lam n
  · exact (rawEquiv_names eta heta h (.inl lam.val) r).symm
  · exact (rawEquiv_names eta heta h (.inr (lam,n)) c).symm

theorem rawEquiv_bottom {x y : (fsTower eta).Carrier} (h : (fsTower eta).rel x y)
    (v : Token (raw eta heta x (zeroSort eta))) :
    bottom eta heta x v = bottom eta heta y (mapToken (rawEquiv eta heta h (zeroSort eta)) v) := by
  have hn : tokenName eta heta y (zeroSort eta) (mapToken (rawEquiv eta heta h (zeroSort eta)) v) =
      tokenName eta heta x (zeroSort eta) v := by
    apply Prod.ext
    · simp only [tokenName,mapToken,List.map_map,Function.comp_def]
      apply List.map_congr_left
      intro u _
      exact rawEquiv_names eta heta h (zeroSort eta) u
    · rfl
  have hd : decodedBottom eta heta y (mapToken (rawEquiv eta heta h (zeroSort eta)) v) =
      decodedBottom eta heta x v := by
    apply Prod.ext
    · have hh := congrArg Prod.fst hn
      have hm := congrArg (List.map (decodeAtom eta heta)) hh
      simpa only [tokenName,mapToken,decodedBottom,List.map_map,Function.comp_def,rawName,zeroSort,mainSort] using hm
    · rfl
  exact congrArg (fun t : Token BottomValueSpace => bottomListMap t.1 t.2) hd.symm

def vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) : Vertex eta heta x ≃ Vertex eta heta y :=
  Equiv.sumCongr (Equiv.refl ℕ) (Equiv.sigmaCongrRight (fun s => tokenCongr (f s)))

@[simp] theorem vertexCongr_coordinate {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (n : ℕ) :
    vertexCongr eta heta f (.inl n) = .inl n := rfl

@[simp] theorem vertexCongr_token {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (s : TokenSort eta) (v : Token (raw eta heta x s)) :
    vertexCongr eta heta f (.inr ⟨s,v⟩) = .inr ⟨s,mapToken (f s) v⟩ := rfl

@[simp] theorem sortOf_vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (v : Vertex eta heta x) :
    sortOf eta heta (vertexCongr eta heta f v) = sortOf eta heta v := by
  cases v <;> rfl

theorem tokenAt_vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (s : TokenSort eta) (v : Vertex eta heta x) :
    tokenAt eta heta s (vertexCongr eta heta f v) =
      (tokenAt eta heta s v).map (mapToken (f s)) := by
  cases v with
  | inl n => rfl
  | inr v =>
    rcases v with ⟨t,v⟩
    by_cases ht : t=s
    · subst t
      simp only [vertexCongr_token,tokenAt_inr,Option.map_some]
    · simp only [vertexCongr_token,tokenAt,dif_neg ht,Option.map_none]

@[simp] theorem coordinateAt_vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (v : Vertex eta heta x) :
    coordinateAt eta heta (vertexCongr eta heta f v) = coordinateAt eta heta v := by
  cases v <;> rfl

theorem edgeAt_vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s) (s t : TokenSort eta)
    (R : Token (raw eta heta x s) → Token (raw eta heta x t) → Bool)
    (R' : Token (raw eta heta y s) → Token (raw eta heta y t) → Bool)
    (hR : ∀ v w, R v w = R' (mapToken (f s) v) (mapToken (f t) w))
    (u v : Vertex eta heta x) : edgeAt eta heta s t R u v =
      edgeAt eta heta s t R' (vertexCongr eta heta f u) (vertexCongr eta heta f v) := by
  unfold edgeAt
  rw [tokenAt_vertexCongr,tokenAt_vertexCongr]
  cases hu : tokenAt eta heta s u <;> cases hv : tokenAt eta heta t v <;>
    simp only [Option.map_none,Option.map_some,Option.elim_none,Option.elim_some]
  exact hR _ _

theorem diagram_vertexCongr {x y : (fsTower eta).Carrier}
    (f : ∀ s, raw eta heta x s ≃ raw eta heta y s)
    (hO : ∀ r u v, ordinaryMatrix eta heta x r u v =
      ordinaryMatrix eta heta y r (f (rowSort eta r) u) (f (colSort eta r) v))
    (hP : ∀ lam n u c, limitProfile eta heta x lam n u c =
      limitProfile eta heta y lam n (f (.inl lam.val) u) (f (.inr (lam,n)) c))
    (hB : ∀ v, bottom eta heta x v = bottom eta heta y (mapToken (f (zeroSort eta)) v)) :
    ∀ s a, diagram eta heta (bottom eta heta) x s a =
      diagram eta heta (bottom eta heta) y s (vertexCongr eta heta f ∘ a) := by
  intro s a
  rcases s with s | r | c | c | u
  · simp only [diagram,Function.comp_def,sortOf_vertexCongr]
  · apply edgeAt_vertexCongr eta heta f
    intro v w
    exact ordinaryEdge_congr _ _ _ _ (hO r) genericTable (roleNumber eta heta (.inl r)) v w
  · rcases c with ⟨lam,n⟩
    apply edgeAt_vertexCongr eta heta f
    intro v w
    exact branchEdge_congr _ _ _ _ (hP lam) genericTable (roleNumber eta heta (.inr (lam,n))) n v w
  · rcases c with ⟨lam,n⟩
    apply edgeAt_vertexCongr eta heta f
    intro v w
    exact decide_eq_decide.mpr (limit_R_congr _ _ (f (.inl lam.val))
      (fun n => f (.inr (lam,n))) (hP lam) v w n)
  · change (tokenAt eta heta (zeroSort eta) (a (0 : Fin 2))).elim false
      (fun r => (coordinateAt eta heta (a (1 : Fin 2))).elim false (bottom eta heta x r)) =
      (tokenAt eta heta (zeroSort eta) (vertexCongr eta heta f (a (0 : Fin 2)))).elim false
      (fun r => (coordinateAt eta heta (vertexCongr eta heta f (a (1 : Fin 2)))).elim false
        (bottom eta heta y r))
    rw [tokenAt_vertexCongr,coordinateAt_vertexCongr]
    cases ht : tokenAt eta heta (zeroSort eta) (a (0 : Fin 2)) <;>
      cases hq : coordinateAt eta heta (a (1 : Fin 2)) <;>
      simp only [Option.map_none,Option.map_some,Option.elim_none,Option.elim_some]
    exact congrFun (hB _) _

theorem source_equivalent_qFixed {x y : (fsTower eta).Carrier} (h : (fsTower eta).rel x y) :
    ∃ e : Vertex eta heta x ≃ Vertex eta heta y,
      (∀ s a, diagram eta heta (bottom eta heta) x s a =
        diagram eta heta (bottom eta heta) y s (e ∘ a)) ∧ ∀ n, e (.inl n) = .inl n := by
  refine ⟨vertexCongr eta heta (rawEquiv eta heta h),?_,fun _ => rfl⟩
  apply diagram_vertexCongr eta heta (rawEquiv eta heta h)
  · intro r u v
    rw [ordinaryMatrix_eq_names,ordinaryMatrix_eq_names,rawEquiv_names,rawEquiv_names]
  · exact rawEquiv_profile eta heta h
  · exact rawEquiv_bottom eta heta h

end FSCofinality.CosetConstruction.TokenModel

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

-- Original module: FSCofinalityProof.BorelBackAndForth
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

private theorem inverse_coordinates {L : CountableRelationalLanguage} {M N : Structures L}
    (b : ℕ → ℕ) (hb : ∀ n, attemptTree M N (initialSegment b n) = true) :
    (∀ i, b (2 * b (2*i)+1) = i) ∧ (∀ i, b (2 * b (2*i+1)) = i) := by
  have hpair (i : ℕ) {n : ℕ} (hn : 2*i < n) :
      (i,b (2*i)) ∈ pairsFrom 0 (initialSegment b n) := by
    simpa only [scheduledPair_even] using scheduledPair_mem_prefix b hn
  have hipair (i : ℕ) {n : ℕ} (hn : 2*i+1 < n) :
      (b (2*i+1),i) ∈ pairsFrom 0 (initialSegment b n) := by
    simpa only [scheduledPair_odd] using scheduledPair_mem_prefix b hn
  constructor
  · intro i
    let n := max (2*i) (2 * b (2*i)+1)+1
    exact ((compatible_of_branch hb n).1 (i,b (2*i)) (hpair i (by omega))
      (b (2 * b (2*i)+1),b (2*i)) (hipair (b (2*i)) (by omega))).mpr rfl |>.symm
  · intro i
    let n := max (2 * b (2*i+1)) (2*i+1)+1
    exact ((compatible_of_branch hb n).1 (b (2*i+1),b (2 * b (2*i+1)))
      (hpair (b (2*i+1)) (by omega)) (b (2*i+1),i) (hipair i (by omega))).mp rfl

/-- A branch gives a specific permutation, with explicitly measurable forward
and inverse coordinates. -/
def branchPermutation {L : CountableRelationalLanguage} {M N : Structures L}
    (b : ℕ → ℕ) (hb : ∀ n, attemptTree M N (initialSegment b n) = true) :
    PermutationGroup :=
  ⟨fun i => b (2*i),fun i => b (2*i+1),
    (inverse_coordinates b hb).1,(inverse_coordinates b hb).2⟩

theorem branchPermutation_preserves {L : CountableRelationalLanguage} {M N : Structures L}
    (b : ℕ → ℕ) (hb : ∀ n, attemptTree M N (initialSegment b n) = true) :
    ∀ s a, M ⟨s,a⟩ = N ⟨s,(branchPermutation b hb).toFun ∘ a⟩ := by
  intro s a
  let n : ℕ := (Finset.univ.sup (fun i : Fin (L.arity s) => 2*(a i)))+1
  exact (compatible_of_branch hb n).2 s (fun i => (a i,b (2*a i))) (fun i => by
    simpa only [scheduledPair_even] using scheduledPair_mem_prefix b
      (Nat.lt_succ_of_le (Finset.le_sup
        (f := fun i : Fin (L.arity s) => 2*(a i)) (Finset.mem_univ i))))

theorem measurable_permutation_of_coordinates {P : Type} [MeasurableSpace P]
    (f : P → PermutationGroup)
    (hf : ∀ n, Measurable (fun p => (f p).toFun n))
    (hg : ∀ n, Measurable (fun p => (f p).symm n)) : Measurable f := by
  have hemb : MeasurableEmbedding permutationCoordinates :=
    (show Topology.IsClosedEmbedding permutationCoordinates from
      ⟨permutationCoordinates_injective.isEmbedding_induced,
        range_permutationCoordinates ▸ isClosed_inversePairCondition⟩).measurableEmbedding
  apply hemb.measurable_comp_iff.mp
  exact (measurable_pi_lambda _ hf).prodMk (measurable_pi_lambda _ hg)

/-- The extra finite-map requirements of a construction can be retained in
the chosen tree: pruning is required of that actual tree, rather than inferred
from the mere existence of an isomorphism. -/
def prunedFamilyPermutation {P : Type} {L : CountableRelationalLanguage}
    (M N : P → Structures L) (T : P → RootedTrees.TreeSpace)
    (hroot : ∀ p, T p [] = true) (hpruned : ∀ p, RootedTrees.Pruned (T p))
    (hcompatible : ∀ p s, T p s = true →
      AtomicCompatible (M p) (N p) {q | q ∈ pairsFrom 0 s}) (p : P) :
    PermutationGroup :=
  branchPermutation (RootedTrees.branchChoice (T p)) (fun n => by
    apply decide_eq_true
    apply hcompatible p
    exact RootedTrees.branchChoice_spec (T p) (hroot p) (hpruned p) n)

theorem prunedFamilyPermutation_preserves {P : Type} {L : CountableRelationalLanguage}
    (M N : P → Structures L) (T : P → RootedTrees.TreeSpace)
    (hroot : ∀ p, T p [] = true) (hpruned : ∀ p, RootedTrees.Pruned (T p))
    (hcompatible : ∀ p s, T p s = true →
      AtomicCompatible (M p) (N p) {q | q ∈ pairsFrom 0 s}) (p : P) :
    ∀ s a, M p ⟨s,a⟩ = N p ⟨s,(prunedFamilyPermutation M N T hroot hpruned hcompatible p).toFun ∘ a⟩ :=
  branchPermutation_preserves _ _

theorem measurable_prunedFamilyPermutation {P : Type} [MeasurableSpace P]
    {L : CountableRelationalLanguage}
    (M N : P → Structures L) (T : P → RootedTrees.TreeSpace)
    (hroot : ∀ p, T p [] = true) (hpruned : ∀ p, RootedTrees.Pruned (T p))
    (hcompatible : ∀ p s, T p s = true →
      AtomicCompatible (M p) (N p) {q | q ∈ pairsFrom 0 s})
    (hT : Measurable T) :
    Measurable (prunedFamilyPermutation M N T hroot hpruned hcompatible) := by
  apply measurable_permutation_of_coordinates
  · intro n
    exact (measurable_pi_apply (2*n)).comp (RootedTrees.measurable_branchChoice.comp hT)
  · intro n
    exact (measurable_pi_apply (2*n+1)).comp (RootedTrees.measurable_branchChoice.comp hT)

end FSCofinality.PartialIso

end
end

-- Original module: FSCofinalityProof.AutomorphismGroups
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set TopologicalSpace

namespace FSCofinality

def Preserves {L : CountableRelationalLanguage} (M : Structures L)
    (p : PermutationGroup) : Prop :=
  ∀ s a, M ⟨s,a⟩ = M ⟨s,p.toFun ∘ a⟩

def automorphismGroup {L : CountableRelationalLanguage} (M : Structures L) :
    Subgroup PermutationGroup where
  carrier := {p | Preserves M p}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro p q hp hq s a
    exact (hq s a).trans (hp s (q.toFun ∘ a))
  inv_mem' := by
    intro p hp s a
    have h := hp s (p.symm.toFun ∘ a)
    have heq : p.toFun ∘ (p.symm.toFun ∘ a) = a :=
      funext (fun i => p.apply_symm_apply (a i))
    rw [heq] at h
    exact h.symm

theorem continuous_relabel_eval {L : CountableRelationalLanguage} (M : Structures L)
    (s : L.Symbol) (a : Fin (L.arity s) → ℕ) :
    Continuous (fun p : PermutationGroup => M ⟨s,p.toFun ∘ a⟩) := by
  have hc : Continuous (fun p : PermutationGroup => p.toFun ∘ a) :=
    continuous_pi (fun i => (continuous_apply (a i)).comp continuous_permutationCoordinates.fst)
  exact (continuous_of_discreteTopology : Continuous
    (fun b : Fin (L.arity s) → ℕ => M ⟨s,b⟩)).comp hc

theorem isClosed_automorphismGroup {L : CountableRelationalLanguage} (M : Structures L) :
    IsClosed (automorphismGroup M : Set PermutationGroup) := by
  change IsClosed {p : PermutationGroup | ∀ s a, M ⟨s,a⟩ = M ⟨s,p.toFun ∘ a⟩}
  simp only [setOf_forall]
  exact isClosed_iInter (fun s => isClosed_iInter (fun a =>
    isClosed_eq continuous_const (continuous_relabel_eval M s a)))

namespace DistinguishedRestriction

def restrictPerm (Q : Set ℕ) (e : ℕ ≃ Q) (p : PermutationGroup)
    (hp : ∀ n, n ∈ Q ↔ p.toFun n ∈ Q) : PermutationGroup :=
  (e.trans ((p : ℕ ≃ ℕ).subtypeEquiv hp)).trans e.symm

@[simp] theorem restrictPerm_apply_val (Q : Set ℕ) (e : ℕ ≃ Q) (p : PermutationGroup)
    (hp : ∀ n, n ∈ Q ↔ p.toFun n ∈ Q) (n : ℕ) :
    (e ((restrictPerm Q e p hp).toFun n)).val = p.toFun (e n).val := by
  simp [restrictPerm,Equiv.subtypeEquiv]

def hom {L : CountableRelationalLanguage} (M : Structures L) (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup M, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q) :
    automorphismGroup M →* PermutationGroup where
  toFun := fun p => restrictPerm Q e p.val (hQ p)
  map_one' := by
    apply Equiv.ext
    intro n
    apply e.injective
    apply Subtype.ext
    change (e ((restrictPerm Q e 1 _).toFun n)).val = (e n).val
    rw [restrictPerm_apply_val]
    rfl
  map_mul' := by
    intro p q
    apply Equiv.ext
    intro n
    apply e.injective
    apply Subtype.ext
    change (e ((restrictPerm Q e (p*q).val (hQ (p*q))).toFun n)).val =
      (e ((restrictPerm Q e p.val (hQ p)).toFun
        ((restrictPerm Q e q.val (hQ q)).toFun n))).val
    simp only [restrictPerm_apply_val]
    rfl

theorem continuous_hom {L : CountableRelationalLanguage} (M : Structures L)
    (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup M, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q) :
    Continuous (hom M Q e hQ) := by
  have hf (n : ℕ) : Continuous (fun p : automorphismGroup M =>
      (hom M Q e hQ p).toFun n) := by
    have hv : Continuous (fun p : automorphismGroup M => p.val.toFun (e n).val) :=
      ((continuous_apply (e n).val).comp continuous_permutationCoordinates.fst).comp
        continuous_subtype_val
    have hs : Continuous (fun p : automorphismGroup M =>
        (⟨p.val.toFun (e n).val,(hQ p (e n).val).mp (e n).property⟩ : Q)) :=
      hv.subtype_mk _
    exact (continuous_of_discreteTopology : Continuous e.symm).comp hs
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · exact continuous_pi hf
  · apply continuous_pi
    intro n
    have hi := (hf n).comp (continuous_inv : Continuous (fun p : automorphismGroup M => p⁻¹))
    convert hi using 1

theorem hom_injective {L : CountableRelationalLanguage} (M : Structures L)
    (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup M, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q)
    (hfaithful : ∀ p q : automorphismGroup M,
      (∀ n ∈ Q, p.val.toFun n = q.val.toFun n) → p = q) :
    Function.Injective (hom M Q e hQ) := by
  intro p q hpq
  apply hfaithful p q
  intro n hn
  obtain ⟨k,hk⟩ := e.surjective ⟨n,hn⟩
  have h := congrArg (fun g : PermutationGroup => (e (g.toFun k)).val) hpq
  simpa only [hom,MonoidHom.coe_mk,OneHom.coe_mk,restrictPerm_apply_val,hk] using h

end DistinguishedRestriction
end FSCofinality

end
end

-- Original module: FSCofinalityProof.IsomorphismCosets
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality

def Carries {L : CountableRelationalLanguage} (M N : Structures L)
    (p : PermutationGroup) : Prop :=
  ∀ s a, M ⟨s,a⟩ = N ⟨s,p.toFun ∘ a⟩

theorem Carries.mul {L : CountableRelationalLanguage} {M N O : Structures L}
    {p q : PermutationGroup} (hp : Carries N O p) (hq : Carries M N q) :
    Carries M O (p*q) := fun s a => (hq s a).trans (hp s (q.toFun ∘ a))

theorem Carries.inv {L : CountableRelationalLanguage} {M N : Structures L}
    {p : PermutationGroup} (hp : Carries M N p) : Carries N M p⁻¹ := by
  intro s a
  have h := hp s (p.symm.toFun ∘ a)
  have heq : p.toFun ∘ (p.symm.toFun ∘ a) = a := funext (fun i => p.apply_symm_apply _)
  rw [heq] at h
  exact h.symm

def QFixedIsomorphic {L : CountableRelationalLanguage} (Q : Set ℕ) (M N : Structures L) :
    Prop := ∃ p : PermutationGroup, Carries M N p ∧ ∀ n ∈ Q, p.toFun n = n

namespace DistinguishedRestriction

theorem restrictPerm_eq_iff (Q : Set ℕ) (e : ℕ ≃ Q) (p q : PermutationGroup)
    (hp : ∀ n, n ∈ Q ↔ p.toFun n ∈ Q) (hq : ∀ n, n ∈ Q ↔ q.toFun n ∈ Q) :
    restrictPerm Q e p hp = restrictPerm Q e q hq ↔
      ∀ n ∈ Q, p.toFun n = q.toFun n := by
  constructor
  · intro h n hn
    obtain ⟨k,hk⟩ := e.surjective ⟨n,hn⟩
    have h' := congrArg (fun g : PermutationGroup => (e (g.toFun k)).val) h
    simpa only [restrictPerm_apply_val,hk] using h'
  · intro h
    apply Equiv.ext
    intro k
    apply e.injective
    apply Subtype.ext
    change (e ((restrictPerm Q e p hp).toFun k)).val =
      (e ((restrictPerm Q e q hq).toFun k)).val
    simpa only [restrictPerm_apply_val] using h (e k).val (e k).property

theorem measurable_restrictPerm {P : Type} [MeasurableSpace P]
    (Q : Set ℕ) (e : ℕ ≃ Q) (u : P → PermutationGroup)
    (huQ : ∀ p n, n ∈ Q ↔ (u p).toFun n ∈ Q) (hu : Measurable u) :
    Measurable (fun p => restrictPerm Q e (u p) (huQ p)) := by
  apply PartialIso.measurable_permutation_of_coordinates
  · intro n
    have hv : Measurable (fun p => (u p).toFun (e n).val) :=
      ((continuous_apply (e n).val).comp continuous_permutationCoordinates.fst).measurable.comp hu
    have hs : Measurable (fun p =>
        (⟨(u p).toFun (e n).val,(huQ p _).mp (e n).property⟩ : Q)) := hv.subtype_mk
    exact (measurable_of_countable e.symm).comp hs
  · intro n
    have hv : Measurable (fun p => (u p).symm.toFun (e n).val) :=
      ((continuous_apply (e n).val).comp continuous_permutationCoordinates.snd).measurable.comp hu
    have hm (p : P) : (u p).symm.toFun (e n).val ∈ Q := by
      apply (huQ p _).mpr
      have hi : (u p).toFun ((u p).symm.toFun (e n).val) = (e n).val :=
        (u p).right_inv _
      rw [hi]
      exact (e n).property
    have hs : Measurable (fun p =>
        (⟨(u p).symm.toFun (e n).val,hm p⟩ : Q)) := hv.subtype_mk
    exact (measurable_of_countable e.symm).comp hs

/-- Chosen isomorphisms into one base structure identify fixed-point
isomorphism with cosets of the base automorphism group's restriction image.
The inverse in the output is forced by the left-coset convention. -/
theorem qFixed_iff_coset {P : Type} {L : CountableRelationalLanguage}
    (M : P → Structures L) (B : Structures L) (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup B, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q)
    (u : P → PermutationGroup) (hu : ∀ x, Carries (M x) B (u x))
    (huQ : ∀ x n, n ∈ Q ↔ (u x).toFun n ∈ Q) (x y : P) :
    QFixedIsomorphic Q (M x) (M y) ↔
      (imageCosetRelation (hom B Q e hQ)).rel
        (show PermutationGroup from (restrictPerm Q e (u x) (huQ x))⁻¹)
        (show PermutationGroup from (restrictPerm Q e (u y) (huQ y))⁻¹) := by
  let alpha (z : P) := restrictPerm Q e (u z) (huQ z)
  have hcoord (g : automorphismGroup B) :
      hom B Q e hQ g = alpha y * (alpha x)⁻¹ ↔
        ∀ n ∈ Q, g.val.toFun ((u x).toFun n) = (u y).toFun n := by
    rw [eq_mul_inv_iff_mul_eq]
    constructor
    · intro h n hn
      obtain ⟨k,hk⟩ := e.surjective ⟨n,hn⟩
      have ht := congrArg (fun p : PermutationGroup => (e (p.toFun k)).val) h
      change (e ((restrictPerm Q e g.val (hQ g)).toFun ((alpha x).toFun k))).val =
        (e ((alpha y).toFun k)).val at ht
      simpa only [alpha,restrictPerm_apply_val,hk] using ht
    · intro h
      apply Equiv.ext
      intro k
      apply e.injective
      apply Subtype.ext
      change (e ((restrictPerm Q e g.val (hQ g)).toFun ((alpha x).toFun k))).val =
        (e ((alpha y).toFun k)).val
      simpa only [alpha,restrictPerm_apply_val] using h (e k).val (e k).property
  change QFixedIsomorphic Q (M x) (M y) ↔
    (alpha y)⁻¹⁻¹ * (alpha x)⁻¹ ∈ (hom B Q e hQ).range
  rw [inv_inv]
  constructor
  · rintro ⟨t,ht,hfix⟩
    let g : automorphismGroup B :=
      ⟨u y * t * (u x)⁻¹,(hu y).mul (ht.mul (hu x).inv)⟩
    refine ⟨g,?_⟩
    apply (hcoord g).mpr
    intro n hn
    change (u y).toFun (t.toFun ((u x).symm.toFun ((u x).toFun n))) = (u y).toFun n
    have hinv : (u x).symm.toFun ((u x).toFun n) = n := (u x).left_inv n
    rw [hinv,hfix n hn]
  · rintro ⟨g,hg⟩
    have hc := (hcoord g).mp hg
    refine ⟨(u y)⁻¹ * g.val * u x,((hu y).inv.mul g.property).mul (hu x),?_⟩
    intro n hn
    change (u y).symm.toFun (g.val.toFun ((u x).toFun n)) = n
    rw [hc n hn]
    exact (u y).symm_apply_apply n

theorem qFixed_reduces_coset {P : Type} [MeasurableSpace P]
    {L : CountableRelationalLanguage}
    (M : P → Structures L) (B : Structures L) (Q : Set ℕ) (e : ℕ ≃ Q)
    (hQ : ∀ p : automorphismGroup B, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q)
    (u : P → PermutationGroup) (hu : ∀ x, Carries (M x) B (u x))
    (huQ : ∀ x n, n ∈ Q ↔ (u x).toFun n ∈ Q) (hmeas : Measurable u) :
    BorelReducible (fun x y => QFixedIsomorphic Q (M x) (M y))
      (CosetRelation (hom B Q e hQ).range) := by
  refine ⟨fun x => (restrictPerm Q e (u x) (huQ x))⁻¹,?_,?_⟩
  · exact continuous_permutation_inv.measurable.comp (measurable_restrictPerm Q e u huQ hmeas)
  · exact qFixed_iff_coset M B Q e hQ u hu huQ

end DistinguishedRestriction
end FSCofinality

end
end

-- Original module: FSCofinalityProof.CosetConstructionNativeCoordinates
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def coordinateCode (n : ℕ) : ℕ := (templateEnumeration eta heta).symm (.inl n)

theorem coordinateCode_injective : Function.Injective (coordinateCode eta heta) :=
  (templateEnumeration eta heta).symm.injective.comp Sum.inl_injective

def nativeQ : Set ℕ := range (coordinateCode eta heta)

def coordinateEquiv : ℕ ≃ nativeQ eta heta :=
  Equiv.ofInjective (coordinateCode eta heta) (coordinateCode_injective eta heta)

theorem nativeEnumeration_coordinateCode (x : (fsTower eta).Carrier) (n : ℕ) :
    nativeEnumeration eta heta x (coordinateCode eta heta n) = .inl n := by
  rw [show coordinateCode eta heta n = (nativeEnumeration eta heta x).symm (.inl n) from
    (nativeEnumeration_coordinate_preimage eta heta x n).symm]
  exact (nativeEnumeration eta heta x).apply_symm_apply _

theorem nativeQ_iff (x : (fsTower eta).Carrier) (k : ℕ) :
    k ∈ nativeQ eta heta ↔ sortOf eta heta (nativeEnumeration eta heta x k) = none := by
  constructor
  · rintro ⟨n,rfl⟩
    rw [nativeEnumeration_coordinateCode]
    rfl
  · intro hk
    cases hv : nativeEnumeration eta heta x k with
    | inl n =>
      refine ⟨n,?_⟩
      apply (nativeEnumeration eta heta x).injective
      rw [nativeEnumeration_coordinateCode,hv]
    | inr v => simp only [hv,sortOf] at hk; contradiction

def fromNative (x y : (fsTower eta).Carrier) (p : PermutationGroup) :
    Vertex eta heta x ≃ Vertex eta heta y :=
  (((nativeEnumeration eta heta x).symm).trans (p : ℕ ≃ ℕ)).trans (nativeEnumeration eta heta y)

theorem fromNative_preserves (x y : (fsTower eta).Carrier) (p : PermutationGroup)
    (hp : Carries (nativeModel eta heta x) (nativeModel eta heta y) p) :
    PreservesDiagram eta heta (fromNative eta heta x y p) := by
  intro s a
  have h := hp s ((nativeEnumeration eta heta x).symm ∘ a)
  simpa only [nativeModel,modelWithEnumeration,fromNative,Equiv.trans_apply,Function.comp_def,
    Equiv.apply_symm_apply] using h

def toNative (x y : (fsTower eta).Carrier) (e : Vertex eta heta x ≃ Vertex eta heta y) :
    PermutationGroup :=
  (((nativeEnumeration eta heta x).trans e).trans (nativeEnumeration eta heta y).symm)

theorem toNative_carries (x y : (fsTower eta).Carrier) (e : Vertex eta heta x ≃ Vertex eta heta y)
    (he : PreservesDiagram eta heta e) :
    Carries (nativeModel eta heta x) (nativeModel eta heta y) (toNative eta heta x y e) := by
  intro s a
  have h := he s (nativeEnumeration eta heta x ∘ a)
  change diagram eta heta (bottom eta heta) x s (fun i => nativeEnumeration eta heta x (a i)) =
    diagram eta heta (bottom eta heta) y s (fun i => nativeEnumeration eta heta y
      ((nativeEnumeration eta heta y).symm (e (nativeEnumeration eta heta x (a i)))))
  simpa only [Function.comp_def,Equiv.apply_symm_apply] using h

theorem fromNative_fixes_coordinate (x y : (fsTower eta).Carrier) (p : PermutationGroup)
    (hQ : ∀ k ∈ nativeQ eta heta, p.toFun k = k) (n : ℕ) :
    fromNative eta heta x y p (.inl n) = .inl n := by
  change nativeEnumeration eta heta y (p.toFun ((nativeEnumeration eta heta x).symm (.inl n))) = _
  rw [nativeEnumeration_coordinate_preimage]
  change nativeEnumeration eta heta y (p.toFun (coordinateCode eta heta n)) = _
  rw [hQ _ (mem_range_self n),nativeEnumeration_coordinateCode]

theorem toNative_fixesQ (x y : (fsTower eta).Carrier) (e : Vertex eta heta x ≃ Vertex eta heta y)
    (hQ : ∀ n, e (.inl n) = .inl n) :
    ∀ k ∈ nativeQ eta heta, (toNative eta heta x y e).toFun k = k := by
  rintro k ⟨n,rfl⟩
  change (nativeEnumeration eta heta y).symm (e (nativeEnumeration eta heta x (coordinateCode eta heta n))) = _
  rw [nativeEnumeration_coordinateCode,hQ,nativeEnumeration_coordinate_preimage]
  rfl

theorem nativeCarries_preservesQ (x y : (fsTower eta).Carrier) (p : PermutationGroup)
    (hp : Carries (nativeModel eta heta x) (nativeModel eta heta y) p) (n : ℕ) :
    n ∈ nativeQ eta heta ↔ p.toFun n ∈ nativeQ eta heta := by
  rw [nativeQ_iff eta heta x n,nativeQ_iff eta heta y (p.toFun n)]
  have h := hp (.inl none) (fun _ => n)
  change decide (sortOf eta heta (nativeEnumeration eta heta x n) = none) =
    decide (sortOf eta heta (nativeEnumeration eta heta y (p.toFun n)) = none) at h
  exact decide_eq_decide.mp h

theorem native_qFixed_iff (x y : (fsTower eta).Carrier) :
    (fsTower eta).rel x y ↔
      QFixedIsomorphic (nativeQ eta heta) (nativeModel eta heta x) (nativeModel eta heta y) := by
  constructor
  · intro hxy
    obtain ⟨e,he,hQ⟩ := source_equivalent_qFixed eta heta hxy
    exact ⟨toNative eta heta x y e,toNative_carries eta heta x y e he,toNative_fixesQ eta heta x y e hQ⟩
  · rintro ⟨p,hp,hQ⟩
    exact qFixed_reflects eta heta (fromNative eta heta x y p) (fromNative_preserves eta heta x y p hp)
      (fromNative_fixes_coordinate eta heta x y p hQ)

theorem native_qFixed_rigid (x : (fsTower eta).Carrier) (p : PermutationGroup)
    (hp : Carries (nativeModel eta heta x) (nativeModel eta heta x) p)
    (hQ : ∀ k ∈ nativeQ eta heta, p.toFun k = k) : p = 1 := by
  have he := qFixed_rigid eta heta (fromNative eta heta x x p) (fromNative_preserves eta heta x x p hp)
    (fromNative_fixes_coordinate eta heta x x p hQ)
  apply Equiv.ext
  intro n
  apply (nativeEnumeration eta heta x).injective
  have h := congrArg (fun e : Vertex eta heta x ≃ Vertex eta heta x => e (nativeEnumeration eta heta x n)) he
  simpa only [fromNative,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.refl_apply] using h

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.TokenAtomicExtensions
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

def twoTuple {α : Type*} {n : ℕ} (x y : α) : Fin n → α :=
  fun i => if i.val = 0 then x else y

/-- In a unary/binary relational language, all complete atomic requirements
for one new point reduce to its unary type, its diagonal binary type, and
the two directed incidences with old points. -/
theorem AtomicCompatible.insert_of_unary_binary {L : CountableRelationalLanguage}
    {M N : Structures L} {R : Set (ℕ × ℕ)} (hR : AtomicCompatible M N R)
    (hArity : ∀ s, L.arity s ≤ 2) (x y : ℕ)
    (hEq : ∀ p ∈ R, x = p.1 ↔ y = p.2)
    (hUnary : ∀ s, L.arity s = 1 → M ⟨s,fun _ => x⟩ = N ⟨s,fun _ => y⟩)
    (hDiagonal : ∀ s, L.arity s = 2 → M ⟨s,fun _ => x⟩ = N ⟨s,fun _ => y⟩)
    (hForward : ∀ s, L.arity s = 2 → ∀ p ∈ R,
      M ⟨s,twoTuple x p.1⟩ = N ⟨s,twoTuple y p.2⟩)
    (hBackward : ∀ s, L.arity s = 2 → ∀ p ∈ R,
      M ⟨s,twoTuple p.1 x⟩ = N ⟨s,twoTuple p.2 y⟩) :
    AtomicCompatible M N (insert (x,y) R) := by
  constructor
  · intro p hp q hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · simp
    · exact hEq q hq
    · simpa only [eq_comm] using hEq p hp
    · exact hR.1 p hp q hq
  · intro s a ha
    have hcases : L.arity s = 0 ∨ L.arity s = 1 ∨ L.arity s = 2 := by
      have := hArity s
      omega
    rcases hcases with hzero | hone | htwo
    · apply hR.2 s a
      intro i
      exact False.elim (by have := i.isLt; omega)
    · let i₀ : Fin (L.arity s) := ⟨0,by omega⟩
      have hall (i : Fin (L.arity s)) : i = i₀ := by apply Fin.ext; have := i.isLt; omega
      rcases ha i₀ with hn | ho
      · have heq : ∀ i, a i = (x,y) := fun i => (congrArg a (hall i)).trans hn
        simpa only [heq] using hUnary s hone
      · apply hR.2 s a
        intro i
        simpa only [hall i] using ho
    · let i₀ : Fin (L.arity s) := ⟨0,by omega⟩
      let i₁ : Fin (L.arity s) := ⟨1,by omega⟩
      have hcoordinates (i : Fin (L.arity s)) :
          a i = if i.val = 0 then a i₀ else a i₁ := by
        split_ifs with hi
        · exact congrArg a (Fin.ext hi)
        · apply congrArg a
          apply Fin.ext
          change i.val = 1
          have := i.isLt
          omega
      rcases ha i₀ with h₀ | h₀ <;> rcases ha i₁ with h₁ | h₁
      · have heq : ∀ i, a i = (x,y) := by
          intro i
          rw [hcoordinates,h₀,h₁]
          split_ifs <;> rfl
        simpa only [heq] using hDiagonal s htwo
      · have hf : (fun i => (a i).1) = twoTuple x (a i₁).1 := by
          funext i
          rw [hcoordinates,h₀]
          unfold twoTuple
          split_ifs <;> rfl
        have hg : (fun i => (a i).2) = twoTuple y (a i₁).2 := by
          funext i
          rw [hcoordinates,h₀]
          unfold twoTuple
          split_ifs <;> rfl
        rw [hf,hg]
        exact hForward s htwo (a i₁) h₁
      · have hf : (fun i => (a i).1) = twoTuple (a i₀).1 x := by
          funext i
          rw [hcoordinates,h₁]
          unfold twoTuple
          split_ifs <;> rfl
        have hg : (fun i => (a i).2) = twoTuple (a i₀).2 y := by
          funext i
          rw [hcoordinates,h₁]
          unfold twoTuple
          split_ifs <;> rfl
        rw [hf,hg]
        exact hBackward s htwo (a i₀) h₀
      · apply hR.2 s a
        intro i
        rw [hcoordinates]
        split_ifs
        · exact h₀
        · exact h₁

theorem AtomicCompatible.empty_of_positive_arity {L : CountableRelationalLanguage}
    (M N : Structures L) (hArity : ∀ s, 0 < L.arity s) :
    AtomicCompatible M N ∅ := by
  constructor
  · simp
  · intro s a ha
    exact False.elim (ha ⟨0,hArity s⟩)

theorem AtomicCompatible.swap {L : CountableRelationalLanguage} {M N : Structures L}
    {R : Set (ℕ × ℕ)} (hR : AtomicCompatible M N R) :
    AtomicCompatible N M (Prod.swap ⁻¹' R) := by
  constructor
  · intro p hp q hq
    exact (hR.1 p.swap hp q.swap hq).symm
  · intro s a ha
    exact (hR.2 s (fun i => (a i).swap) ha).symm

theorem AtomicCompatible.swap_list {L : CountableRelationalLanguage} {M N : Structures L}
    {R : List (ℕ × ℕ)} (hR : AtomicCompatible M N {p | p ∈ R}) :
    AtomicCompatible N M {p | p ∈ R.map Prod.swap} := by
  apply hR.swap.mono
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact hq

end FSCofinality.PartialIso

end
end

-- Original module: FSCofinalityProof.ParameterClassOrbits
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology TopologicalSpace

namespace FSCofinality.OrbitCoding

def perm (g : PermutationGroup) : ℕ ≃ ℕ := g

/-- Every nonempty finite tuple names one relation, whose interpretation
is its orbit under the parameter group. -/
def language : CountableRelationalLanguage where
  Symbol := Σ n : ℕ, Fin (n+1) → ℕ
  arity := fun s => s.1+1
  countable := inferInstance

def canonicalStructure (H : Subgroup PermutationGroup) : Structures language :=
  fun ⟨s,a⟩ => decide (∃ g : H, ∀ i, (perm g.val) (s.2 i) = a i)

def sequenceStructure (d : ℕ → PermutationGroup) : Structures language :=
  fun ⟨s,a⟩ => decide (∃ j : ℕ, ∀ i, (perm (d j)) (s.2 i) = a i)

theorem continuous_apply (n : ℕ) :
    Continuous (fun g : PermutationGroup => (perm g) n) :=
  (_root_.continuous_apply n).comp continuous_permutationCoordinates.fst

/-- Closedness turns agreement on every finite initial segment into
actual membership in the permutation subgroup. -/
theorem mem_of_finite_agreement (H : Subgroup PermutationGroup)
    (hH : IsClosed (H : Set PermutationGroup)) (p : PermutationGroup)
    (hag : ∀ n : ℕ, ∃ g : H, ∀ i < n, (perm g.val) i = (perm p) i) :
    p ∈ H := by
  choose g hg using hag
  have hf : Tendsto (fun n => (permutationCoordinates (g n).val).1) atTop
      (𝓝 (permutationCoordinates p).1) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (i+1)] with n hn
    exact (hg n i (by omega)).symm
  have hi : Tendsto (fun n => (permutationCoordinates (g n).val).2) atTop
      (𝓝 (permutationCoordinates p).2) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ((perm p).symm i+1)] with n hn
    have he := hg n ((perm p).symm i) (by omega)
    have he' : perm (g n).val ((perm p).symm i) = i := by
      simpa only [Equiv.apply_symm_apply] using he
    exact ((perm (g n).val).symm_apply_eq.mpr he'.symm).symm
  have ht : Tendsto (fun n => (g n).val) atTop (𝓝 p) := by
    rw [nhds_induced]
    exact tendsto_comap_iff.mpr (hf.prodMk_nhds hi)
  exact hH.mem_of_tendsto ht (Eventually.of_forall (fun n => (g n).property))

/-- Every automorphism of the orbit-naming structure belongs to the
original closed subgroup; every subgroup element preserves its named
orbits. -/
theorem preserves_canonicalStructure_iff (H : Subgroup PermutationGroup)
    (hH : IsClosed (H : Set PermutationGroup)) (p : PermutationGroup) :
    (∀ (s : language.Symbol) (a : Fin (language.arity s) → ℕ),
      canonicalStructure H ⟨s,a⟩ =
        canonicalStructure H ⟨s,(perm p) ∘ a⟩) ↔ p ∈ H := by
  constructor
  · intro hpres
    apply mem_of_finite_agreement H hH p
    intro n
    let t : Fin (n+1) → ℕ := fun i => i.val
    have hself : canonicalStructure H ⟨⟨n,t⟩,t⟩ = true := by
      simp only [canonicalStructure,decide_eq_true_eq]
      exact ⟨1,fun _ => rfl⟩
    have hp := (hpres ⟨n,t⟩ t).symm.trans hself
    obtain ⟨g,hg⟩ : ∃ g : H, ∀ i : Fin (n+1),
        (perm g.val) i.val = (perm p) i.val := by
      simpa only [canonicalStructure,decide_eq_true_eq,Function.comp_def,t] using hp
    exact ⟨g,fun i hi => hg ⟨i,by omega⟩⟩
  · intro hp s a
    simp only [canonicalStructure,decide_eq_decide]
    constructor
    · rintro ⟨g,hg⟩
      refine ⟨⟨p*g.val,H.mul_mem hp g.property⟩,fun i => ?_⟩
      exact congrArg (perm p) (hg i)
    · rintro ⟨g,hg⟩
      refine ⟨⟨p⁻¹*g.val,H.mul_mem (H.inv_mem hp) g.property⟩,fun i => ?_⟩
      apply (perm p).injective
      change (perm p) ((perm p).symm ((perm g.val) (s.2 i))) = (perm p) (a i)
      simpa only [Equiv.apply_symm_apply,Function.comp_apply] using hg i

/-- Countable dense sequences are sufficient to recover every orbit
relation; no selection theorem is used by this statement. -/
theorem sequenceStructure_eq_canonicalStructure (H : Subgroup PermutationGroup)
    (d : ℕ → H) (hd : DenseRange d) :
    sequenceStructure (fun j => (d j).val) = canonicalStructure H := by
  funext ⟨s,a⟩
  change decide (∃ j, ∀ i, (perm (d j).val) (s.2 i) = a i) =
    decide (∃ g : H, ∀ i, (perm g.val) (s.2 i) = a i)
  simp only [decide_eq_decide]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨d j,hj⟩
  · rintro ⟨g,hg⟩
    have ho : IsOpen {q : H | ∀ i : Fin (s.1+1), (perm q.val) (s.2 i) = a i} := by
      simp only [setOf_forall]
      apply isOpen_iInter_of_finite
      intro i
      exact (isOpen_discrete {a i}).preimage
        ((continuous_apply (s.2 i)).comp continuous_subtype_val)
    exact hd.exists_mem_open ho ⟨g,hg⟩

/-- The canonical structure produced from a sequence of permutations is
a Borel function of that sequence. -/
theorem measurable_sequenceStructure : Measurable sequenceStructure := by
  change @Measurable (ℕ → PermutationGroup) (Coordinate language → Bool) _
    (borel (Coordinate language → Bool)) sequenceStructure
  rw [← BorelSpace.measurable_eq (α := Coordinate language → Bool)]
  apply measurable_pi_iff.mpr
  rintro ⟨s,a⟩
  have htest : MeasurableSet {d : ℕ → PermutationGroup |
      ∃ j : ℕ, ∀ i : Fin (s.1+1), (perm (d j)) (s.2 i) = a i} := by
    simp only [setOf_exists,setOf_forall]
    apply MeasurableSet.iUnion
    intro j
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_eq_fun
      (((continuous_apply (s.2 i)).measurable).comp (measurable_pi_apply j)) measurable_const
  convert Measurable.ite htest (measurable_const (a := true))
    (measurable_const (a := false)) using 1

end FSCofinality.OrbitCoding


end
end

-- Original module: FSCofinalityProof.ParameterClassCopies
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CopyCoding
open PartialIso

/-- Every compatible finite correspondence into the structure extends to
an isomorphism. This formulation also includes copies on the fixed domain. -/
def FiniteMapExtension {L : CountableRelationalLanguage} (M : Structures L) : Prop :=
  ∀ N : Structures L, Isomorphic N M → ∀ R : List (ℕ × ℕ),
    AtomicCompatible N M {p | p ∈ R} →
    ∃ e : ℕ ≃ ℕ, (∀ s a, N ⟨s,a⟩ = M ⟨s,e ∘ a⟩) ∧
      ∀ p ∈ R, e p.1 = p.2

/-- A countable Borel test for being a copy of an ultrahomogeneous structure.
Both extension directions are stated explicitly. -/
def CopyTest {L : CountableRelationalLanguage} (N M : Structures L) : Prop :=
  AtomicCompatible N M ∅ ∧
  ∀ R : List (ℕ × ℕ), AtomicCompatible N M {p | p ∈ R} →
    (∀ x : ℕ, ∃ y : ℕ, AtomicCompatible N M {p | p ∈ R ++ [(x,y)]}) ∧
    (∀ y : ℕ, ∃ x : ℕ, AtomicCompatible N M {p | p ∈ R ++ [(x,y)]})

theorem canonical_finiteMapExtension (H : Subgroup PermutationGroup) :
    FiniteMapExtension (OrbitCoding.canonicalStructure H) := by
  intro N hNM R hR
  obtain ⟨e,he⟩ := hNM
  cases R with
  | nil => exact ⟨e,he,by simp⟩
  | cons p R =>
    let a : Fin (R.length+1) → ℕ := fun i => ((p::R).get i).1
    let b : Fin (R.length+1) → ℕ := fun i => ((p::R).get i).2
    let t : Fin (R.length+1) → ℕ := e ∘ a
    let s : OrbitCoding.language.Symbol := ⟨R.length,t⟩
    have ht : OrbitCoding.canonicalStructure H ⟨s,t⟩ = true := by
      simp only [OrbitCoding.canonicalStructure, decide_eq_true_eq]
      exact ⟨1,fun _ => rfl⟩
    have hNa : N ⟨s,a⟩ = true := (he s a).trans ht
    have hNb : OrbitCoding.canonicalStructure H ⟨s,b⟩ = true := by
      have hh := hR.2 s (fun i => (p::R).get i) (fun i => by
        change Fin (R.length+1) at i
        exact List.get_mem (p::R) i)
      exact hh.symm.trans hNa
    obtain ⟨g,hg⟩ : ∃ g : H, ∀ i, (OrbitCoding.perm g.val) (t i) = b i :=
      of_decide_eq_true hNb
    refine ⟨e.trans (OrbitCoding.perm g.val),?_,?_⟩
    · intro q c
      refine (he q c).trans ?_
      change OrbitCoding.canonicalStructure H ⟨q,e ∘ c⟩ =
        OrbitCoding.canonicalStructure H ⟨q,OrbitCoding.perm g.val ∘ (e ∘ c)⟩
      simp only [OrbitCoding.canonicalStructure, decide_eq_decide]
      constructor
      · rintro ⟨k,hk⟩
        exact ⟨g*k,fun i => congrArg (OrbitCoding.perm g.val) (hk i)⟩
      · rintro ⟨k,hk⟩
        refine ⟨g⁻¹*k,fun i => ?_⟩
        apply (OrbitCoding.perm g.val).injective
        change (OrbitCoding.perm g.val) ((OrbitCoding.perm g.val).symm
          ((OrbitCoding.perm k.val) (q.2 i))) = (OrbitCoding.perm g.val) (e (c i))
        simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hk i
    · intro q hq
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hq
      simpa only [Equiv.trans_apply,a,b,t,Function.comp_apply,hi] using hg i

theorem copyTest_of_isomorphic {L : CountableRelationalLanguage} {M N : Structures L}
    (hM : FiniteMapExtension M) (hNM : Isomorphic N M) : CopyTest N M := by
  constructor
  · obtain ⟨e,he⟩ := hNM
    exact compatible_graph e he (by simp)
  · intro R hR
    obtain ⟨e,he,hagree⟩ := hM N hNM R hR
    constructor
    · intro x
      refine ⟨e x,compatible_graph e he ?_⟩
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hagree p hp
      · rcases List.mem_singleton.mp hp with rfl
        rfl
    · intro y
      refine ⟨e.symm y,compatible_graph e he ?_⟩
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hagree p hp
      · rcases List.mem_singleton.mp hp with rfl
        exact e.apply_symm_apply y

theorem CopyTest.pruned {L : CountableRelationalLanguage} {N M : Structures L}
    (h : CopyTest N M) : RootedTrees.Pruned (attemptTree N M) := by
  intro s hs
  have hc : AtomicCompatible N M {p | p ∈ pairsFrom 0 s} := of_decide_eq_true hs
  have hh := h.2 (pairsFrom 0 s) hc
  by_cases heven : s.length % 2 = 0
  · obtain ⟨y,hy⟩ := hh.1 (s.length/2)
    refine ⟨y,decide_eq_true ?_⟩
    simpa only [pairsFrom_append,pairsFrom,List.length_nil,Nat.add_zero,Nat.zero_add,
      scheduledPair,heven,if_true] using hy
  · obtain ⟨x,hx⟩ := hh.2 (s.length/2)
    refine ⟨x,decide_eq_true ?_⟩
    simpa only [pairsFrom_append,pairsFrom,List.length_nil,Nat.add_zero,Nat.zero_add,
      scheduledPair,heven,if_false] using hx

theorem CopyTest.root {L : CountableRelationalLanguage} {N M : Structures L}
    (h : CopyTest N M) : attemptTree N M [] = true := by
  apply decide_eq_true
  simpa only [pairsFrom,List.not_mem_nil,setOf_false] using h.1

theorem CopyTest.isomorphic {L : CountableRelationalLanguage} {N M : Structures L}
    (h : CopyTest N M) : Isomorphic N M := by
  exact isomorphic_of_branch (RootedTrees.branchChoice (attemptTree N M))
    (RootedTrees.branchChoice_spec _ h.root h.pruned)

theorem copyTest_iff_isomorphic {L : CountableRelationalLanguage} {M N : Structures L}
    (hM : FiniteMapExtension M) : CopyTest N M ↔ Isomorphic N M :=
  ⟨CopyTest.isomorphic,copyTest_of_isomorphic hM⟩

theorem measurableSet_copyTest {L : CountableRelationalLanguage} :
    MeasurableSet {p : Structures L × Structures L | CopyTest p.1 p.2} := by
  unfold CopyTest
  rw [setOf_and]
  apply (measurableSet_atomicCompatible ∅).inter
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro R
  apply (measurableSet_atomicCompatible {p | p ∈ R}).imp
  rw [setOf_and]
  apply MeasurableSet.inter <;> simp only [setOf_forall,setOf_exists] <;>
    apply MeasurableSet.iInter <;> intro n <;>
    apply MeasurableSet.iUnion <;> intro m <;>
    exact measurableSet_atomicCompatible _

def chosenIsomorphism {P : Type} {L : CountableRelationalLanguage}
    (N M : P → Structures L) (h : ∀ p, CopyTest (N p) (M p)) :
    P → PermutationGroup :=
  prunedFamilyPermutation N M (fun p => attemptTree (N p) (M p))
    (fun p => (h p).root) (fun p => (h p).pruned)
    (fun _ _ hs => of_decide_eq_true hs)

theorem chosenIsomorphism_preserves {P : Type} {L : CountableRelationalLanguage}
    (N M : P → Structures L) (h : ∀ p, CopyTest (N p) (M p)) (p : P) :
    ∀ s a, N p ⟨s,a⟩ = M p ⟨s,(chosenIsomorphism N M h p).toFun ∘ a⟩ :=
  prunedFamilyPermutation_preserves N M _ _ _ _ p

theorem measurable_chosenIsomorphism {P : Type} [MeasurableSpace P]
    {L : CountableRelationalLanguage} (N M : P → Structures L)
    (h : ∀ p, CopyTest (N p) (M p)) (hN : Measurable N) (hM : Measurable M) :
    Measurable (chosenIsomorphism N M h) := by
  apply measurable_prunedFamilyPermutation
  exact measurable_attemptTree.comp (hN.prodMk hM)

end FSCofinality.CopyCoding

end
end

-- Original module: FSCofinalityProof.TokenCommonIsotype
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

def ForthExtension {L : CountableRelationalLanguage} (M N : Structures L) : Prop :=
  ∀ R : List (ℕ × ℕ), AtomicCompatible M N {p | p ∈ R} →
    ∀ x : ℕ, ∃ y : ℕ, AtomicCompatible M N {p | p ∈ R ++ [(x,y)]}

/-- Old domain points can be handled without invoking a realization lemma;
only genuinely new points require the construction's extension property. -/
theorem forthExtension_of_fresh {L : CountableRelationalLanguage} {M N : Structures L}
    (h : ∀ R : List (ℕ × ℕ), AtomicCompatible M N {p | p ∈ R} →
      ∀ x : ℕ, (∀ p ∈ R, x ≠ p.1) →
        ∃ y : ℕ, AtomicCompatible M N {p | p ∈ R ++ [(x,y)]}) : ForthExtension M N := by
  intro R hR x
  by_cases hfresh : ∀ p ∈ R, x ≠ p.1
  · exact h R hR x hfresh
  · push_neg at hfresh
    obtain ⟨p,hp,hpx⟩ := hfresh
    refine ⟨p.2,hR.mono ?_⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hq
    · have heq : q = (x,p.2) := List.mem_singleton.mp hq
      have hpair : (x,p.2) = p := Prod.ext hpx rfl
      exact heq.symm ▸ hpair.symm ▸ hp

theorem copyTest_of_extensions {L : CountableRelationalLanguage} {M N : Structures L}
    (hempty : AtomicCompatible M N ∅) (hMN : ForthExtension M N)
    (hNM : ForthExtension N M) : CopyCoding.CopyTest M N := by
  refine ⟨hempty,fun R hR => ⟨hMN R hR,?_⟩⟩
  intro y
  obtain ⟨x,hx⟩ := hNM (R.map Prod.swap) hR.swap_list y
  refine ⟨x,?_⟩
  have hh := hx.swap_list
  simpa [List.map_map,Function.comp_def] using hh

theorem isomorphic_of_extensions {L : CountableRelationalLanguage} {M N : Structures L}
    (hempty : AtomicCompatible M N ∅) (hMN : ForthExtension M N)
    (hNM : ForthExtension N M) : Isomorphic M N :=
  (copyTest_of_extensions hempty hMN hNM).isomorphic

/-- Once the actual one-point realization theorem has been proved for a
family, the measurable isomorphism selector has no further choice inputs. -/
def familyIsomorphism {P : Type} {L : CountableRelationalLanguage}
    (M : P → Structures L) (hArity : ∀ s, 0 < L.arity s)
    (hExtension : ∀ p q, ForthExtension (M p) (M q)) (base : P) : P → PermutationGroup :=
  CopyCoding.chosenIsomorphism M (fun _ => M base) (fun p =>
    copyTest_of_extensions (AtomicCompatible.empty_of_positive_arity _ _ hArity)
      (hExtension p base) (hExtension base p))

theorem familyIsomorphism_preserves {P : Type} {L : CountableRelationalLanguage}
    (M : P → Structures L) (hArity : ∀ s, 0 < L.arity s)
    (hExtension : ∀ p q, ForthExtension (M p) (M q)) (base p : P) :
    ∀ s a, M p ⟨s,a⟩ = M base ⟨s,(familyIsomorphism M hArity hExtension base p).toFun ∘ a⟩ :=
  CopyCoding.chosenIsomorphism_preserves _ _ _ p

theorem measurable_familyIsomorphism {P : Type} [MeasurableSpace P]
    {L : CountableRelationalLanguage} (M : P → Structures L)
    (hArity : ∀ s, 0 < L.arity s)
    (hExtension : ∀ p q, ForthExtension (M p) (M q)) (base : P)
    (hM : Measurable M) : Measurable (familyIsomorphism M hArity hExtension base) :=
  CopyCoding.measurable_chosenIsomorphism _ _ _ hM measurable_const

end FSCofinality.PartialIso

end
end

-- Original module: FSCofinalityProof.TokenLiteralMaps
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

abbrev Diagram (L : CountableRelationalLanguage) (X : Type) :=
  ∀ s : L.Symbol, (Fin (L.arity s) → X) → Bool

/-- Complete atomic agreement on a correspondence between two literal
domains, before either domain is enumerated by the natural numbers. -/
def CompatibleOn {L : CountableRelationalLanguage} {X Y : Type}
    (M : Diagram L X) (N : Diagram L Y) (R : Set (X × Y)) : Prop :=
  (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 ↔ p.2 = q.2) ∧
    ∀ s (a : Fin (L.arity s) → X × Y), (∀ i, a i ∈ R) →
      M s (fun i => (a i).1) = N s (fun i => (a i).2)

theorem CompatibleOn.mono {L : CountableRelationalLanguage} {X Y : Type}
    {M : Diagram L X} {N : Diagram L Y} {R S : Set (X × Y)}
    (h : CompatibleOn M N S) (hRS : R ⊆ S) : CompatibleOn M N R :=
  ⟨fun p hp q hq => h.1 p (hRS hp) q (hRS hq),
    fun s a ha => h.2 s a (fun i => hRS (ha i))⟩

theorem CompatibleOn.pair_diagram {L : CountableRelationalLanguage} {X Y : Type}
    {M : Diagram L X} {N : Diagram L Y} {R : Set (X × Y)}
    (h : CompatibleOn M N R) (s : L.Symbol) (p) (hp : p ∈ R) (q) (hq : q ∈ R) :
    M s (twoTuple p.1 q.1) = N s (twoTuple p.2 q.2) := by
  have hh := h.2 s (fun i => if i.val = 0 then p else q) (fun i => by
    dsimp only
    split_ifs
    · exact hp
    · exact hq)
  simpa only [twoTuple,apply_ite] using hh

theorem CompatibleOn.insert_of_unary_binary {L : CountableRelationalLanguage} {X Y : Type}
    {M : Diagram L X} {N : Diagram L Y} {R : Set (X × Y)} (hR : CompatibleOn M N R)
    (hArity : ∀ s, L.arity s ≤ 2) (x : X) (y : Y)
    (hEq : ∀ p ∈ R, x = p.1 ↔ y = p.2)
    (hUnary : ∀ s, L.arity s = 1 → M s (fun _ => x) = N s (fun _ => y))
    (hDiagonal : ∀ s, L.arity s = 2 → M s (fun _ => x) = N s (fun _ => y))
    (hForward : ∀ s, L.arity s = 2 → ∀ p ∈ R,
      M s (twoTuple x p.1) = N s (twoTuple y p.2))
    (hBackward : ∀ s, L.arity s = 2 → ∀ p ∈ R,
      M s (twoTuple p.1 x) = N s (twoTuple p.2 y)) :
    CompatibleOn M N (insert (x,y) R) := by
  constructor
  · intro p hp q hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · simp
    · exact hEq q hq
    · simpa only [eq_comm] using hEq p hp
    · exact hR.1 p hp q hq
  · intro s a ha
    have hcases : L.arity s = 0 ∨ L.arity s = 1 ∨ L.arity s = 2 := by
      have := hArity s
      omega
    rcases hcases with hzero | hone | htwo
    · apply hR.2 s a
      intro i
      exact False.elim (by have := i.isLt; omega)
    · let i₀ : Fin (L.arity s) := ⟨0,by omega⟩
      have hall (i : Fin (L.arity s)) : i = i₀ := by apply Fin.ext; have := i.isLt; omega
      rcases ha i₀ with hn | ho
      · have heq : ∀ i, a i = (x,y) := fun i => (congrArg a (hall i)).trans hn
        simpa only [heq] using hUnary s hone
      · apply hR.2 s a
        intro i
        simpa only [hall i] using ho
    · let i₀ : Fin (L.arity s) := ⟨0,by omega⟩
      let i₁ : Fin (L.arity s) := ⟨1,by omega⟩
      have hcoordinates (i : Fin (L.arity s)) :
          a i = if i.val = 0 then a i₀ else a i₁ := by
        split_ifs with hi
        · exact congrArg a (Fin.ext hi)
        · apply congrArg a
          apply Fin.ext
          change i.val = 1
          have := i.isLt
          omega
      rcases ha i₀ with h₀ | h₀ <;> rcases ha i₁ with h₁ | h₁
      · have heq : ∀ i, a i = (x,y) := by
          intro i
          rw [hcoordinates,h₀,h₁]
          split_ifs <;> rfl
        simpa only [heq] using hDiagonal s htwo
      · have hf : (fun i => (a i).1) = twoTuple x (a i₁).1 := by
          funext i
          rw [hcoordinates,h₀]
          unfold twoTuple
          split_ifs <;> rfl
        have hg : (fun i => (a i).2) = twoTuple y (a i₁).2 := by
          funext i
          rw [hcoordinates,h₀]
          unfold twoTuple
          split_ifs <;> rfl
        rw [hf,hg]
        exact hForward s htwo (a i₁) h₁
      · have hf : (fun i => (a i).1) = twoTuple (a i₀).1 x := by
          funext i
          rw [hcoordinates,h₁]
          unfold twoTuple
          split_ifs <;> rfl
        have hg : (fun i => (a i).2) = twoTuple (a i₀).2 y := by
          funext i
          rw [hcoordinates,h₁]
          unfold twoTuple
          split_ifs <;> rfl
        rw [hf,hg]
        exact hBackward s htwo (a i₀) h₀
      · apply hR.2 s a
        intro i
        rw [hcoordinates]
        split_ifs
        · exact h₀
        · exact h₁


def enumerateDiagram {L : CountableRelationalLanguage} {X : Type}
    (M : Diagram L X) (e : ℕ ≃ X) : Structures L :=
  fun ⟨s,a⟩ => M s (e ∘ a)

theorem compatibleOn_iff_enumeration {L : CountableRelationalLanguage} {X Y : Type}
    (M : Diagram L X) (N : Diagram L Y) (e : ℕ ≃ X) (f : ℕ ≃ Y)
    (R : Set (X × Y)) : CompatibleOn M N R ↔
      AtomicCompatible (enumerateDiagram M e) (enumerateDiagram N f)
        {p | (e p.1,f p.2) ∈ R} := by
  constructor
  · intro h
    constructor
    · intro p hp q hq
      exact ⟨fun heq => f.injective ((h.1 _ hp _ hq).mp (congrArg e heq)),
        fun heq => e.injective ((h.1 _ hp _ hq).mpr (congrArg f heq))⟩
    · intro s a ha
      exact h.2 s (fun i => (e (a i).1,f (a i).2)) ha
  · intro h
    constructor
    · intro p hp q hq
      have hh := h.1 (e.symm p.1,f.symm p.2) (by simpa using hp)
        (e.symm q.1,f.symm q.2) (by simpa using hq)
      exact ⟨fun heq => f.symm.injective (hh.mp (congrArg e.symm heq)),
        fun heq => e.symm.injective (hh.mpr (congrArg f.symm heq))⟩
    · intro s a ha
      have hh := h.2 s (fun i => (e.symm (a i).1,f.symm (a i).2))
        (fun i => by simpa using ha i)
      simpa only [enumerateDiagram,Function.comp_def,Equiv.apply_symm_apply] using hh

theorem preimage_equiv_list (X Y : Type) (e : ℕ ≃ X) (f : ℕ ≃ Y)
    (R : List (ℕ × ℕ)) :
    {p : ℕ × ℕ | (e p.1,f p.2) ∈ R.map (fun q => (e q.1,f q.2))} =
      {p | p ∈ R} := by
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,hqp⟩ := List.mem_map.mp hp
    have hfst := e.injective (congrArg Prod.fst hqp)
    have hsnd := f.injective (congrArg Prod.snd hqp)
    exact (Prod.ext hfst hsnd) ▸ hq
  · intro hp
    exact List.mem_map.mpr ⟨p,hp,rfl⟩

def LiteralForth {L : CountableRelationalLanguage} {X Y : Type}
    (M : Diagram L X) (N : Diagram L Y) : Prop :=
  ∀ R : List (X × Y), CompatibleOn M N {p | p ∈ R} →
    ∀ x : X, ∃ y : Y, CompatibleOn M N {p | p ∈ R ++ [(x,y)]}

theorem forthExtension_of_literal {L : CountableRelationalLanguage} {X Y : Type}
    (M : Diagram L X) (N : Diagram L Y) (e : ℕ ≃ X) (f : ℕ ≃ Y)
    (h : LiteralForth M N) : ForthExtension (enumerateDiagram M e) (enumerateDiagram N f) := by
  intro R hR x
  let S := R.map (fun q => (e q.1,f q.2))
  have hS : CompatibleOn M N {p | p ∈ S} := by
    apply (compatibleOn_iff_enumeration M N e f _).mpr
    change AtomicCompatible (enumerateDiagram M e) (enumerateDiagram N f)
      {p | (e p.1,f p.2) ∈ R.map (fun q => (e q.1,f q.2))}
    rw [preimage_equiv_list]
    exact hR
  obtain ⟨y,hy⟩ := h S hS (e x)
  refine ⟨f.symm y,?_⟩
  have hhy := (compatibleOn_iff_enumeration M N e f _).mp hy
  apply hhy.mono
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · rcases List.mem_singleton.mp hp with rfl
    apply List.mem_append_right
    simp only [List.mem_singleton,Equiv.apply_symm_apply]

end FSCofinality.PartialIso

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

def LiteralCompatible (bottom : ∀ x : (fsTower eta).Carrier,
    Tokens.Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x y : (fsTower eta).Carrier) (R : Set (Vertex eta heta x × Vertex eta heta y)) : Prop :=
  CompatibleOn (L := language eta heta) (diagram eta heta bottom x) (diagram eta heta bottom y) R

theorem forth_modelWithEnumeration_of_literal
    (bottom : ∀ x : (fsTower eta).Carrier,
      Tokens.Token (raw eta heta x (zeroSort eta)) → ℕ → Bool)
    (x y : (fsTower eta).Carrier) (e : ℕ ≃ Vertex eta heta x) (f : ℕ ≃ Vertex eta heta y)
    (h : LiteralForth (L := language eta heta) (diagram eta heta bottom x) (diagram eta heta bottom y)) :
    ForthExtension (modelWithEnumeration eta heta bottom x e)
      (modelWithEnumeration eta heta bottom y f) :=
  forthExtension_of_literal _ _ e f h

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.TokenLiteralForth
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.PartialIso

theorem literalForth_of_fresh {L : CountableRelationalLanguage} {X Y : Type}
    {M : Diagram L X} {N : Diagram L Y}
    (h : ∀ R : List (X × Y), CompatibleOn M N {p | p ∈ R} →
      ∀ x : X, (∀ p ∈ R, x ≠ p.1) →
        ∃ y : Y, CompatibleOn M N {p | p ∈ R ++ [(x,y)]}) : LiteralForth M N := by
  intro R hR x
  by_cases hfresh : ∀ p ∈ R, x ≠ p.1
  · exact h R hR x hfresh
  · push_neg at hfresh
    obtain ⟨p,hp,hpx⟩ := hfresh
    refine ⟨p.2,hR.mono ?_⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hq
    · have heq : q = (x,p.2) := List.mem_singleton.mp hq
      have hpair : (x,p.2) = p := Prod.ext hpx rfl
      exact heq.symm ▸ hpair.symm ▸ hp

end FSCofinality.PartialIso

end
end

-- Original module: FSCofinalityProof.TokenCoordinateExtension
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.Tokens

/-- Repeated rows cause no problem if their prescribed bits agree. -/
theorem bottomListMap_consistent_finite_independence {U I : Type}
    [MeasurableSpace U] [StandardBorelSpace U] [Fintype I]
    (p : I → Token U) (epsilon : I → Bool)
    (hconsistent : ∀ i j, p i = p j → epsilon i = epsilon j) (N : ℕ) :
    ∃ q > N, ∀ i, bottomListMap (p i).1 (p i).2 q = epsilon i := by
  classical
  let S : Finset (Token U) := Finset.univ.image p
  have hpre (v : S) : ∃ i, p i = v.val := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp v.property
    exact ⟨i,hi⟩
  let bit (v : S) : Bool := epsilon (hpre v).choose
  obtain ⟨q,hq,hbits⟩ := bottomListMap_finite_independence
    (fun v : S => v.val) Subtype.val_injective bit N
  refine ⟨q,hq,fun i => ?_⟩
  let v : S := ⟨p i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩
  exact (hbits v).trans (hconsistent (hpre v).choose i (hpre v).choose_spec)

end FSCofinality.Tokens

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

theorem decodedBottom_injective (x : (fsTower eta).Carrier) :
    Function.Injective (decodedBottom eta heta x) := by
  intro v w h
  apply tokenName_injective eta heta x (zeroSort eta)
  exact (decodedBottom_reencode eta heta x v).symm.trans
    ((congrArg (mapToken (atomObject eta heta)) h).trans (decodedBottom_reencode eta heta x w))

theorem bottom_finite_independence (x : (fsTower eta).Carrier) {I : Type} [Fintype I]
    (v : I → Token (raw eta heta x (zeroSort eta))) (epsilon : I → Bool)
    (hconsistent : ∀ i j, v i = v j → epsilon i = epsilon j) (N : ℕ) :
    ∃ q > N, ∀ i, bottom eta heta x (v i) q = epsilon i := by
  exact bottomListMap_consistent_finite_independence
    (fun i => decodedBottom eta heta x (v i)) epsilon
    (fun i j hij => hconsistent i j (decodedBottom_injective eta heta x hij)) N

theorem tokenAt_eq_some_iff {x : (fsTower eta).Carrier} (s : TokenSort eta)
    (u : Vertex eta heta x) (v : Token (raw eta heta x s)) :
    tokenAt eta heta s u = some v ↔ u = .inr ⟨s,v⟩ := by
  cases u with
  | inl n => simp [tokenAt]
  | inr w =>
    rcases w with ⟨t,w⟩
    by_cases ht : t=s
    · subst t
      rw [tokenAt_inr]
      simp only [Option.some.injEq]
      constructor
      · intro h
        subst w
        rfl
      · intro h
        exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2
    · constructor
      · intro h
        simp [tokenAt,ht] at h
      · intro h
        exact False.elim (ht (congrArg Sigma.fst (Sum.inr.inj h)))

theorem LiteralCompatible.sort_eq {x y : (fsTower eta).Carrier}
    {R : Set (Vertex eta heta x × Vertex eta heta y)}
    (hR : LiteralCompatible eta heta (bottom eta heta) x y R) (p) (hp : p ∈ R) :
    sortOf eta heta p.1 = sortOf eta heta p.2 := by
  have hh := hR.2 (.inl (sortOf eta heta p.1)) (fun _ => p) (fun _ => hp)
  change decide (sortOf eta heta p.1 = sortOf eta heta p.1) =
    decide (sortOf eta heta p.2 = sortOf eta heta p.1) at hh
  exact (of_decide_eq_true (hh.symm.trans (decide_eq_true rfl))).symm

theorem tokenAt_none_iff_sort {x : (fsTower eta).Carrier} (s : TokenSort eta)
    (u : Vertex eta heta x) :
    tokenAt eta heta s u = none ↔ sortOf eta heta u ≠ some s := by
  cases u with
  | inl n => simp [tokenAt,sortOf]
  | inr u =>
    rcases u with ⟨t,u⟩
    by_cases ht : t=s
    · subst t
      rw [tokenAt_inr]
      simp [sortOf]
    · simp [tokenAt,sortOf,ht]

def bottomAt (x : (fsTower eta).Carrier) (u : Vertex eta heta x) (n : ℕ) : Bool :=
  (tokenAt eta heta (zeroSort eta) u).elim false (fun v => bottom eta heta x v n)

theorem edgeAt_coordinate_right {x : (fsTower eta).Carrier} (s t : TokenSort eta)
    (f : Token (raw eta heta x s) → Token (raw eta heta x t) → Bool)
    (u : Vertex eta heta x) (n : ℕ) : edgeAt eta heta s t f u (.inl n) = false := by
  unfold edgeAt
  rw [tokenAt_inl]
  cases tokenAt eta heta s u <;> rfl

theorem diagram_coordinate_left (x : (fsTower eta).Carrier)
    (s : OrdinaryRole eta ⊕ (ColumnIndex eta ⊕ (ColumnIndex eta ⊕ Unit)))
    (n : ℕ) (u : Vertex eta heta x) :
    diagram eta heta (bottom eta heta) x (.inr s) (twoTuple (.inl n) u) = false := by
  rcases s with s | (s | (s | s)) <;> rfl

theorem coordinate_insert_compatible {x y : (fsTower eta).Carrier}
    {R : Set (Vertex eta heta x × Vertex eta heta y)}
    (hR : LiteralCompatible eta heta (bottom eta heta) x y R) (n m : ℕ)
    (hfresh : ∀ p ∈ R, (.inl n : Vertex eta heta x) ≠ p.1)
    (hfresh' : ∀ p ∈ R, (.inl m : Vertex eta heta y) ≠ p.2)
    (hbits : ∀ p ∈ R, bottomAt eta heta x p.1 n = bottomAt eta heta y p.2 m) :
    LiteralCompatible eta heta (bottom eta heta) x y (insert (.inl n,.inl m) R) := by
  apply CompatibleOn.insert_of_unary_binary hR
    (fun s => by cases s <;> simp [language,arity]) (.inl n) (.inl m)
  · intro p hp
    exact iff_of_false (hfresh p hp) (hfresh' p hp)
  · intro s hs
    cases s with
    | inl s => rfl
    | inr s => simp [language,arity] at hs
  · intro s hs
    cases s with
    | inl s => simp [language,arity] at hs
    | inr s =>
      rcases s with s | (s | (s | s)) <;> rfl
  · intro s hs p hp
    cases s with
    | inl s => simp [language,arity] at hs
    | inr s =>
      exact (diagram_coordinate_left eta heta x s n p.1).trans
        (diagram_coordinate_left eta heta y s m p.2).symm
  · intro s hs p hp
    cases s with
    | inl s => simp [language,arity] at hs
    | inr s =>
      rcases s with s | (s | (s | s))
      · change edgeAt eta heta _ _ _ p.1 (.inl n) = edgeAt eta heta _ _ _ p.2 (.inl m)
        rw [edgeAt_coordinate_right,edgeAt_coordinate_right]
      · change edgeAt eta heta _ _ _ p.1 (.inl n) = edgeAt eta heta _ _ _ p.2 (.inl m)
        rw [edgeAt_coordinate_right,edgeAt_coordinate_right]
      · change edgeAt eta heta _ _ _ p.1 (.inl n) = edgeAt eta heta _ _ _ p.2 (.inl m)
        rw [edgeAt_coordinate_right,edgeAt_coordinate_right]
      · exact hbits p hp

/-- Actual one-point extension in the coordinate sort. Every incidence
requirement is supplied by finite independence of the bottom decoder. -/
theorem coordinate_extension {x y : (fsTower eta).Carrier}
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (n : ℕ) (hfresh : ∀ p ∈ R, (.inl n : Vertex eta heta x) ≠ p.1) :
    ∃ m : ℕ, LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inl n,.inl m)]} := by
  let I := {i : Fin R.length // ∃ v : Token (raw eta heta y (zeroSort eta)),
    tokenAt eta heta (zeroSort eta) (R.get i).2 = some v}
  let old (i : I) : Token (raw eta heta y (zeroSort eta)) := i.property.choose
  have hold (i : I) : tokenAt eta heta (zeroSort eta) (R.get i.val).2 = some (old i) :=
    i.property.choose_spec
  let epsilon (i : I) : Bool := bottomAt eta heta x (R.get i.val).1 n
  have hconsistent (i j : I) (hij : old i = old j) : epsilon i = epsilon j := by
    have hi := (tokenAt_eq_some_iff eta heta _ _ _).mp (hold i)
    have hj := (tokenAt_eq_some_iff eta heta _ _ _).mp (hold j)
    have htarget : (R.get i.val).2 = (R.get j.val).2 := by rw [hi,hj,hij]
    have hsource := (hR.1 _ (List.get_mem _ i.val) _ (List.get_mem _ j.val)).mpr htarget
    exact congrArg (fun u => bottomAt eta heta x u n) hsource
  let B := Finset.univ.sup (fun i : Fin R.length =>
    (coordinateAt eta heta (R.get i).2).getD 0)
  obtain ⟨m,hm,hbits⟩ := bottom_finite_independence eta heta y old epsilon hconsistent B
  have hfresh' (p) (hp : p ∈ R) : (.inl m : Vertex eta heta y) ≠ p.2 := by
    intro heq
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
    have hi : (coordinateAt eta heta (R.get i).2).getD 0 ≤ B :=
      Finset.le_sup (f := fun i : Fin R.length =>
        (coordinateAt eta heta (R.get i).2).getD 0) (Finset.mem_univ i)
    rw [← heq] at hi
    change m ≤ B at hi
    omega
  have hmatch (p) (hp : p ∈ R) : bottomAt eta heta x p.1 n = bottomAt eta heta y p.2 m := by
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
    cases ht : tokenAt eta heta (zeroSort eta) (R.get i).2 with
    | none =>
      have hs := hR.sort_eq eta heta (R.get i) (List.get_mem _ i)
      have hn := (tokenAt_none_iff_sort eta heta (zeroSort eta) (R.get i).2).mp ht
      have hz : tokenAt eta heta (zeroSort eta) (R.get i).1 = none :=
        (tokenAt_none_iff_sort eta heta _ _).mpr (hs ▸ hn)
      simp only [bottomAt,hz,ht,Option.elim_none]
    | some v =>
      let j : I := ⟨i,⟨v,ht⟩⟩
      have hv : old j = v := Option.some.inj ((hold j).symm.trans ht)
      have hh := hbits j
      rw [hv] at hh
      change bottomAt eta heta x (R.get i).1 n =
        (tokenAt eta heta (zeroSort eta) (R.get i).2).elim false
          (fun w => bottom eta heta y w m)
      rw [ht]
      exact hh.symm
  refine ⟨m,?_⟩
  have hinsert := coordinate_insert_compatible eta heta hR n m hfresh hfresh' hmatch
  apply hinsert.mono
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact Or.inr hp
  · exact Or.inl (List.mem_singleton.mp hp)

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.TokenFiniteCorrespondence
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

def SortEntries (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta) :=
  {i : Fin R.length // sortOf eta heta (R.get i).2 = some s}

instance (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta) :
    Fintype (SortEntries eta heta R s) := inferInstanceAs (Fintype {i : Fin R.length // _})

def targetEntry (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta)
    (i : SortEntries eta heta R s) : Token (raw eta heta y s) :=
  (tokenFiberEquiv eta heta y s).symm ⟨(R.get i.val).2,i.property⟩

def sourceEntry (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R}) (s : TokenSort eta)
    (i : SortEntries eta heta R s) : Token (raw eta heta x s) :=
  (tokenFiberEquiv eta heta x s).symm ⟨(R.get i.val).1,
    (hR.sort_eq eta heta _ (List.get_mem _ i.val)).trans i.property⟩

theorem targetEntry_vertex (R : List (Vertex eta heta x × Vertex eta heta y))
    (s : TokenSort eta) (i : SortEntries eta heta R s) :
    (.inr ⟨s,targetEntry eta heta R s i⟩ : Vertex eta heta y) = (R.get i.val).2 :=
  congrArg Subtype.val ((tokenFiberEquiv eta heta y s).apply_symm_apply _)

theorem sourceEntry_vertex (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (i : SortEntries eta heta R s) :
    (.inr ⟨s,sourceEntry eta heta R hR s i⟩ : Vertex eta heta x) = (R.get i.val).1 :=
  congrArg Subtype.val ((tokenFiberEquiv eta heta x s).apply_symm_apply _)

theorem tokenVertex_injective (z : (fsTower eta).Carrier) (s : TokenSort eta) :
    Function.Injective (fun v : Token (raw eta heta z s) => (.inr ⟨s,v⟩ : Vertex eta heta z)) := by
  intro v w h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2

theorem sourceEntry_eq_iff_targetEntry_eq
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (i j : SortEntries eta heta R s) :
    sourceEntry eta heta R hR s i = sourceEntry eta heta R hR s j ↔
      targetEntry eta heta R s i = targetEntry eta heta R s j := by
  have h := hR.1 (R.get i.val) (List.get_mem _ i.val) (R.get j.val) (List.get_mem _ j.val)
  constructor
  · intro hij
    apply tokenVertex_injective eta heta y s
    dsimp only
    rw [targetEntry_vertex,targetEntry_vertex]
    apply h.mp
    rw [← sourceEntry_vertex eta heta R hR s i,← sourceEntry_vertex eta heta R hR s j,hij]
  · intro hij
    apply tokenVertex_injective eta heta x s
    dsimp only
    rw [sourceEntry_vertex,sourceEntry_vertex]
    apply h.mpr
    rw [← targetEntry_vertex eta heta R s i,← targetEntry_vertex eta heta R s j,hij]

theorem entries_preserve_limit_R
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ)
    (i j : SortEntries eta heta R (.inl lam.val)) :
    Tokens.R (limitProfile eta heta x lam) n (sourceEntry eta heta R hR _ i)
      (sourceEntry eta heta R hR _ j) ↔
    Tokens.R (limitProfile eta heta y lam) n (targetEntry eta heta R _ i)
      (targetEntry eta heta R _ j) := by
  have h := hR.pair_diagram (.inr (.inr (.inr (.inl (lam,n)))))
    (R.get i.val) (List.get_mem _ i.val) (R.get j.val) (List.get_mem _ j.val)
  rw [← sourceEntry_vertex eta heta R hR (.inl lam.val) i,
    ← sourceEntry_vertex eta heta R hR (.inl lam.val) j,
    ← targetEntry_vertex eta heta R (.inl lam.val) i,
    ← targetEntry_vertex eta heta R (.inl lam.val) j] at h
  change edgeAt eta heta _ _ _ (.inr ⟨_,_⟩) (.inr ⟨_,_⟩) =
    edgeAt eta heta _ _ _ (.inr ⟨_,_⟩) (.inr ⟨_,_⟩) at h
  exact decide_eq_decide.mp (by simpa only [edgeAt_inr] using h)

theorem entries_preserve_branch
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ)
    (i : SortEntries eta heta R (.inl lam.val))
    (j : SortEntries eta heta R (.inr (lam,n))) :
    branch eta heta x lam n (sourceEntry eta heta R hR _ i) (sourceEntry eta heta R hR _ j) =
      branch eta heta y lam n (targetEntry eta heta R _ i) (targetEntry eta heta R _ j) := by
  have h := hR.pair_diagram (.inr (.inr (.inl (lam,n))))
    (R.get i.val) (List.get_mem _ i.val) (R.get j.val) (List.get_mem _ j.val)
  rw [← sourceEntry_vertex eta heta R hR (.inl lam.val) i,
    ← sourceEntry_vertex eta heta R hR (.inr (lam,n)) j,
    ← targetEntry_vertex eta heta R (.inl lam.val) i,
    ← targetEntry_vertex eta heta R (.inr (lam,n)) j] at h
  change edgeAt eta heta _ _ _ (.inr ⟨_,_⟩) (.inr ⟨_,_⟩) =
    edgeAt eta heta _ _ _ (.inr ⟨_,_⟩) (.inr ⟨_,_⟩) at h
  simpa only [edgeAt_inr] using h

theorem targetEntry_covers
    (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta)
    (p : Vertex eta heta x × Vertex eta heta y) (hp : p ∈ R)
    (v : Token (raw eta heta y s)) (hv : p.2 = .inr ⟨s,v⟩) :
    ∃ i : SortEntries eta heta R s, R.get i.val = p ∧ targetEntry eta heta R s i = v := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
  let j : SortEntries eta heta R s := ⟨i,by rw [hi,hv]; rfl⟩
  refine ⟨j,hi,?_⟩
  apply tokenVertex_injective eta heta y s
  dsimp only
  exact (targetEntry_vertex eta heta R s j).trans ((congrArg Prod.snd hi).trans hv)

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.GenericTablesHistoryExtensions
section


noncomputable section
open Set

namespace FSCofinality.GenericTables

theorem localCode_eq_of_le (h k : History) {m n : ℕ} (hmn : m ≤ n)
    (heq : h.localCode n = k.localCode n) : h.localCode m = k.localCode m := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact heq
  | succ n IH =>
    by_cases hm : m = n+1
    · rw [hm]
      exact heq
    · exact IH (by omega) (localCode_refines h k n heq)

/-- A fresh local code continues to separate the two histories at every
later level; choosing a later tail cannot erase the separation. -/
theorem localCode_ne_of_le (h k : History) {m n : ℕ} (hmn : m ≤ n)
    (hne : h.localCode m ≠ k.localCode m) : h.localCode n ≠ k.localCode n :=
  fun heq => hne (localCode_eq_of_le h k hmn heq)

theorem localCode_eq_of_same_prefix (h k : History) (M n : ℕ)
    (hn : n ≤ M) (ha : h.activation = k.activation)
    (hk : ∀ i ≤ M, h.noise i = k.noise i) : h.localCode n = k.localCode n := by
  apply (localCode_eq_iff h k n).mpr
  apply Prod.ext
  · change h.activation.filter _ = k.activation.filter _
    rw [ha]
  · change List.ofFn (fun i : Fin (n+1) => h.noise i) =
      List.ofFn (fun i : Fin (n+1) => k.noise i)
    congr 1
    funext i
    exact hk i (by omega)

/-- Every full label in a fixed-history-prefix fiber preserves all previously
fixed local history codes, not just one finite code coordinate. -/
theorem fullLabelSet_preserves_prefix (h : History) (M z : ℕ) (hz : z ∈ fullLabelSet h M) :
    let k := (fullLabelEquiv h.activation.length).symm z
    k.val.activation = h.activation ∧ ∀ n ≤ M, k.val.localCode n = h.localCode n := by
  obtain ⟨k,hk,ha,hnoise⟩ := hz
  have heq : (fullLabelEquiv h.activation.length).symm z = k := by
    rw [← hk,Equiv.symm_apply_apply]
  dsimp
  rw [heq]
  exact ⟨ha,fun n hn => localCode_eq_of_same_prefix k.val h M n hn ha hnoise⟩

def History.appendLate (h : History) (M count : ℕ)
    (hbound : ∀ a ∈ h.activation, a ≤ M) : History where
  activation := h.activation ++ List.replicate count (M+1)
  ordered := by
    apply List.pairwise_append.mpr
    refine ⟨h.ordered,by simp,?_⟩
    intro a ha b hb
    rw [List.eq_of_mem_replicate hb]
    exact (hbound a ha).trans (Nat.le_succ M)
  noise := h.noise

theorem appendLate_localCode (h : History) (M count : ℕ)
    (hbound : ∀ a ∈ h.activation, a ≤ M) (n : ℕ) (hn : n ≤ M) :
    (h.appendLate M count hbound).localCode n = h.localCode n := by
  apply (localCode_eq_iff _ _ n).mpr
  apply Prod.ext
  · change (h.activation ++ List.replicate count (M+1)).filter _ = h.activeTimes n
    apply activeTimes_append_late
    intro a ha
    have heq : a = M+1 := List.eq_of_mem_replicate ha
    omega
  · rfl

theorem bump_localCode (h : History) (M k n : ℕ) (hn : n ≤ M) :
    (h.bump M k).localCode n = h.localCode n :=
  localCode_eq_of_same_prefix _ _ M n hn rfl (fun i hi => bump_noise_prefix h M k i hi)

def History.appendAt (h : History) (time count : ℕ)
    (hbound : ∀ a ∈ h.activation, a ≤ time) : History where
  activation := h.activation ++ List.replicate count time
  ordered := by
    apply List.pairwise_append.mpr
    refine ⟨h.ordered,by simp,?_⟩
    intro a ha b hb
    rw [List.eq_of_mem_replicate hb]
    exact hbound a ha
  noise := h.noise

theorem appendAt_localCode (h : History) (time count : ℕ)
    (hbound : ∀ a ∈ h.activation, a ≤ time) (n : ℕ) (hn : n < time) :
    (h.appendAt time count hbound).localCode n = h.localCode n := by
  apply (localCode_eq_iff _ _ n).mpr
  apply Prod.ext
  · change (h.activation ++ List.replicate count time).filter _ = h.activeTimes n
    apply activeTimes_append_late
    intro a ha
    simpa only [List.eq_of_mem_replicate ha] using hn
  · rfl

def History.noiseBefore (h : History) (n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => h.noise i)

def History.updateNoise (h : History) (n k : ℕ) : History :=
  ⟨h.activation,h.ordered,h.noise.update n k⟩

theorem updateNoise_prefix (h : History) (n k : ℕ) :
    (h.updateNoise n k).noisePrefix n = h.noiseBefore n ++ [k] := by
  unfold History.noisePrefix
  rw [List.ofFn_succ',List.concat_eq_append]
  congr 1
  · apply congrArg List.ofFn
    funext i
    change h.noise.update n k i = h.noise i
    rw [Finsupp.update_apply,if_neg (by omega : (i : ℕ) ≠ n)]
  · simp [History.updateNoise,Finsupp.update_apply]

theorem updateNoise_localCode_at (h : History) (n k : ℕ) :
    (h.updateNoise n k).localCode n = Encodable.encode (h.activeTimes n,h.noiseBefore n ++ [k]) := by
  unfold History.localCode History.localView
  rw [updateNoise_prefix]
  rfl

theorem updateNoise_localCode_earlier (h : History) (n k m : ℕ) (hm : m < n) :
    (h.updateNoise n k).localCode m = h.localCode m := by
  apply localCode_eq_of_same_prefix (h.updateNoise n k) h m m le_rfl rfl
  intro i hi
  change h.noise.update n k i = h.noise i
  rw [Finsupp.update_apply,if_neg (by omega : i ≠ n)]

end FSCofinality.GenericTables

end
end

-- Original module: FSCofinalityProof.TokenHistoryOperations
section


noncomputable section

namespace FSCofinality.Tokens
open GenericTables

theorem activeLength_le_length {U : Type*} (v : Token U) (n : ℕ) :
    activeLength v n ≤ v.1.length := by
  unfold activeLength History.activeTimes
  exact (List.length_filter_le _ _).trans_eq (history v).property

def extendAt {U : Type*} (v : Token U) (time : ℕ) (extra : List U)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ time) : Token U :=
  ofHistory (v.1 ++ extra) ⟨(history v).val.appendAt time extra.length hbound,by
    simp only [History.appendAt,List.length_append,List.length_replicate,(history v).property]⟩

theorem extendAt_history {U : Type*} (v : Token U) (time : ℕ) (extra : List U)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ time) :
    (history (extendAt v time extra hbound)).val =
      (history v).val.appendAt time extra.length hbound := by
  simp only [extendAt,history_ofHistory]

theorem extendAt_localCode {U : Type*} (v : Token U) (time : ℕ) (extra : List U)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ time) (n : ℕ) (hn : n < time) :
    localCode (extendAt v time extra hbound) n = localCode v n := by
  unfold localCode
  rw [extendAt_history]
  exact appendAt_localCode _ _ _ _ _ hn

theorem extendAt_activeTuple {U : Type*} (v : Token U) (time : ℕ) (extra : List U)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ time) (n : ℕ) (hn : n < time) :
    activeTuple (extendAt v time extra hbound) n = activeTuple v n := by
  have hv := (localCode_eq_iff _ _ n).mp (extendAt_localCode v time extra hbound n hn)
  have hl : activeLength (extendAt v time extra hbound) n = activeLength v n :=
    congrArg (fun p : List ℕ × List ℕ => p.1.length) hv
  change (v.1 ++ extra).take _ = v.1.take _
  rw [hl,List.take_append_of_le_length (activeLength_le_length v n)]

def withNoiseAt {U : Type*} (v : Token U) (n k : ℕ) : Token U :=
  ofHistory v.1 ⟨(history v).val.updateNoise n k,(history v).property⟩

theorem withNoiseAt_history {U : Type*} (v : Token U) (n k : ℕ) :
    (history (withNoiseAt v n k)).val = (history v).val.updateNoise n k := by
  simp only [withNoiseAt,history_ofHistory]

theorem withNoiseAt_localCode_at {U : Type*} (v : Token U) (n k : ℕ) :
    localCode (withNoiseAt v n k) n = Encodable.encode
      ((history v).val.activeTimes n,(history v).val.noiseBefore n ++ [k]) := by
  unfold localCode
  rw [withNoiseAt_history]
  exact updateNoise_localCode_at _ _ _

theorem withNoiseAt_localCode_earlier {U : Type*} (v : Token U) (n k m : ℕ) (hm : m < n) :
    localCode (withNoiseAt v n k) m = localCode v m := by
  unfold localCode
  rw [withNoiseAt_history]
  exact updateNoise_localCode_earlier _ _ _ _ hm

theorem withNoiseAt_activeTuple {U : Type*} (v : Token U) (n k m : ℕ) :
    activeTuple (withNoiseAt v n k) m = activeTuple v m := by
  unfold activeTuple activeLength
  rw [withNoiseAt_history]
  rfl

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenLimitStep
section


noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

/-- One constrained branch level: append the actual raw witnesses at that
level, choose a local history label in its genuine infinite fiber, and
preserve every earlier active tuple and local history. -/
theorem limit_branch_step {U : Type} [Nonempty U] {Col : ℕ → Type}
    (profile : ∀ n, U → Col n → Bool) (e n : ℕ)
    (hcol : Function.Injective (fun c : Col n => fun u => profile n u c))
    (v : Token U) (hbound : ∀ a ∈ (history v).val.activation, a ≤ n)
    {ι : Type} [Fintype ι] (c : ι → Token (Col n)) (epsilon : ι → Bool)
    (hconsistent : ∀ i j, c i = c j → epsilon i = epsilon j) (labelBound : ℕ) :
    ∃ w : Token U, ∃ extra : List U,
      w.1 = v.1 ++ extra ∧ labelBound < localCode w n ∧
      (∀ a ∈ (history w).val.activation, a ≤ n) ∧
      (∀ m < n, localCode w m = localCode v m ∧ activeTuple w m = activeTuple v m) ∧
      ∀ i, branchEdge profile genericTable e n w (c i) = epsilon i := by
  classical
  obtain ⟨S,hS⟩ := finite_context_witnesses (profile n) hcol (fun i => (c i).1)
  let extra := S.toList
  let rows := v.1 ++ extra
  let v0 := extendAt v n extra hbound
  have hrows (u : U) (hu : u ∈ S) : u ∈ rows :=
    List.mem_append_right _ (Finset.mem_toList.mpr hu)
  let req : ι → Request := fun i =>
    ⟨e,contextMatrix (rows.map (profile n)) (c i).1,true,(c i).2,epsilon i⟩
  let P := Finset.univ.image req
  have hP : Compatible P := by
    rintro a ha b hb heq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hb
    have hdata : contextMatrix (rows.map (profile n)) (c i).1 =
        contextMatrix (rows.map (profile n)) (c j).1 ∧ (c i).2 = (c j).2 := by
      simpa only [Request.key,req,Prod.mk.injEq,true_and,and_true] using heq
    exact hconsistent i j (Prod.ext (hS rows hrows i j hdata.1) hdata.2)
  have hbound0 : ∀ a ∈ (history v0).val.activation, a ≤ n := by
    intro a ha
    rw [show v0 = extendAt v n extra hbound from rfl,extendAt_history] at ha
    rcases List.mem_append.mp ha with hold | hnew
    · exact hbound a hold
    · exact le_of_eq (List.eq_of_mem_replicate hnew)
  obtain ⟨z,hz,hzN,hbits⟩ := genericTable_realizes P hP
    (.inr (.inl ((history v0).val.activation,(history v0).val.noiseBefore n))) labelBound
  change z ∈ localLabelSet (history v0).val.activation ((history v0).val.noiseBefore n) at hz
  obtain ⟨k,hk⟩ := hz
  let w := withNoiseAt v0 n k
  have hcode : localCode w n = z := by
    rw [show w = withNoiseAt v0 n k from rfl,withNoiseAt_localCode_at,
      activeTimes_eq_self _ _ hbound0]
    exact hk
  have hfull : activeTuple w n = rows := by
    rw [show w = withNoiseAt v0 n k from rfl,withNoiseAt_activeTuple,
      activeTuple_eq_full v0 n hbound0]
    rfl
  have hboundw : ∀ a ∈ (history w).val.activation, a ≤ n := by
    intro a ha
    rw [show w = withNoiseAt v0 n k from rfl,withNoiseAt_history] at ha
    exact hbound0 a ha
  refine ⟨w,extra,rfl,by rwa [hcode],hboundw,?_,?_⟩
  · intro m hm
    refine ⟨?_,?_⟩
    · rw [show w = withNoiseAt v0 n k from rfl,withNoiseAt_localCode_earlier _ _ _ _ hm]
      exact extendAt_localCode v n extra hbound m hm
    · rw [show w = withNoiseAt v0 n k from rfl,withNoiseAt_activeTuple]
      exact extendAt_activeTuple v n extra hbound m hm
  · intro i
    change genericTable (e,contextMatrix ((activeTuple w n).map (profile n)) (c i).1,
      (c i).2,localCode w n) = epsilon i
    rw [hfull,hcode]
    exact hbits (req i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenLimitBlock
section


noncomputable section

namespace FSCofinality.Tokens
open GenericTables

theorem branchEdge_eq_of_snapshot {U : Type*} {Col : ℕ → Type*}
    (profile : ∀ n, U → Col n → Bool) (A : Table) (e n : ℕ) {v w : Token U}
    (hc : localCode v n = localCode w n) (ht : activeTuple v n = activeTuple w n)
    (c : Token (Col n)) : branchEdge profile A e n v c = branchEdge profile A e n w c := by
  simp only [branchEdge,activeProfiles,hc,ht]

/-- The finite branch-level induction in limit one-point extension. Every
processed level is retained literally while later levels add new slots. -/
theorem limit_branch_block {U : Type} [Nonempty U] {Col : ℕ → Type}
    (profile : ∀ n, U → Col n → Bool)
    (hcol : ∀ n, Function.Injective (fun c : Col n => fun u => profile n u c))
    (e count : ℕ → ℕ) (c : ∀ n, Fin (count n) → Token (Col n))
    (epsilon : ∀ n, Fin (count n) → Bool)
    (hconsistent : ∀ n i j, c n i = c n j → epsilon n i = epsilon n j)
    (labelBound : ℕ → ℕ) (v : Token U) (start steps : ℕ)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ start) :
    ∃ w : Token U,
      (∀ a ∈ (history w).val.activation, a ≤ start+steps) ∧
      (∀ m < start, localCode w m = localCode v m ∧ activeTuple w m = activeTuple v m) ∧
      ∀ i < steps, labelBound (start+i) < localCode w (start+i) ∧
        ∀ j, branchEdge profile genericTable (e (start+i)) (start+i) w (c (start+i) j) =
          epsilon (start+i) j := by
  induction steps with
  | zero =>
    refine ⟨v,?_,fun _ _ => ⟨rfl,rfl⟩,?_⟩
    · simpa only [Nat.add_zero] using hbound
    · intro i hi
      omega
  | succ steps IH =>
    obtain ⟨v0,hb0,hpast,hbits⟩ := IH
    obtain ⟨w,extra,_,hlabel,hbw,hkeep,hnew⟩ := limit_branch_step profile
      (e (start+steps)) (start+steps) (hcol _) v0 hb0
      (c (start+steps)) (epsilon (start+steps)) (hconsistent _) (labelBound (start+steps))
    refine ⟨w,?_,?_,?_⟩
    · intro a ha
      exact (hbw a ha).trans (by omega)
    · intro m hm
      have hk := hkeep m (by omega)
      have hp := hpast m hm
      exact ⟨hk.1.trans hp.1,hk.2.trans hp.2⟩
    · intro i hi
      by_cases hold : i < steps
      · have hk := hkeep (start+i) (by omega)
        have hb := hbits i hold
        refine ⟨by rw [hk.1]; exact hb.1,fun j => ?_⟩
        exact (branchEdge_eq_of_snapshot profile genericTable (e (start+i)) (start+i)
          hk.1 hk.2 (c (start+i) j)).trans (hb.2 j)
      · have heq : i = steps := by omega
        subst i
        exact ⟨hlabel,hnew⟩

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenOrdinaryExtension
section


noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

/-- Finite incidence requirements from one decoding role, viewed from the
new point. Different roles may place it on different sides of their tables. -/
structure FiniteRole (U : Type) where
  Opposite : Type
  count : ℕ
  context : Fin count → List Opposite
  label : Fin count → ℕ
  bit : Fin count → Bool
  raw : U → Opposite → Bool
  separated : Function.Injective (fun v => fun u => raw u v)
  direction : Bool
  role : ℕ
  consistent : ∀ i j, context i = context j → label i = label j → bit i = bit j

def orientMatrix (direction : Bool) (M : BoolMatrix) : BoolMatrix :=
  if direction then M else M.transpose

theorem orientMatrix_injective (direction : Bool) : Function.Injective (orientMatrix direction) := by
  intro M N h
  cases direction
  · have hh := congrArg BoolMatrix.transpose h
    simpa only [orientMatrix,Bool.false_eq_true,if_false,BoolMatrix.transpose_transpose] using hh
  · exact h

def FiniteRole.request {U : Type} (r : FiniteRole U) (rows : List U) (j : Fin r.count) : Request :=
  ⟨r.role,orientMatrix r.direction (contextMatrix (rows.map r.raw) (r.context j)),
    r.direction,r.label j,r.bit j⟩

/-- Simultaneous ordinary one-point extension in finitely many incident
roles, preserving an arbitrary already chosen raw context. -/
theorem ordinary_extension {U ι : Type} [Nonempty U] [Fintype ι]
    (r : ι → FiniteRole U) (hr : Function.Injective (fun i => (r i).role))
    (initial : List U) (N : ℕ) :
    ∃ rows : List U, ∃ k > N, (∃ extra, rows = initial ++ extra) ∧
      ∀ i j, genericTable (((r i).request rows j).index k) = (r i).bit j := by
  classical
  have hw (i : ι) : ∃ S : Finset U, ∀ rows : List U, (∀ u ∈ S, u ∈ rows) → ∀ a b,
      contextMatrix (rows.map (r i).raw) ((r i).context a) =
        contextMatrix (rows.map (r i).raw) ((r i).context b) →
          (r i).context a = (r i).context b :=
    finite_context_witnesses (r i).raw (r i).separated (r i).context
  choose S hS using hw
  let allS : Finset U := Finset.univ.biUnion S
  let rows := initial ++ allS.toList
  have hrows (i : ι) (u : U) (hu : u ∈ S i) : u ∈ rows := by
    apply List.mem_append_right
    apply Finset.mem_toList.mpr
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hu⟩
  let P : Finset Request := Finset.univ.image (fun q : Σ i, Fin (r i).count =>
    (r q.1).request rows q.2)
  have hP : Compatible P := by
    rintro a ha b hb heq
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨i',j'⟩,_,rfl⟩ := Finset.mem_image.mp hb
    have hrole : (r i).role = (r i').role := congrArg Prod.fst heq
    have hii : i = i' := hr hrole
    subst i'
    have hdata :
        orientMatrix (r i).direction (contextMatrix (rows.map (r i).raw) ((r i).context j)) =
          orientMatrix (r i).direction (contextMatrix (rows.map (r i).raw) ((r i).context j')) ∧
        (r i).label j = (r i).label j' := by
      simpa only [Request.key,FiniteRole.request,Prod.mk.injEq,true_and,and_true] using heq
    apply (r i).consistent j j' ?_ hdata.2
    exact hS i rows (hrows i) j j' (orientMatrix_injective _ hdata.1)
  obtain ⟨k,_,hk,hbits⟩ := genericTable_realizes P hP (.inl ()) N
  refine ⟨rows,k,hk,⟨allS.toList,rfl⟩,fun i j => ?_⟩
  exact hbits ((r i).request rows j)
    (Finset.mem_image.mpr ⟨⟨i,j⟩,Finset.mem_univ _,rfl⟩)

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenLimitTail
section


noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

theorem fullLabelFiber_snapshot {U : Type*} (v : Token U) (M z : ℕ)
    (hz : z ∈ fullLabelSet (history v).val M) :
    ∀ n ≤ M, localCode (v.1,z) n = localCode v n ∧
      activeTuple (v.1,z) n = activeTuple v n := by
  have hpres := fullLabelSet_preserves_prefix (history v).val M z hz
  dsimp only at hpres
  rw [(history v).property] at hpres
  have ha : (history (v.1,z)).val.activation = (history v).val.activation := by
    simpa only [history] using hpres.1
  intro n hn
  refine ⟨?_,?_⟩
  · simpa only [localCode,history] using hpres.2 n hn
  · unfold activeTuple activeLength History.activeTimes
    rw [ha]

/-- Once the actual full raw tuple and activation list are fixed, the
eventually-zero tail realizes any compatible finite upper-table pattern
without changing any previously fixed branch snapshot. -/
theorem limit_tail_realization {U : Type*} (v : Token U) (M : ℕ)
    (P : Finset Request) (hP : Compatible P) (labelBound : ℕ) :
    ∃ w : Token U, w.1 = v.1 ∧ labelBound < w.2 ∧
      (∀ n ≤ M, localCode w n = localCode v n ∧ activeTuple w n = activeTuple v n) ∧
      ∀ r ∈ P, genericTable (r.index w.2) = r.value := by
  obtain ⟨z,hz,hN,hbits⟩ := genericTable_realizes P hP
    (.inr (.inr ((history v).val,M))) labelBound
  exact ⟨(v.1,z),rfl,hN,fullLabelFiber_snapshot v M z hz,hbits⟩

/-- Late raw witnesses for ordinary upper roles preserve the complete
already fixed branch snapshots, including the active profile tuples. -/
theorem late_witnesses_preserve {U : Type*} (v : Token U) (M : ℕ) (extra : List U)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ M) :
    ∃ w : Token U, w.1 = v.1 ++ extra ∧
      ∀ n ≤ M, localCode w n = localCode v n ∧ activeTuple w n = activeTuple v n := by
  let hb : ∀ a ∈ (history v).val.activation, a ≤ M+1 :=
    fun a ha => (hbound a ha).trans (Nat.le_succ M)
  refine ⟨extendAt v (M+1) extra hb,rfl,fun n hn => ?_⟩
  exact ⟨extendAt_localCode v (M+1) extra hb n (by omega),
    extendAt_activeTuple v (M+1) extra hb n (by omega)⟩

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenLimitUpper
section


noncomputable section

namespace FSCofinality.Tokens
open GenericTables

/-- Ordinary upper roles are met after all branch levels have been fixed.
Their actual raw witnesses activate later than `M`; the final tail varies
inside the full-history prefix fiber and retains every earlier snapshot. -/
theorem limit_upper_extension {U ι : Type} [Nonempty U] [Fintype ι]
    (r : ι → FiniteRole U) (hr : Function.Injective (fun i => (r i).role))
    (v : Token U) (M : ℕ) (hbound : ∀ a ∈ (history v).val.activation, a ≤ M)
    (labelBound : ℕ) :
    ∃ w : Token U, labelBound < w.2 ∧
      (∀ n ≤ M, localCode w n = localCode v n ∧ activeTuple w n = activeTuple v n) ∧
      ∀ i j, genericTable (((r i).request w.1 j).index w.2) = (r i).bit j := by
  classical
  obtain ⟨rows,k,_,⟨extra,hrows⟩,hreq⟩ := ordinary_extension r hr v.1 0
  let P : Finset Request := Finset.univ.image (fun q : Σ i, Fin (r i).count =>
    (r q.1).request rows q.2)
  have hP : Compatible P := by
    apply compatible_of_realization genericTable P k
    intro a ha
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp ha
    exact hreq i j
  obtain ⟨v0,hv0,hprefix⟩ := late_witnesses_preserve v M extra hbound
  have htuple : v0.1 = rows := hv0.trans hrows.symm
  obtain ⟨w,hwt,hlabel,hsnap,hbits⟩ := limit_tail_realization v0 M P hP labelBound
  refine ⟨w,hlabel,?_,?_⟩
  · intro n hn
    have hs := hsnap n hn
    have hp := hprefix n hn
    exact ⟨hs.1.trans hp.1,hs.2.trans hp.2⟩
  · intro i j
    rw [hwt,htuple]
    exact hbits ((r i).request rows j)
      (Finset.mem_image.mpr ⟨⟨i,j⟩,Finset.mem_univ _,rfl⟩)

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.GenericTablesHistorySorting
section


noncomputable section

namespace FSCofinality.GenericTables

/-- A sorted activation list activates an initial segment, exactly as used
by `Tokens.activeTuple`; no later slot is silently selected out of order. -/
theorem filter_le_eq_take (a : List ℕ) (ha : a.Pairwise (· ≤ ·)) (n : ℕ) :
    a.filter (fun t => decide (t ≤ n)) =
      a.take ((a.filter (fun t => decide (t ≤ n))).length) := by
  induction a with
  | nil => rfl
  | cons x a IH =>
    have hpair := List.pairwise_cons.mp ha
    by_cases hx : x ≤ n
    · simp only [List.filter_cons,decide_eq_true hx,if_true,List.length_cons]
      rw [List.take_succ_cons,← IH hpair.2]
    · have he : a.filter (fun t => decide (t ≤ n)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simpa only [decide_eq_true_eq] using
          not_le.mpr ((lt_of_not_ge hx).trans_le (hpair.1 y hy))
      simp [hx,he]

theorem activeTimes_is_initial_segment (h : History) (n : ℕ) :
    h.activeTimes n = h.activation.take (h.activeTimes n).length :=
  filter_le_eq_take h.activation h.ordered n

end FSCofinality.GenericTables

end
end

-- Original module: FSCofinalityProof.TokenAnchor
section


noncomputable section
open Set

namespace FSCofinality.GenericTables

theorem activeTimes_restrict (h : History) {m n : ℕ} (hmn : m ≤ n) :
    h.activeTimes m = (h.activeTimes n).filter (fun a => decide (a ≤ m)) := by
  simp only [History.activeTimes,List.filter_filter]
  congr 1
  funext a
  by_cases ha : a ≤ m
  · have hb : a ≤ n := ha.trans hmn
    simp [ha,hb]
  · simp [ha]

def History.truncate (h : History) (N : ℕ) : History where
  activation := h.activeTimes N
  ordered := h.ordered.filter _
  noise := h.noise.filter (fun i => i ≤ N)

theorem truncate_activeTimes (h : History) (N m : ℕ) (hm : m ≤ N) :
    (h.truncate N).activeTimes m = h.activeTimes m := (activeTimes_restrict h hm).symm

theorem truncate_bound (h : History) (N : ℕ) :
    ∀ a ∈ (h.truncate N).activation, a ≤ N := by
  intro a ha
  exact of_decide_eq_true (List.mem_filter.mp ha).2

theorem truncate_localCode (h : History) (N m : ℕ) (hm : m ≤ N) :
    (h.truncate N).localCode m = h.localCode m := by
  apply (localCode_eq_iff _ _ m).mpr
  apply Prod.ext
  · exact truncate_activeTimes h N m hm
  · change List.ofFn (fun i : Fin (m+1) => (h.truncate N).noise i) =
      List.ofFn (fun i : Fin (m+1) => h.noise i)
    congr 1
    funext i
    change h.noise.filter (fun j => j ≤ N) i = h.noise i
    rw [Finsupp.filter_apply,if_pos (by omega : (i : ℕ) ≤ N)]

end FSCofinality.GenericTables

namespace FSCofinality.Tokens
open GenericTables

theorem activeLength_le_of_level {U : Type*} (v : Token U) {m n : ℕ} (hmn : m ≤ n) :
    activeLength v m ≤ activeLength v n := by
  unfold activeLength
  rw [activeTimes_restrict _ hmn]
  exact List.length_filter_le _ _

/-- Copy precisely the anchor's existing active slots and history prefix;
its future slots and noise are not copied into the new point. -/
def truncate {U : Type*} (v : Token U) (N : ℕ) : Token U :=
  ofHistory (activeTuple v N) ⟨(history v).val.truncate N,by
    change activeLength v N = (v.1.take (activeLength v N)).length
    simp only [List.length_take,Nat.min_eq_left (activeLength_le_length v N)]⟩

theorem truncate_history {U : Type*} (v : Token U) (N : ℕ) :
    (history (truncate v N)).val = (history v).val.truncate N := by
  simp only [truncate,history_ofHistory]

theorem truncate_activation_bound {U : Type*} (v : Token U) (N : ℕ) :
    ∀ a ∈ (history (truncate v N)).val.activation, a ≤ N := by
  rw [truncate_history]
  exact truncate_bound _ _

theorem truncate_snapshot {U : Type*} (v : Token U) (N m : ℕ) (hm : m ≤ N) :
    localCode (truncate v N) m = localCode v m ∧ activeTuple (truncate v N) m = activeTuple v m := by
  refine ⟨?_,?_⟩
  · unfold localCode
    rw [truncate_history]
    exact truncate_localCode _ _ _ hm
  · have hl : activeLength (truncate v N) m = activeLength v m := by
      unfold activeLength
      rw [truncate_history,truncate_activeTimes _ _ _ hm]
    change ((v.1.take (activeLength v N)).take (activeLength (truncate v N) m)) = _
    rw [hl,List.take_take,Nat.min_eq_left (activeLength_le_of_level v hm)]
    rfl

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenLimitExtension
section


noncomputable section

namespace FSCofinality.Tokens
open GenericTables

/-- Limit one-point extension, starting from a prescribed finite history.
The new point separates from every old point at `start`, retains the entire
earlier history, realizes the finitely many branch levels, and then realizes
all ordinary upper requirements without disturbing those choices. -/
theorem limit_extension_core {U : Type} [Nonempty U] {Col : ℕ → Type}
    (profile : ∀ n, U → Col n → Bool)
    (hcol : ∀ n, Function.Injective (fun c : Col n => fun u => profile n u c))
    (e count : ℕ → ℕ) (c : ∀ n, Fin (count n) → Token (Col n))
    (epsilon : ∀ n, Fin (count n) → Bool)
    (hconsistent : ∀ n i j, c n i = c n j → epsilon n i = epsilon n j)
    {Old Upper : Type} [Fintype Old] [Fintype Upper]
    (old : Old → Token U) (upper : Upper → FiniteRole U)
    (hupper : Function.Injective (fun i => (upper i).role))
    (v : Token U) (start steps : ℕ) (hsteps : 0 < steps)
    (hbound : ∀ a ∈ (history v).val.activation, a ≤ start) (copyBound : ℕ) :
    ∃ w : Token U, copyBound < w.2 ∧
      (∀ m < start, localCode w m = localCode v m ∧ activeTuple w m = activeTuple v m) ∧
      (∀ n ≥ start, ∀ i, ¬ R profile n w (old i)) ∧
      (∀ i < steps, ∀ j,
        branchEdge profile genericTable (e (start+i)) (start+i) w (c (start+i) j) =
          epsilon (start+i) j) ∧
      ∀ i j, genericTable (((upper i).request w.1 j).index w.2) = (upper i).bit j := by
  classical
  let B : ℕ := Finset.univ.sup (fun i : Old => localCode (old i) start)
  obtain ⟨v0,hb0,hpast,hbits⟩ := limit_branch_block profile hcol e count c epsilon
    hconsistent (fun _ => B) v start steps hbound
  obtain ⟨w,hcopy,hsnap,hupperbits⟩ := limit_upper_extension upper hupper v0
    (start+steps) hb0 copyBound
  have hstart : B < localCode w start := by
    have hb := (hbits 0 hsteps).1
    simp only [Nat.add_zero] at hb
    rw [(hsnap start (by omega)).1]
    exact hb
  refine ⟨w,hcopy,?_,?_,?_,hupperbits⟩
  · intro m hm
    have hs := hsnap m (by omega)
    have hp := hpast m hm
    exact ⟨hs.1.trans hp.1,hs.2.trans hp.2⟩
  · intro n hn i hR
    have heq : localCode w start = localCode (old i) start :=
      localCode_eq_of_le (history w).val (history (old i)).val hn hR.1
    have hi : localCode (old i) start ≤ B :=
      Finset.le_sup (f := fun i : Old => localCode (old i) start) (Finset.mem_univ i)
    rw [heq] at hstart
    exact not_lt_of_ge hi hstart
  · intro i hi j
    have hs := hsnap (start+i) (by omega)
    exact (branchEdge_eq_of_snapshot profile genericTable (e (start+i)) (start+i)
      hs.1 hs.2 (c (start+i) j)).trans ((hbits i hi).2 j)

/-- The anchored form retains the complete early equivalence type. Any
consistent extension sharing a class last at `N` has this form, with its
old anchor supplying all earlier branch bits. -/
theorem anchored_limit_extension {U : Type} [Nonempty U] {Col : ℕ → Type}
    (profile : ∀ n, U → Col n → Bool)
    (hcol : ∀ n, Function.Injective (fun c : Col n => fun u => profile n u c))
    (e count : ℕ → ℕ) (c : ∀ n, Fin (count n) → Token (Col n))
    (epsilon : ∀ n, Fin (count n) → Bool)
    (hconsistent : ∀ n i j, c n i = c n j → epsilon n i = epsilon n j)
    {Old Upper : Type} [Fintype Old] [Fintype Upper]
    (old : Old → Token U) (upper : Upper → FiniteRole U)
    (hupper : Function.Injective (fun i => (upper i).role))
    (anchor : Token U) (N steps : ℕ) (hsteps : 0 < steps) (copyBound : ℕ) :
    ∃ w : Token U, copyBound < w.2 ∧
      (∀ m ≤ N, R profile m w anchor) ∧
      (∀ n > N, ∀ i, ¬ R profile n w (old i)) ∧
      (∀ i < steps, ∀ j,
        branchEdge profile genericTable (e (N+1+i)) (N+1+i) w (c (N+1+i) j) =
          epsilon (N+1+i) j) ∧
      ∀ i j, genericTable (((upper i).request w.1 j).index w.2) = (upper i).bit j := by
  have hb : ∀ a ∈ (history (truncate anchor N)).val.activation, a ≤ N+1 :=
    fun a ha => (truncate_activation_bound anchor N a ha).trans (Nat.le_succ N)
  obtain ⟨w,hcopy,hpast,hsep,hbranch,hupperbits⟩ := limit_extension_core profile hcol
    e count c epsilon hconsistent old upper hupper (truncate anchor N) (N+1) steps hsteps hb copyBound
  refine ⟨w,hcopy,?_,?_,hbranch,hupperbits⟩
  · intro m hm
    have hp := hpast m (by omega)
    have ha := truncate_snapshot anchor N m hm
    refine ⟨hp.1.trans ha.1,?_⟩
    simp only [activeProfiles,hp.2,ha.2]
  · intro n hn
    exact hsep n (by omega)

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenFiniteTypes
section


noncomputable section

namespace FSCofinality.Tokens

theorem finite_type_down {Old : Type*} (r : ℕ → Old → Prop)
    (hdown : ∀ n i, r (n+1) i → r n i) {m n : ℕ} (hmn : m ≤ n)
    (i : Old) (hr : r n i) : r m i := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact hr
  | succ n IH =>
    by_cases hm : m = n+1
    · rw [hm]
      exact hr
    · exact IH (by omega) (hdown n i hr)

/-- Every consistent finite one-point type in nested eventually separating
equivalence relations is either wholly separate, or anchored through one
last finite level and wholly separate thereafter. -/
theorem classify_finite_limit_type {Old : Type*} [Fintype Old]
    (E : ℕ → Old → Old → Prop) (r : ℕ → Old → Prop)
    (hdown : ∀ n i, r (n+1) i → r n i)
    (hsep : ∀ i, ∃ N, ∀ n ≥ N, ¬ r n i)
    (hcoherent : ∀ n i, r n i → ∀ j, r n j ↔ E n i j) :
    (∀ n i, ¬ r n i) ∨ ∃ N i, r N i ∧
      (∀ m ≤ N, ∀ j, r m j ↔ E m i j) ∧ ∀ n > N, ∀ j, ¬ r n j := by
  classical
  by_cases hnone : ∀ n i, ¬ r n i
  · exact Or.inl hnone
  right
  choose bound hbound using hsep
  let B := Finset.univ.sup bound
  have hlt (n : ℕ) (i : Old) (hr : r n i) : n < B := by
    have hi : bound i ≤ B := Finset.le_sup (f := bound) (Finset.mem_univ i)
    by_contra hn
    exact hbound i n (by omega) hr
  let S := (Finset.range B).filter (fun n => ∃ i, r n i)
  have hS : S.Nonempty := by
    push_neg at hnone
    obtain ⟨n,i,hr⟩ := hnone
    exact ⟨n,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hlt n i hr),i,hr⟩⟩
  let N := S.max' hS
  have hN : N ∈ S := Finset.max'_mem _ _
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hN).2
  refine ⟨N,i,hi,?_,?_⟩
  · intro m hm j
    exact hcoherent m i (finite_type_down r hdown hm i hi) j
  · intro n hn j hr
    have hnS : n ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hlt n j hr),j,hr⟩
    have hle : n ≤ N := Finset.le_max' _ _ hnS
    omega

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenLimitFiniteType
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.Tokens
open GenericTables

theorem branchEdge_eq_of_R {U : Type} {Col : ℕ → Type}
    (profile : ∀ n, U → Col n → Bool) (A : Table) (e n : ℕ)
    {v w : Token U} (h : R profile n v w) (c : Token (Col n)) :
    branchEdge profile A e n v c = branchEdge profile A e n w c := by
  simp only [branchEdge,h.1,h.2]

/-- Transfer of the full nested-equivalence type together with every finite
branch requirement and all ordinary roles. The old correspondence supplies
only its actual atomic agreements, rather than an extension assumption. -/
theorem limit_finite_type_extension
    {U V : Type} [Nonempty V] {ColX ColY : ℕ → Type}
    (PX : ∀ n, U → ColX n → Bool) (PY : ∀ n, V → ColY n → Bool)
    (jx : ∀ n, ColX n → ColX (n+1))
    (hxprop : ∀ n u c, PX (n+1) u (jx n c) = PX n u c)
    (hxinj : Function.Injective (fun u => fun n => PX n u))
    (hycol : ∀ n, Function.Injective (fun c => fun u => PY n u c))
    (e count : ℕ → ℕ) (cx : ∀ n, Fin (count n) → Token (ColX n))
    (cy : ∀ n, Fin (count n) → Token (ColY n))
    {Old Upper : Type} [Fintype Old] [Fintype Upper]
    (oldX : Old → Token U) (oldY : Old → Token V)
    (hOldR : ∀ n i j, R PX n (oldX i) (oldX j) ↔ R PY n (oldY i) (oldY j))
    (hOldBranch : ∀ n i j,
      branchEdge PX genericTable (e n) n (oldX i) (cx n j) =
      branchEdge PY genericTable (e n) n (oldY i) (cy n j))
    (upper : Upper → FiniteRole V) (hupper : Function.Injective (fun i => (upper i).role))
    (v : Token U) (hfresh : ∀ i, v ≠ oldX i)
    (hconsistent : ∀ n i j, cy n i = cy n j →
      branchEdge PX genericTable (e n) n v (cx n i) =
      branchEdge PX genericTable (e n) n v (cx n j))
    (bound : ℕ) (hbound : ∀ n, bound < n → count n = 0) (copyBound : ℕ) :
    ∃ w : Token V, copyBound < w.2 ∧
      (∀ n i, R PY n w (oldY i) ↔ R PX n v (oldX i)) ∧
      (∀ n j, branchEdge PY genericTable (e n) n w (cy n j) =
        branchEdge PX genericTable (e n) n v (cx n j)) ∧
      ∀ i j, genericTable (((upper i).request w.1 j).index w.2) = (upper i).bit j := by
  let r (n : ℕ) (i : Old) : Prop := R PX n v (oldX i)
  have hdown (n : ℕ) (i : Old) : r (n+1) i → r n i :=
    R_refines PX jx hxprop n
  have hsep (i : Old) : ∃ N, ∀ n ≥ N, ¬r n i := by
    have hnot : ¬∀ n, r n i := fun hall =>
      hfresh i (all_R_separate PX jx hxprop hxinj hall)
    push_neg at hnot
    obtain ⟨N,hN⟩ := hnot
    exact ⟨N,fun n hn hr => hN (finite_type_down r hdown hn i hr)⟩
  have hcoherent (n : ℕ) (i : Old) (hi : r n i) (j : Old) :
      r n j ↔ R PY n (oldY i) (oldY j) := by
    rw [← hOldR n i j]
    exact ⟨fun hj => (R_equivalence PX n).trans ((R_equivalence PX n).symm hi) hj,
      fun hij => (R_equivalence PX n).trans hi hij⟩
  let epsilon (n : ℕ) (j : Fin (count n)) : Bool :=
    branchEdge PX genericTable (e n) n v (cx n j)
  obtain hnone | ⟨N,i,hi,hthrough,htail⟩ :=
    classify_finite_limit_type (fun n i j => R PY n (oldY i) (oldY j)) r hdown hsep hcoherent
  · let v₀ : Token V := ofHistory [] (basicHistory 0 0)
    have hactivation : ∀ a ∈ (history v₀).val.activation, a ≤ 0 := by
      intro a ha
      simp [v₀,basicHistory,history_ofHistory] at ha
    obtain ⟨w,hw,_,hseparate,hbranch,hordinary⟩ := limit_extension_core PY hycol e count cy
      epsilon hconsistent oldY upper hupper v₀ 0 (bound+1) (by omega) hactivation copyBound
    refine ⟨w,hw,?_,?_,hordinary⟩
    · intro n j
      exact iff_of_false (hseparate n (by omega) j) (hnone n j)
    · intro n j
      have hn : n ≤ bound := by
        by_contra hn
        have hz := hbound n (by omega)
        have := j.isLt
        omega
      let matched (k : ℕ) : Prop := ∀ j : Fin (count k),
        branchEdge PY genericTable (e k) k w (cy k j) = epsilon k j
      have hh : matched (0+n) := hbranch n (by omega)
      have hh' : matched n := (Nat.zero_add n) ▸ hh
      exact hh' j
  · obtain ⟨w,hw,hthroughW,hseparate,hbranch,hordinary⟩ := anchored_limit_extension PY hycol
      e count cy epsilon hconsistent oldY upper hupper (oldY i) N (bound+1) (by omega) copyBound
    refine ⟨w,hw,?_,?_,hordinary⟩
    · intro n j
      by_cases hn : n ≤ N
      · have hwanchor := hthroughW n hn
        have heq : R PY n w (oldY j) ↔ R PY n (oldY i) (oldY j) :=
          ⟨fun h => (R_equivalence PY n).trans ((R_equivalence PY n).symm hwanchor) h,
            fun h => (R_equivalence PY n).trans hwanchor h⟩
        exact heq.trans (hthrough n hn j).symm
      · exact iff_of_false (hseparate n (by omega) j) (htail n (by omega) j)
    · intro n j
      by_cases hn : n ≤ N
      · have hvanchor := finite_type_down r hdown hn i hi
        exact (branchEdge_eq_of_R PY genericTable (e n) n (hthroughW n hn) (cy n j)).trans
          ((hOldBranch n i j).symm.trans
            (branchEdge_eq_of_R PX genericTable (e n) n hvanchor (cx n j)).symm)
      · have hnb : n ≤ bound := by
          by_contra hnb
          have hz := hbound n (by omega)
          have := j.isLt
          omega
        have hnrewrite : N+1+(n-(N+1)) = n := by omega
        have hh := hbranch (n-(N+1)) (by omega)
        rw [hnrewrite] at hh
        exact hh j

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenBottomExtension
section


noncomputable section
open Set

namespace FSCofinality.Tokens
open GenericTables

/-- The bottom map may be evaluated after an actual semantic decoder into
a standard Borel space; the raw witness pool itself needs no measurable structure. -/
theorem ordinary_bottom_extension_mapped {U V ι : Type} [Nonempty U]
    [MeasurableSpace V] [StandardBorelSpace V] [Fintype ι]
    (f : U → V) (r : ι → FiniteRole U) (hr : Function.Injective (fun i => (r i).role))
    (initial : List U) (s : List Bool) (N : ℕ) :
    ∃ rows : List U, ∃ k > N, (∃ extra, rows = initial ++ extra) ∧
      (∀ i j, genericTable (((r i).request rows j).index k) = (r i).bit j) ∧
      Bottom.bitsPrefix (bottomListMap (rows.map f) k) s.length = s := by
  classical
  have hw (i : ι) : ∃ S : Finset U, ∀ rows : List U, (∀ u ∈ S, u ∈ rows) → ∀ a b,
      contextMatrix (rows.map (r i).raw) ((r i).context a) =
        contextMatrix (rows.map (r i).raw) ((r i).context b) →
          (r i).context a = (r i).context b :=
    finite_context_witnesses (r i).raw (r i).separated (r i).context
  choose S hS using hw
  let allS : Finset U := Finset.univ.biUnion S
  let rows := initial ++ allS.toList
  have hrows (i : ι) (u : U) (hu : u ∈ S i) : u ∈ rows := by
    apply List.mem_append_right
    apply Finset.mem_toList.mpr
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hu⟩
  let P : Finset Request := Finset.univ.image (fun q : Σ i, Fin (r i).count =>
    (r q.1).request rows q.2)
  have hP : Compatible P := by
    rintro a ha b hb heq
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨i',j'⟩,_,rfl⟩ := Finset.mem_image.mp hb
    have hii : i = i' := hr (congrArg Prod.fst heq)
    subst i'
    have hdata :
        orientMatrix (r i).direction (contextMatrix (rows.map (r i).raw) ((r i).context j)) =
          orientMatrix (r i).direction (contextMatrix (rows.map (r i).raw) ((r i).context j')) ∧
        (r i).label j = (r i).label j' := by
      simpa only [Request.key,FiniteRole.request,Prod.mk.injEq,true_and,and_true] using heq
    exact (r i).consistent j j'
      (hS i rows (hrows i) j j' (orientMatrix_injective _ hdata.1)) hdata.2
  obtain ⟨k,hk,hbits,hbottom⟩ :=
    Bottom.bottomMap_realization (contextOfList (rows.map f)) ⟨P,hP⟩ s N
  refine ⟨rows,k,hk,⟨allS.toList,rfl⟩,?_,hbottom⟩
  intro i j
  exact hbits ((r i).request rows j)
    (Finset.mem_image.mpr ⟨⟨i,j⟩,Finset.mem_univ _,rfl⟩)

/-- Simultaneous ordinary extension can prescribe a finite bottom prefix
while preserving every previously chosen entry of the raw context. -/
theorem ordinary_bottom_extension {U ι : Type} [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
    [Fintype ι] (r : ι → FiniteRole U) (hr : Function.Injective (fun i => (r i).role))
    (initial : List U) (s : List Bool) (N : ℕ) :
    ∃ rows : List U, ∃ k > N, (∃ extra, rows = initial ++ extra) ∧
      (∀ i j, genericTable (((r i).request rows j).index k) = (r i).bit j) ∧
      Bottom.bitsPrefix (bottomListMap rows k) s.length = s := by
  classical
  have hw (i : ι) : ∃ S : Finset U, ∀ rows : List U, (∀ u ∈ S, u ∈ rows) → ∀ a b,
      contextMatrix (rows.map (r i).raw) ((r i).context a) =
        contextMatrix (rows.map (r i).raw) ((r i).context b) →
          (r i).context a = (r i).context b :=
    finite_context_witnesses (r i).raw (r i).separated (r i).context
  choose S hS using hw
  let allS : Finset U := Finset.univ.biUnion S
  let rows := initial ++ allS.toList
  have hrows (i : ι) (u : U) (hu : u ∈ S i) : u ∈ rows := by
    apply List.mem_append_right
    apply Finset.mem_toList.mpr
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hu⟩
  let P : Finset Request := Finset.univ.image (fun q : Σ i, Fin (r i).count =>
    (r q.1).request rows q.2)
  have hP : Compatible P := by
    rintro a ha b hb heq
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨⟨i',j'⟩,_,rfl⟩ := Finset.mem_image.mp hb
    have hrole : (r i).role = (r i').role := congrArg Prod.fst heq
    have hii : i = i' := hr hrole
    subst i'
    have hdata :
        orientMatrix (r i).direction (contextMatrix (rows.map (r i).raw) ((r i).context j)) =
          orientMatrix (r i).direction (contextMatrix (rows.map (r i).raw) ((r i).context j')) ∧
        (r i).label j = (r i).label j' := by
      simpa only [Request.key,FiniteRole.request,Prod.mk.injEq,true_and,and_true] using heq
    apply (r i).consistent j j' ?_ hdata.2
    exact hS i rows (hrows i) j j' (orientMatrix_injective _ hdata.1)
  obtain ⟨k,hk,hbits,hbottom⟩ :=
    Bottom.bottomMap_realization (contextOfList rows) ⟨P,hP⟩ s N
  refine ⟨rows,k,hk,⟨allS.toList,rfl⟩,?_,hbottom⟩
  intro i j
  exact hbits ((r i).request rows j)
    (Finset.mem_image.mpr ⟨⟨i,j⟩,Finset.mem_univ _,rfl⟩)

/-- The bottom requirements may instead be presented at arbitrary finitely
many natural-number coordinates, including repeated coordinates. -/
theorem ordinary_bottom_coordinates_extension {U ι J : Type}
    [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U] [Fintype ι] [Fintype J]
    (r : ι → FiniteRole U) (hr : Function.Injective (fun i => (r i).role))
    (initial : List U) (coordinate : J → ℕ) (epsilon : J → Bool)
    (hconsistent : ∀ i j, coordinate i = coordinate j → epsilon i = epsilon j)
    (N : ℕ) :
    ∃ rows : List U, ∃ k > N, (∃ extra, rows = initial ++ extra) ∧
      (∀ i j, genericTable (((r i).request rows j).index k) = (r i).bit j) ∧
      ∀ j, bottomListMap rows k (coordinate j) = epsilon j := by
  classical
  let f : ℕ → Bool := fun n => if h : ∃ j, coordinate j = n then epsilon h.choose else false
  have hf (j : J) : f (coordinate j) = epsilon j := by
    dsimp [f]
    split_ifs with h
    · exact hconsistent h.choose j h.choose_spec
    · exact False.elim (h ⟨j,rfl⟩)
  let m := Finset.univ.sup coordinate + 1
  let s := Bottom.bitsPrefix f m
  obtain ⟨rows,k,hk,hrows,hreq,hbottom⟩ := ordinary_bottom_extension r hr initial s N
  refine ⟨rows,k,hk,hrows,hreq,fun j => ?_⟩
  have hj : coordinate j < m := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j))
  have he := congrArg (fun t : List Bool => t[coordinate j]?.getD false) hbottom
  have he' : bottomListMap rows k (coordinate j) = f (coordinate j) := by
    simpa only [s,Bottom.bitsPrefix,List.length_ofFn,List.getElem?_ofFn,
      dif_pos hj,Option.getD_some] using he
  exact he'.trans (hf j)

end FSCofinality.Tokens

end
end

-- Original module: FSCofinalityProof.TokenFiniteRoles
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Ordinal Order

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

theorem rowSort_injective : Function.Injective (rowSort eta) := by
  intro e f hef
  rcases e with e | e <;> rcases f with f | f
  · apply congrArg Sum.inl
    apply Subtype.ext
    have hr := congrArg (fun s : TokenSort eta => match s with
      | .inl a => Frame.rank a
      | .inr _ => 0) hef
    simp only [rowSort,mainSort,Frame.rank_ofOrdinal] at hr
    have heq : Frame.rank e.val = Frame.rank f.val :=
      (Ordinal.add_right_cancel 1).mp (by simpa only [Nat.cast_one] using hr)
    have hinj : Function.Injective (Frame.rank (η := eta)) := by
      intro a b hab
      exact Ordinal.ToType.mk.symm.injective (Subtype.ext hab)
    exact hinj heq
  · cases hef
  · cases hef
  · exact congrArg Sum.inr (Sum.inr.inj hef)

theorem rowSort_ne_colSort (e : OrdinaryRole eta) : rowSort eta e ≠ colSort eta e := by
  rcases e with e | e
  · intro h
    have hr := congrArg (fun s : TokenSort eta => match s with
      | .inl a => Frame.rank a
      | .inr _ => 0) h
    simp only [rowSort,colSort,mainSort,Frame.rank_ofOrdinal] at hr
    exact (ne_of_gt (lt_add_one (Frame.rank e.val))) hr
  · intro h
    cases h

theorem rowSort_ne_limit (e : OrdinaryRole eta) (lam : LimitIndex eta) :
    rowSort eta e ≠ .inl lam.val := by
  rcases e with e | e
  · intro h
    have hr := congrArg (fun s : TokenSort eta => match s with
      | .inl a => Frame.rank a
      | .inr _ => 0) h
    simp only [rowSort,mainSort,Frame.rank_ofOrdinal] at hr
    have hlt : Frame.rank e.val < Frame.rank lam.val := by rw [← hr]; exact lt_add_one _
    have hs := lam.property.succ_lt hlt
    rw [Order.succ_eq_add_one,hr] at hs
    exact (lt_irrefl _) hs
  · intro h
    cases h

def rowRole (s : TokenSort eta) : Option (OrdinaryRole eta) :=
  if h : ∃ e, rowSort eta e = s then some h.choose else none

@[simp] theorem rowRole_rowSort (e : OrdinaryRole eta) : rowRole eta (rowSort eta e) = some e := by
  rw [rowRole,dif_pos ⟨e,rfl⟩]
  apply congrArg some
  exact rowSort_injective eta (Exists.choose_spec (show ∃ f, rowSort eta f = rowSort eta e from ⟨e,rfl⟩))

def finiteOrdinaryRoles (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta) :
    Finset (OrdinaryRole eta) :=
  ((s :: R.filterMap (fun p => sortOf eta heta p.2)).filterMap (rowRole eta)).toFinset

theorem mem_finiteOrdinaryRoles_row (R : List (Vertex eta heta x × Vertex eta heta y))
    (s : TokenSort eta) (e : OrdinaryRole eta) (he : rowSort eta e = s) :
    e ∈ finiteOrdinaryRoles eta heta R s := by
  apply List.mem_toFinset.mpr
  apply List.mem_filterMap.mpr
  exact ⟨s,List.mem_cons_self,(he ▸ rowRole_rowSort eta e)⟩

theorem mem_finiteOrdinaryRoles_oldRow (R : List (Vertex eta heta x × Vertex eta heta y))
    (s : TokenSort eta) (e : OrdinaryRole eta) (p) (hp : p ∈ R)
    (hs : sortOf eta heta p.2 = some (rowSort eta e)) :
    e ∈ finiteOrdinaryRoles eta heta R s := by
  apply List.mem_toFinset.mpr
  apply List.mem_filterMap.mpr
  refine ⟨rowSort eta e,List.mem_cons_of_mem _ ?_,rowRole_rowSort eta e⟩
  exact List.mem_filterMap.mpr ⟨p,hp,hs⟩

def rowRequirement (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (e : OrdinaryRole eta)
    (hs : rowSort eta e=s) : FiniteRole (raw eta heta y s) := by
  subst s
  let I := SortEntries eta heta R (colSort eta e)
  let idx := (Fintype.equivFin I).symm
  exact {
    Opposite := raw eta heta y (colSort eta e)
    count := Fintype.card I
    context := fun j => (targetEntry eta heta R _ (idx j)).1
    label := fun j => (targetEntry eta heta R _ (idx j)).2
    bit := fun j => ordinary eta heta x e v (sourceEntry eta heta R hR _ (idx j))
    raw := ordinaryMatrix eta heta y e
    separated := ordinaryMatrix_column_separating eta heta y e
    direction := true
    role := roleNumber eta heta (.inl e)
    consistent := by
      intro i j hc hl
      have he : targetEntry eta heta R _ (idx i) = targetEntry eta heta R _ (idx j) := Prod.ext hc hl
      have hsrc := (sourceEntry_eq_iff_targetEntry_eq eta heta R hR _ (idx i) (idx j)).mpr he
      exact congrArg (ordinary eta heta x e v) hsrc }

def colRequirement (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (e : OrdinaryRole eta)
    (hs : colSort eta e=s) : FiniteRole (raw eta heta y s) := by
  subst s
  let I := SortEntries eta heta R (rowSort eta e)
  let idx := (Fintype.equivFin I).symm
  exact {
    Opposite := raw eta heta y (rowSort eta e)
    count := Fintype.card I
    context := fun j => (targetEntry eta heta R _ (idx j)).1
    label := fun j => (targetEntry eta heta R _ (idx j)).2
    bit := fun j => ordinary eta heta x e (sourceEntry eta heta R hR _ (idx j)) v
    raw := fun u z => ordinaryMatrix eta heta y e z u
    separated := ordinaryMatrix_row_injective eta heta y e
    direction := false
    role := roleNumber eta heta (.inl e)
    consistent := by
      intro i j hc hl
      have he : targetEntry eta heta R _ (idx i) = targetEntry eta heta R _ (idx j) := Prod.ext hc hl
      have hsrc := (sourceEntry_eq_iff_targetEntry_eq eta heta R hR _ (idx i) (idx j)).mpr he
      exact congrArg (fun w => ordinary eta heta x e w v) hsrc }

def ordinaryRequirement (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (e : OrdinaryRole eta) :
    FiniteRole (raw eta heta y s) :=
  if h : rowSort eta e=s then rowRequirement eta heta R hR s v e h
  else if h : colSort eta e=s then colRequirement eta heta R hR s v e h
  else {
    Opposite := Unit
    count := 0
    context := Fin.elim0
    label := Fin.elim0
    bit := Fin.elim0
    raw := fun _ _ => false
    separated := fun a b _ => Subsingleton.elim a b
    direction := true
    role := roleNumber eta heta (.inl e)
    consistent := fun i => Fin.elim0 i }

theorem ordinaryRequirement_role (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (e : OrdinaryRole eta) :
    (ordinaryRequirement eta heta R hR s v e).role = roleNumber eta heta (.inl e) := by
  unfold ordinaryRequirement
  split_ifs with hr hc
  · cases hr
    rfl
  · cases hc
    rfl
  · rfl

def ordinaryRequirements (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s))
    (e : finiteOrdinaryRoles eta heta R s) : FiniteRole (raw eta heta y s) :=
  ordinaryRequirement eta heta R hR s v e.val

theorem ordinaryRequirements_roles_injective (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) :
    Function.Injective (fun e => (ordinaryRequirements eta heta R hR s v e).role) := by
  intro e f hef
  apply Subtype.ext
  simp only [ordinaryRequirements,ordinaryRequirement_role] at hef
  exact Sum.inl.inj ((roleNumber eta heta).injective hef)

def OrdinaryRequestsRealized (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s)) : Prop :=
  ∀ e j, genericTable (((ordinaryRequirements eta heta R hR s v e).request w.1 j).index w.2) =
    (ordinaryRequirements eta heta R hR s v e).bit j

theorem ordinaryRequirements_row_realizes
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s))
    (hw : OrdinaryRequestsRealized eta heta R hR s v w)
    (e : OrdinaryRole eta) (hs : rowSort eta e=s)
    (i : SortEntries eta heta R (colSort eta e)) :
    ordinary eta heta x e (hs.symm ▸ v) (sourceEntry eta heta R hR _ i) =
      ordinary eta heta y e (hs.symm ▸ w) (targetEntry eta heta R _ i) := by
  subst s
  have he := mem_finiteOrdinaryRoles_row eta heta R (rowSort eta e) e rfl
  have h := hw ⟨e,he⟩
  change ∀ j, genericTable (((ordinaryRequirement eta heta R hR (rowSort eta e) v e).request w.1 j).index w.2) =
    (ordinaryRequirement eta heta R hR (rowSort eta e) v e).bit j at h
  rw [ordinaryRequirement,dif_pos rfl] at h
  have hh := h ((Fintype.equivFin (SortEntries eta heta R (colSort eta e))) i)
  simpa only [rowRequirement,FiniteRole.request,orientMatrix,if_true,Request.index,
    Equiv.symm_apply_apply,ordinary,ordinaryEdge] using hh.symm

theorem ordinaryRequirements_col_realizes
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s))
    (hw : OrdinaryRequestsRealized eta heta R hR s v w)
    (e : OrdinaryRole eta) (hs : colSort eta e=s)
    (i : SortEntries eta heta R (rowSort eta e)) :
    ordinary eta heta x e (sourceEntry eta heta R hR _ i) (hs.symm ▸ v) =
      ordinary eta heta y e (targetEntry eta heta R _ i) (hs.symm ▸ w) := by
  subst s
  have he := mem_finiteOrdinaryRoles_oldRow eta heta R (colSort eta e) e
    (R.get i.val) (List.get_mem _ i.val) i.property
  have h := hw ⟨e,he⟩
  change ∀ j, genericTable (((ordinaryRequirement eta heta R hR (colSort eta e) v e).request w.1 j).index w.2) =
    (ordinaryRequirement eta heta R hR (colSort eta e) v e).bit j at h
  rw [ordinaryRequirement,dif_neg (rowSort_ne_colSort eta e),dif_pos rfl] at h
  have hh := h ((Fintype.equivFin (SortEntries eta heta R (rowSort eta e))) i)
  simpa only [colRequirement,FiniteRole.request,orientMatrix,Bool.false_eq_true,if_false,
    Request.index,Equiv.symm_apply_apply,transpose_contextMatrix,ordinary,ordinaryEdge] using hh.symm

theorem ordinaryRequests_forward (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s))
    (hw : OrdinaryRequestsRealized eta heta R hR s v w) (e : OrdinaryRole eta)
    (p : Vertex eta heta x × Vertex eta heta y) (hp : p ∈ R) :
    edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta x e) (.inr ⟨s,v⟩) p.1 =
      edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta y e) (.inr ⟨s,w⟩) p.2 := by
  by_cases hs : rowSort eta e=s
  · subst s
    by_cases ht : sortOf eta heta p.2 = some (colSort eta e)
    · let u := (tokenFiberEquiv eta heta y (colSort eta e)).symm ⟨p.2,ht⟩
      have hu : (.inr ⟨colSort eta e,u⟩ : Vertex eta heta y) = p.2 :=
        congrArg Subtype.val ((tokenFiberEquiv eta heta y (colSort eta e)).apply_symm_apply _)
      obtain ⟨i,hi,_⟩ := targetEntry_covers eta heta R (colSort eta e) p hp u hu.symm
      have h := ordinaryRequirements_row_realizes eta heta R hR _ v w hw e rfl i
      have he : edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta x e)
          (.inr ⟨rowSort eta e,v⟩) (R.get i.val).1 =
          edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta y e)
            (.inr ⟨rowSort eta e,w⟩) (R.get i.val).2 := by
        rw [← sourceEntry_vertex eta heta R hR (colSort eta e) i,← targetEntry_vertex eta heta R (colSort eta e) i]
        simpa only [edgeAt_inr] using h
      simpa only [hi] using he
    · have hyt := (tokenAt_none_iff_sort eta heta (colSort eta e) p.2).mpr ht
      have hxt := (tokenAt_none_iff_sort eta heta (colSort eta e) p.1).mpr
        (by rw [hR.sort_eq eta heta p hp]; exact ht)
      unfold edgeAt
      rw [tokenAt_inr,tokenAt_inr,hxt,hyt]
      rfl
  · have hxt : tokenAt eta heta (rowSort eta e) (.inr ⟨s,v⟩) = none := by simp [tokenAt,Ne.symm hs]
    have hyt : tokenAt eta heta (rowSort eta e) (.inr ⟨s,w⟩) = none := by simp [tokenAt,Ne.symm hs]
    simp only [edgeAt,hxt,hyt,Option.elim_none]

theorem ordinaryRequests_backward (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s))
    (hw : OrdinaryRequestsRealized eta heta R hR s v w) (e : OrdinaryRole eta)
    (p : Vertex eta heta x × Vertex eta heta y) (hp : p ∈ R) :
    edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta x e) p.1 (.inr ⟨s,v⟩) =
      edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta y e) p.2 (.inr ⟨s,w⟩) := by
  by_cases hs : colSort eta e=s
  · subst s
    by_cases ht : sortOf eta heta p.2 = some (rowSort eta e)
    · let u := (tokenFiberEquiv eta heta y (rowSort eta e)).symm ⟨p.2,ht⟩
      have hu : (.inr ⟨rowSort eta e,u⟩ : Vertex eta heta y) = p.2 :=
        congrArg Subtype.val ((tokenFiberEquiv eta heta y (rowSort eta e)).apply_symm_apply _)
      obtain ⟨i,hi,_⟩ := targetEntry_covers eta heta R (rowSort eta e) p hp u hu.symm
      have h := ordinaryRequirements_col_realizes eta heta R hR _ v w hw e rfl i
      have he : edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta x e)
          (R.get i.val).1 (.inr ⟨colSort eta e,v⟩) =
          edgeAt eta heta (rowSort eta e) (colSort eta e) (ordinary eta heta y e)
            (R.get i.val).2 (.inr ⟨colSort eta e,w⟩) := by
        rw [← sourceEntry_vertex eta heta R hR (rowSort eta e) i,← targetEntry_vertex eta heta R (rowSort eta e) i]
        simpa only [edgeAt_inr] using h
      simpa only [hi] using he
    · have hyt := (tokenAt_none_iff_sort eta heta (rowSort eta e) p.2).mpr ht
      have hxt := (tokenAt_none_iff_sort eta heta (rowSort eta e) p.1).mpr
        (by rw [hR.sort_eq eta heta p hp]; exact ht)
      simp only [edgeAt,hxt,hyt,Option.elim_none]
  · have hxt : tokenAt eta heta (colSort eta e) (.inr ⟨s,v⟩) = none := by simp [tokenAt,Ne.symm hs]
    have hyt : tokenAt eta heta (colSort eta e) (.inr ⟨s,w⟩) = none := by simp [tokenAt,Ne.symm hs]
    unfold edgeAt
    rw [hxt,hyt]
    cases tokenAt eta heta (rowSort eta e) p.1 <;> cases tokenAt eta heta (rowSort eta e) p.2 <;> rfl

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.TokenLimitRequests
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

def branchLevel (lam : LimitIndex eta) : Option (TokenSort eta) → ℕ
  | some (.inr (mu,n)) => if mu = lam then n else 0
  | _ => 0

theorem limit_requests_realized
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (v : Token (raw eta heta x (.inl lam.val)))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inl lam.val,v⟩ : Vertex eta heta x) ≠ p.1)
    (copyBound : ℕ) :
    ∃ w : Token (raw eta heta y (.inl lam.val)), copyBound < w.2 ∧
      (∀ (n : ℕ) (i : SortEntries eta heta R (.inl lam.val)),
        Tokens.R (limitProfile eta heta y lam) n w (targetEntry eta heta R _ i) ↔
        Tokens.R (limitProfile eta heta x lam) n v (sourceEntry eta heta R hR _ i)) ∧
      (∀ n (j : SortEntries eta heta R (.inr (lam,n))),
        branch eta heta y lam n w (targetEntry eta heta R _ j) =
          branch eta heta x lam n v (sourceEntry eta heta R hR _ j)) ∧
      OrdinaryRequestsRealized eta heta R hR (.inl lam.val) v w := by
  letI : Infinite (raw eta heta y (.inl lam.val)) :=
    pool_infinite eta heta (fun b => fullSeeds eta heta b y) (Frame.rank lam.val)
  let count (n : ℕ) := Fintype.card (SortEntries eta heta R (.inr (lam,n)))
  let idx (n : ℕ) : Fin (count n) ≃ SortEntries eta heta R (.inr (lam,n)) :=
    (Fintype.equivFin _).symm
  let cx (n : ℕ) (j : Fin (count n)) := sourceEntry eta heta R hR (.inr (lam,n)) (idx n j)
  let cy (n : ℕ) (j : Fin (count n)) := targetEntry eta heta R (.inr (lam,n)) (idx n j)
  let oldX := sourceEntry eta heta R hR (.inl lam.val)
  let oldY := targetEntry eta heta R (.inl lam.val)
  have hOldR := entries_preserve_limit_R eta heta R hR lam
  have hOldBranch (n : ℕ) (i : SortEntries eta heta R (.inl lam.val))
      (j : Fin (count n)) :
      branch eta heta x lam n (oldX i) (cx n j) =
        branch eta heta y lam n (oldY i) (cy n j) :=
    entries_preserve_branch eta heta R hR lam n i (idx n j)
  have hfreshOld (i : SortEntries eta heta R (.inl lam.val)) : v ≠ oldX i := by
    intro heq
    apply hfresh (R.get i.val) (List.get_mem _ i.val)
    exact (congrArg (fun u => (.inr ⟨.inl lam.val,u⟩ : Vertex eta heta x)) heq).trans
      (sourceEntry_vertex eta heta R hR _ i)
  have hconsistent (n : ℕ) (i j : Fin (count n)) (hij : cy n i = cy n j) :
      branch eta heta x lam n v (cx n i) = branch eta heta x lam n v (cx n j) := by
    have hsrc := (sourceEntry_eq_iff_targetEntry_eq eta heta R hR (.inr (lam,n))
      (idx n i) (idx n j)).mpr hij
    exact congrArg (branch eta heta x lam n v) hsrc
  let bound := Finset.univ.sup (fun i : Fin R.length =>
    branchLevel eta lam (sortOf eta heta (R.get i).2))
  have hbound (n : ℕ) (hn : bound < n) : count n = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    constructor
    intro i
    have hi := i.property
    have hle : branchLevel eta lam (sortOf eta heta (R.get i.val).2) ≤ bound :=
      Finset.le_sup (f := fun i : Fin R.length =>
        branchLevel eta lam (sortOf eta heta (R.get i).2)) (Finset.mem_univ i.val)
    rw [hi] at hle
    simp [branchLevel] at hle
    omega
  obtain ⟨w,hw,hrelation,hbranch,hordinary⟩ := limit_finite_type_extension
    (limitProfile eta heta x lam) (limitProfile eta heta y lam)
    (limitPropagate eta heta x lam) (limitProfile_propagate eta heta x lam)
    (limitProfile_full_injective eta heta x lam) (limitProfile_column_separating eta heta y lam)
    (fun n => roleNumber eta heta (.inr (lam,n))) count cx cy oldX oldY hOldR hOldBranch
    (ordinaryRequirements eta heta R hR (.inl lam.val) v)
    (ordinaryRequirements_roles_injective eta heta R hR (.inl lam.val) v)
    v hfreshOld hconsistent bound hbound copyBound
  refine ⟨w,hw,hrelation,?_,hordinary⟩
  intro n j
  have hh := hbranch n ((idx n).symm j)
  simpa only [cy,cx,Equiv.apply_symm_apply] using hh

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.TokenInsertion
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

def oldLabelBound (R : List (Vertex eta heta x × Vertex eta heta y)) (s : TokenSort eta) : ℕ :=
  Finset.univ.sup (fun i : Fin R.length =>
    (tokenAt eta heta s (R.get i).2).elim 0 (fun v => v.2))

theorem token_fresh_of_labelBound (R : List (Vertex eta heta x × Vertex eta heta y))
    (s : TokenSort eta) (w : Token (raw eta heta y s)) (hw : oldLabelBound eta heta R s < w.2) :
    ∀ p ∈ R, (.inr ⟨s,w⟩ : Vertex eta heta y) ≠ p.2 := by
  intro p hp heq
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
  have hi : (tokenAt eta heta s (R.get i).2).elim 0 (fun v => v.2) ≤ oldLabelBound eta heta R s :=
    Finset.le_sup (f := fun i : Fin R.length =>
      (tokenAt eta heta s (R.get i).2).elim 0 (fun v => v.2)) (Finset.mem_univ i)
  rw [← heq,tokenAt_inr] at hi
  exact not_lt_of_ge hi hw

def localRelationAt (z : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (u v : Vertex eta heta z) : Bool :=
  edgeAt eta heta (.inl lam.val) (.inl lam.val)
    (fun r t => decide (Tokens.R (limitProfile eta heta z lam) n r t)) u v

def bottomEdge (z : (fsTower eta).Carrier) (u v : Vertex eta heta z) : Bool :=
  (tokenAt eta heta (zeroSort eta) u).elim false (fun r =>
    (coordinateAt eta heta v).elim false (bottom eta heta z r))

theorem localRelationAt_symm (z : (fsTower eta).Carrier) (lam : LimitIndex eta) (n : ℕ)
    (u v : Vertex eta heta z) : localRelationAt eta heta z lam n u v =
      localRelationAt eta heta z lam n v u := by
  unfold localRelationAt edgeAt
  cases tokenAt eta heta (.inl lam.val) u <;> cases tokenAt eta heta (.inl lam.val) v
    <;> simp only [Option.elim_none,Option.elim_some]
  apply decide_eq_decide.mpr
  exact ⟨(Tokens.R_equivalence _ _).symm,(Tokens.R_equivalence _ _).symm⟩

theorem bottomEdge_token_right (z : (fsTower eta).Carrier) (u : Vertex eta heta z)
    (s : TokenSort eta) (v : Token (raw eta heta z s)) :
    bottomEdge eta heta z u (.inr ⟨s,v⟩) = false := by
  unfold bottomEdge
  cases tokenAt eta heta (zeroSort eta) u <;> rfl

theorem edgeAt_self_of_ne (z : (fsTower eta).Carrier) (s t : TokenSort eta) (hst : s ≠ t)
    (f : Token (raw eta heta z s) → Token (raw eta heta z t) → Bool)
    (u : Vertex eta heta z) : edgeAt eta heta s t f u u = false := by
  unfold edgeAt
  cases hs : tokenAt eta heta s u with
  | none => rfl
  | some r =>
    have hu := (tokenAt_eq_some_iff eta heta s u r).mp hs
    have ht : tokenAt eta heta t u = none :=
      (tokenAt_none_iff_sort eta heta t u).mpr (by
        rw [hu]
        exact fun h => hst (Option.some.inj h))
    simp only [Option.elim_some,ht,Option.elim_none]

theorem token_diagonal_agrees (s : TokenSort eta) (v : Token (raw eta heta x s))
    (w : Token (raw eta heta y s)) (r : (language eta heta).Symbol) :
    diagram eta heta (bottom eta heta) x r (fun _ => .inr ⟨s,v⟩) =
      diagram eta heta (bottom eta heta) y r (fun _ => .inr ⟨s,w⟩) := by
  rcases r with r | (e | (⟨lam,n⟩ | (⟨lam,n⟩ | r)))
  · rfl
  · exact (edgeAt_self_of_ne eta heta x _ _ (rowSort_ne_colSort eta e) _ _).trans
      (edgeAt_self_of_ne eta heta y _ _ (rowSort_ne_colSort eta e) _ _).symm
  · exact (edgeAt_self_of_ne eta heta x _ _ (by intro h; cases h) _ _).trans
      (edgeAt_self_of_ne eta heta y _ _ (by intro h; cases h) _ _).symm
  · by_cases hs : s = .inl lam.val
    · subst s
      change edgeAt eta heta _ _ _ (.inr ⟨.inl lam.val,v⟩) (.inr ⟨.inl lam.val,v⟩) =
        edgeAt eta heta _ _ _ (.inr ⟨.inl lam.val,w⟩) (.inr ⟨.inl lam.val,w⟩)
      rw [edgeAt_inr,edgeAt_inr]
      simp [Tokens.R]
    · have hx : tokenAt eta heta (.inl lam.val) (.inr ⟨s,v⟩ : Vertex eta heta x) = none :=
        (tokenAt_none_iff_sort eta heta _ _).mpr (fun h => hs (Option.some.inj h))
      have hy : tokenAt eta heta (.inl lam.val) (.inr ⟨s,w⟩ : Vertex eta heta y) = none :=
        (tokenAt_none_iff_sort eta heta _ _).mpr (fun h => hs (Option.some.inj h))
      change edgeAt eta heta _ _ _ _ _ = edgeAt eta heta _ _ _ _ _
      simp only [edgeAt,hx,hy,Option.elim_none]
  · exact (bottomEdge_token_right eta heta x _ s v).trans
      (bottomEdge_token_right eta heta y _ s w).symm

theorem token_insert_compatible
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (w : Token (raw eta heta y s))
    (hfresh : ∀ p ∈ R, (.inr ⟨s,v⟩ : Vertex eta heta x) ≠ p.1)
    (hfresh' : ∀ p ∈ R, (.inr ⟨s,w⟩ : Vertex eta heta y) ≠ p.2)
    (hOrdF : ∀ e p, p ∈ R → edgeAt eta heta _ _ (ordinary eta heta x e) (.inr ⟨s,v⟩) p.1 =
      edgeAt eta heta _ _ (ordinary eta heta y e) (.inr ⟨s,w⟩) p.2)
    (hOrdB : ∀ e p, p ∈ R → edgeAt eta heta _ _ (ordinary eta heta x e) p.1 (.inr ⟨s,v⟩) =
      edgeAt eta heta _ _ (ordinary eta heta y e) p.2 (.inr ⟨s,w⟩))
    (hBrF : ∀ lam n p, p ∈ R → edgeAt eta heta _ _ (branch eta heta x lam n) (.inr ⟨s,v⟩) p.1 =
      edgeAt eta heta _ _ (branch eta heta y lam n) (.inr ⟨s,w⟩) p.2)
    (hBrB : ∀ lam n p, p ∈ R → edgeAt eta heta _ _ (branch eta heta x lam n) p.1 (.inr ⟨s,v⟩) =
      edgeAt eta heta _ _ (branch eta heta y lam n) p.2 (.inr ⟨s,w⟩))
    (hRF : ∀ lam n p, p ∈ R → localRelationAt eta heta x lam n (.inr ⟨s,v⟩) p.1 =
      localRelationAt eta heta y lam n (.inr ⟨s,w⟩) p.2)
    (hBottomF : ∀ p, p ∈ R → bottomEdge eta heta x (.inr ⟨s,v⟩) p.1 =
      bottomEdge eta heta y (.inr ⟨s,w⟩) p.2) :
    LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨s,v⟩,.inr ⟨s,w⟩)]} := by
  have hcompat : CompatibleOn (L := language eta heta) (diagram eta heta (bottom eta heta) x)
      (diagram eta heta (bottom eta heta) y) (insert (.inr ⟨s,v⟩,.inr ⟨s,w⟩) {p | p ∈ R}) := by
    apply CompatibleOn.insert_of_unary_binary hR (fun r => by cases r <;> simp [language,arity])
    · intro p hp
      exact iff_of_false (hfresh p hp) (hfresh' p hp)
    · intro r hr
      cases r with
      | inl r => rfl
      | inr r => simp [language,arity] at hr
    · intro r _
      exact token_diagonal_agrees eta heta s v w r
    · intro r hr p hp
      rcases r with r | (e | (⟨lam,n⟩ | (⟨lam,n⟩ | r)))
      · simp [language,arity] at hr
      · exact hOrdF e p hp
      · exact hBrF lam n p hp
      · exact hRF lam n p hp
      · exact hBottomF p hp
    · intro r hr p hp
      rcases r with r | (e | (⟨lam,n⟩ | (⟨lam,n⟩ | r)))
      · simp [language,arity] at hr
      · exact hOrdB e p hp
      · exact hBrB lam n p hp
      · exact (localRelationAt_symm eta heta x lam n p.1 _).trans
          ((hRF lam n p hp).trans (localRelationAt_symm eta heta y lam n p.2 _).symm)
      · exact (bottomEdge_token_right eta heta x p.1 s v).trans
          (bottomEdge_token_right eta heta y p.2 s w).symm
  apply hcompat.mono
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact Or.inr hp
  · exact Or.inl (List.mem_singleton.mp hp)

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.TokenLimitMaps
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

theorem limit_branch_forward
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (v : Token (raw eta heta x (.inl lam.val)))
    (w : Token (raw eta heta y (.inl lam.val)))
    (hbranch : ∀ n (j : SortEntries eta heta R (.inr (lam,n))),
      branch eta heta y lam n w (targetEntry eta heta R _ j) =
        branch eta heta x lam n v (sourceEntry eta heta R hR _ j))
    (mu : LimitIndex eta) (n : ℕ) (p) (hp : p ∈ R) :
    edgeAt eta heta _ _ (branch eta heta x mu n) (.inr ⟨.inl lam.val,v⟩) p.1 =
      edgeAt eta heta _ _ (branch eta heta y mu n) (.inr ⟨.inl lam.val,w⟩) p.2 := by
  by_cases hmu : mu=lam
  · subst mu
    by_cases ht : sortOf eta heta p.2 = some (.inr (lam,n))
    · let c := (tokenFiberEquiv eta heta y (.inr (lam,n))).symm ⟨p.2,ht⟩
      have hc : (.inr ⟨.inr (lam,n),c⟩ : Vertex eta heta y) = p.2 :=
        congrArg Subtype.val ((tokenFiberEquiv eta heta y (.inr (lam,n))).apply_symm_apply _)
      obtain ⟨j,hj,_⟩ := targetEntry_covers eta heta R (.inr (lam,n)) p hp c hc.symm
      have hh : edgeAt eta heta _ _ (branch eta heta x lam n) (.inr ⟨.inl lam.val,v⟩) (R.get j.val).1 =
          edgeAt eta heta _ _ (branch eta heta y lam n) (.inr ⟨.inl lam.val,w⟩) (R.get j.val).2 := by
        rw [← sourceEntry_vertex eta heta R hR (.inr (lam,n)) j,
          ← targetEntry_vertex eta heta R (.inr (lam,n)) j]
        simpa only [edgeAt_inr] using (hbranch n j).symm
      simpa only [hj] using hh
    · have hy := (tokenAt_none_iff_sort eta heta (.inr (lam,n)) p.2).mpr ht
      have hx := (tokenAt_none_iff_sort eta heta (.inr (lam,n)) p.1).mpr
        (by rw [hR.sort_eq eta heta p hp]; exact ht)
      simp only [edgeAt,tokenAt_inr,hx,hy,Option.elim_some,Option.elim_none]
  · have hs : (.inl lam.val : TokenSort eta) ≠ .inl mu.val :=
      fun h => hmu (Subtype.ext (Sum.inl.inj h).symm)
    have hx : tokenAt eta heta (.inl mu.val) (.inr ⟨.inl lam.val,v⟩) = none := by simp [tokenAt,hs]
    have hy : tokenAt eta heta (.inl mu.val) (.inr ⟨.inl lam.val,w⟩) = none := by simp [tokenAt,hs]
    simp only [edgeAt,hx,hy,Option.elim_none]

theorem limit_relation_forward
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (v : Token (raw eta heta x (.inl lam.val)))
    (w : Token (raw eta heta y (.inl lam.val)))
    (hrelation : ∀ (n : ℕ) (i : SortEntries eta heta R (.inl lam.val)),
      Tokens.R (limitProfile eta heta y lam) n w (targetEntry eta heta R _ i) ↔
        Tokens.R (limitProfile eta heta x lam) n v (sourceEntry eta heta R hR _ i))
    (mu : LimitIndex eta) (n : ℕ) (p) (hp : p ∈ R) :
    localRelationAt eta heta x mu n (.inr ⟨.inl lam.val,v⟩) p.1 =
      localRelationAt eta heta y mu n (.inr ⟨.inl lam.val,w⟩) p.2 := by
  by_cases hmu : mu=lam
  · subst mu
    by_cases ht : sortOf eta heta p.2 = some (.inl lam.val)
    · let c := (tokenFiberEquiv eta heta y (.inl lam.val)).symm ⟨p.2,ht⟩
      have hc : (.inr ⟨.inl lam.val,c⟩ : Vertex eta heta y) = p.2 :=
        congrArg Subtype.val ((tokenFiberEquiv eta heta y (.inl lam.val)).apply_symm_apply _)
      obtain ⟨j,hj,_⟩ := targetEntry_covers eta heta R (.inl lam.val) p hp c hc.symm
      have hh : localRelationAt eta heta x lam n (.inr ⟨.inl lam.val,v⟩) (R.get j.val).1 =
          localRelationAt eta heta y lam n (.inr ⟨.inl lam.val,w⟩) (R.get j.val).2 := by
        rw [← sourceEntry_vertex eta heta R hR (.inl lam.val) j,
          ← targetEntry_vertex eta heta R (.inl lam.val) j]
        unfold localRelationAt
        rw [edgeAt_inr,edgeAt_inr]
        exact decide_eq_decide.mpr (hrelation n j).symm
      simpa only [hj] using hh
    · have hy := (tokenAt_none_iff_sort eta heta (.inl lam.val) p.2).mpr ht
      have hx := (tokenAt_none_iff_sort eta heta (.inl lam.val) p.1).mpr
        (by rw [hR.sort_eq eta heta p hp]; exact ht)
      simp only [localRelationAt,edgeAt,tokenAt_inr,hx,hy,Option.elim_some,Option.elim_none]
  · have hs : (.inl lam.val : TokenSort eta) ≠ .inl mu.val :=
      fun h => hmu (Subtype.ext (Sum.inl.inj h).symm)
    have hx : tokenAt eta heta (.inl mu.val) (.inr ⟨.inl lam.val,v⟩) = none := by simp [tokenAt,hs]
    have hy : tokenAt eta heta (.inl mu.val) (.inr ⟨.inl lam.val,w⟩) = none := by simp [tokenAt,hs]
    simp only [localRelationAt,edgeAt,hx,hy,Option.elim_none]

/-- Actual one-point extension in every limit main sort, including the
entire infinite nested-equivalence diagram. -/
theorem limit_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (v : Token (raw eta heta x (.inl lam.val)))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inl lam.val,v⟩ : Vertex eta heta x) ≠ p.1) :
    ∃ w : Token (raw eta heta y (.inl lam.val)),
      LiteralCompatible eta heta (bottom eta heta) x y
        {p | p ∈ R ++ [(.inr ⟨.inl lam.val,v⟩,.inr ⟨.inl lam.val,w⟩)]} := by
  obtain ⟨w,hw,hrelation,hbranch,hordinary⟩ := limit_requests_realized eta heta R hR lam v hfresh
    (oldLabelBound eta heta R (.inl lam.val))
  refine ⟨w,token_insert_compatible eta heta R hR (.inl lam.val) v w hfresh
    (token_fresh_of_labelBound eta heta R _ w hw)
    (ordinaryRequests_forward eta heta R hR _ v w hordinary)
    (ordinaryRequests_backward eta heta R hR _ v w hordinary)
    (limit_branch_forward eta heta R hR lam v w hbranch) ?_
    (limit_relation_forward eta heta R hR lam v w hrelation) ?_⟩
  · intro mu n p hp
    have hx : tokenAt eta heta (.inr (mu,n)) (.inr ⟨.inl lam.val,v⟩) = none := by simp [tokenAt]
    have hy : tokenAt eta heta (.inr (mu,n)) (.inr ⟨.inl lam.val,w⟩) = none := by simp [tokenAt]
    unfold edgeAt
    rw [hx,hy]
    cases tokenAt eta heta (.inl mu.val) p.1 <;> cases tokenAt eta heta (.inl mu.val) p.2 <;> rfl
  · intro p hp
    have hs : (.inl lam.val : TokenSort eta) ≠ zeroSort eta := by
      intro heq
      have hr := congrArg (fun s : TokenSort eta => match s with
        | .inl a => Frame.rank a
        | .inr _ => 0) heq
      have hz : Frame.rank lam.val = 0 := by simpa only [zeroSort,mainSort,Frame.rank_ofOrdinal] using hr
      exact lam.property.ne_zero hz
    have hx : tokenAt eta heta (zeroSort eta) (.inr ⟨.inl lam.val,v⟩) = none := by simp [tokenAt,hs]
    have hy : tokenAt eta heta (zeroSort eta) (.inr ⟨.inl lam.val,w⟩) = none := by simp [tokenAt,hs]
    simp only [bottomEdge,hx,hy,Option.elim_none]

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.TokenOrdinaryMaps
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

theorem raw_nonempty (z : (fsTower eta).Carrier) (s : TokenSort eta) : Nonempty (raw eta heta z s) := by
  cases s with
  | inl a =>
    letI : Infinite (raw eta heta z (.inl a)) := pool_infinite eta heta _ _
    exact Infinite.nonempty _
  | inr c =>
    exact ⟨⟨markerBirth eta heta _ c.1.property _ 0,Nat.zero_le c.2⟩⟩

theorem ordinary_requests_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (s : TokenSort eta) (v : Token (raw eta heta x s)) (initial : List (raw eta heta y s)) (N : ℕ) :
    ∃ w : Token (raw eta heta y s), N < w.2 ∧ (∃ extra, w.1=initial++extra) ∧
      OrdinaryRequestsRealized eta heta R hR s v w := by
  letI := raw_nonempty eta heta y s
  obtain ⟨rows,k,hk,hrows,hbits⟩ := ordinary_extension (ordinaryRequirements eta heta R hR s v)
    (ordinaryRequirements_roles_injective eta heta R hR s v) initial N
  exact ⟨(rows,k),hk,hrows,hbits⟩

theorem ordinary_bottom_requests_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (v : Token (raw eta heta x (zeroSort eta))) (s : List Bool) (N : ℕ) :
    ∃ w : Token (raw eta heta y (zeroSort eta)), N < w.2 ∧
      OrdinaryRequestsRealized eta heta R hR (zeroSort eta) v w ∧
      Bottom.bitsPrefix (bottom eta heta y w) s.length=s := by
  letI := raw_nonempty eta heta y (zeroSort eta)
  obtain ⟨rows,k,hk,_,hbits,hbottom⟩ := ordinary_bottom_extension_mapped
    (fun u : raw eta heta y (zeroSort eta) => decodeAtom eta heta u.val)
    (ordinaryRequirements eta heta R hR (zeroSort eta) v)
    (ordinaryRequirements_roles_injective eta heta R hR (zeroSort eta) v) [] s N
  exact ⟨(rows,k),hk,hbits,hbottom⟩

def branchRequirement (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inr (lam,n)))) :
    FiniteRole (raw eta heta y (.inr (lam,n))) := by
  let I := SortEntries eta heta R (.inl lam.val)
  let idx := (Fintype.equivFin I).symm
  exact {
    Opposite := raw eta heta y (.inr (lam,n)) → Bool
    count := Fintype.card I
    context := fun j => activeProfiles (limitProfile eta heta y lam) (targetEntry eta heta R _ (idx j)) n
    label := fun j => localCode (targetEntry eta heta R _ (idx j)) n
    bit := fun j => branch eta heta x lam n (sourceEntry eta heta R hR _ (idx j)) v
    raw := fun c f => f c
    separated := fun f g h => funext (fun c => congrFun h c)
    direction := false
    role := roleNumber eta heta (.inr (lam,n))
    consistent := by
      intro i j hc hl
      have hRY : Tokens.R (limitProfile eta heta y lam) n
          (targetEntry eta heta R _ (idx i)) (targetEntry eta heta R _ (idx j)) := ⟨hl,hc⟩
      have hRX := (entries_preserve_limit_R eta heta R hR lam n (idx i) (idx j)).mpr hRY
      exact (R_iff_branch_neighborhood _ genericTable_generic (roleNumber eta heta (.inr (lam,n))) n _ _).mp hRX v }

def columnRequirements (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inr (lam,n)))) :
    (finiteOrdinaryRoles eta heta R (.inr (lam,n))) ⊕ Unit → FiniteRole (raw eta heta y (.inr (lam,n))) :=
  Sum.elim (ordinaryRequirements eta heta R hR (.inr (lam,n)) v)
    (fun _ => branchRequirement eta heta R hR lam n v)

theorem columnRequirements_roles_injective (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inr (lam,n)))) :
    Function.Injective (fun i => (columnRequirements eta heta R hR lam n v i).role) := by
  intro i j hij
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
  · exact congrArg Sum.inl (ordinaryRequirements_roles_injective eta heta R hR _ v hij)
  · simp only [columnRequirements,Sum.elim_inl,Sum.elim_inr,ordinaryRequirements,
      ordinaryRequirement_role,branchRequirement] at hij
    have hh := (roleNumber eta heta).injective hij
    cases hh
  · simp only [columnRequirements,Sum.elim_inl,Sum.elim_inr,ordinaryRequirements,
      ordinaryRequirement_role,branchRequirement] at hij
    have hh := (roleNumber eta heta).injective hij
    cases hh
  · rfl

theorem column_requests_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inr (lam,n)))) (N : ℕ) :
    ∃ w : Token (raw eta heta y (.inr (lam,n))), N < w.2 ∧
      OrdinaryRequestsRealized eta heta R hR (.inr (lam,n)) v w ∧
      ∀ i : SortEntries eta heta R (.inl lam.val),
        branch eta heta x lam n (sourceEntry eta heta R hR _ i) v =
          branch eta heta y lam n (targetEntry eta heta R _ i) w := by
  letI := raw_nonempty eta heta y (.inr (lam,n))
  obtain ⟨rows,k,hk,_,hbits⟩ := ordinary_extension (columnRequirements eta heta R hR lam n v)
    (columnRequirements_roles_injective eta heta R hR lam n v) [] N
  refine ⟨(rows,k),hk,(fun i j => hbits (.inl i) j),fun i => ?_⟩
  have hh := hbits (.inr ()) ((Fintype.equivFin (SortEntries eta heta R (.inl lam.val))) i)
  have heval : (fun (f : raw eta heta y (.inr (lam,n)) → Bool) u => f u) = id := rfl
  simpa only [columnRequirements,Sum.elim_inr,branchRequirement,FiniteRole.request,orientMatrix,
    Bool.false_eq_true,if_false,Request.index,Equiv.symm_apply_apply,transpose_contextMatrix,
    branch,branchEdge,heval,List.map_id] using hh.symm

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.TokenOrdinaryInsertion
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

theorem edgeAt_token_left_of_ne (z : (fsTower eta).Carrier) (s t u : TokenSort eta)
    (h : s ≠ u) (f : Token (raw eta heta z s) → Token (raw eta heta z t) → Bool)
    (v : Token (raw eta heta z u)) (w : Vertex eta heta z) :
    edgeAt eta heta s t f (.inr ⟨u,v⟩) w = false := by
  have hn : tokenAt eta heta s (.inr ⟨u,v⟩) = none := by simp [tokenAt,Ne.symm h]
  simp only [edgeAt,hn,Option.elim_none]

theorem edgeAt_token_right_of_ne (z : (fsTower eta).Carrier) (s t u : TokenSort eta)
    (h : t ≠ u) (f : Token (raw eta heta z s) → Token (raw eta heta z t) → Bool)
    (v : Token (raw eta heta z u)) (w : Vertex eta heta z) :
    edgeAt eta heta s t f w (.inr ⟨u,v⟩) = false := by
  have hn : tokenAt eta heta t (.inr ⟨u,v⟩) = none := by simp [tokenAt,Ne.symm h]
  unfold edgeAt
  rw [hn]
  cases tokenAt eta heta s w <;> rfl

theorem bottomEdge_token_left_of_ne (z : (fsTower eta).Carrier) (s : TokenSort eta)
    (h : zeroSort eta ≠ s) (v : Token (raw eta heta z s)) (w : Vertex eta heta z) :
    bottomEdge eta heta z (.inr ⟨s,v⟩) w=false := by
  have hn : tokenAt eta heta (zeroSort eta) (.inr ⟨s,v⟩) = none := by simp [tokenAt,Ne.symm h]
  simp only [bottomEdge,hn,Option.elim_none]

theorem main_ne_limit (a : MainIndex eta) (ha : ¬ Order.IsSuccLimit (Frame.rank a))
    (lam : LimitIndex eta) : (.inl lam.val : TokenSort eta) ≠ .inl a := by
  intro h
  have he : lam.val=a := Sum.inl.inj h
  exact ha (he ▸ lam.property)

theorem nonlimit_requests_insert
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (a : MainIndex eta) (ha : ¬ Order.IsSuccLimit (Frame.rank a))
    (v : Token (raw eta heta x (.inl a))) (w : Token (raw eta heta y (.inl a)))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inl a,v⟩ : Vertex eta heta x) ≠ p.1)
    (hfresh' : ∀ p ∈ R, (.inr ⟨.inl a,w⟩ : Vertex eta heta y) ≠ p.2)
    (hw : OrdinaryRequestsRealized eta heta R hR (.inl a) v w)
    (hbottom : ∀ p, p ∈ R → bottomEdge eta heta x (.inr ⟨.inl a,v⟩) p.1 =
      bottomEdge eta heta y (.inr ⟨.inl a,w⟩) p.2) :
    LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨.inl a,v⟩,.inr ⟨.inl a,w⟩)]} := by
  apply token_insert_compatible eta heta R hR (.inl a) v w hfresh hfresh'
  · exact ordinaryRequests_forward eta heta R hR _ v w hw
  · exact ordinaryRequests_backward eta heta R hR _ v w hw
  · intro lam n p _
    exact (edgeAt_token_left_of_ne eta heta x _ _ _ (main_ne_limit eta a ha lam) _ v p.1).trans
      (edgeAt_token_left_of_ne eta heta y _ _ _ (main_ne_limit eta a ha lam) _ w p.2).symm
  · intro lam n p _
    exact (edgeAt_token_right_of_ne eta heta x _ _ _ (by intro h; cases h) _ v p.1).trans
      (edgeAt_token_right_of_ne eta heta y _ _ _ (by intro h; cases h) _ w p.2).symm
  · intro lam n p _
    exact (edgeAt_token_left_of_ne eta heta x _ _ _ (main_ne_limit eta a ha lam) _ v p.1).trans
      (edgeAt_token_left_of_ne eta heta y _ _ _ (main_ne_limit eta a ha lam) _ w p.2).symm
  · exact hbottom

theorem column_branch_backward
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ)
    (v : Token (raw eta heta x (.inr (lam,n)))) (w : Token (raw eta heta y (.inr (lam,n))))
    (hbranch : ∀ i : SortEntries eta heta R (.inl lam.val),
      branch eta heta x lam n (sourceEntry eta heta R hR _ i) v =
        branch eta heta y lam n (targetEntry eta heta R _ i) w)
    (mu : LimitIndex eta) (m : ℕ) (p) (hp : p ∈ R) :
    edgeAt eta heta _ _ (branch eta heta x mu m) p.1 (.inr ⟨.inr (lam,n),v⟩) =
      edgeAt eta heta _ _ (branch eta heta y mu m) p.2 (.inr ⟨.inr (lam,n),w⟩) := by
  by_cases hmn : (mu,m)=(lam,n)
  · rcases Prod.mk.inj hmn with ⟨hmu,hm⟩
    subst mu
    subst m
    by_cases ht : sortOf eta heta p.2 = some (.inl lam.val)
    · let u := (tokenFiberEquiv eta heta y (.inl lam.val)).symm ⟨p.2,ht⟩
      have hu : (.inr ⟨.inl lam.val,u⟩ : Vertex eta heta y) = p.2 :=
        congrArg Subtype.val ((tokenFiberEquiv eta heta y (.inl lam.val)).apply_symm_apply _)
      obtain ⟨i,hi,_⟩ := targetEntry_covers eta heta R (.inl lam.val) p hp u hu.symm
      have he : edgeAt eta heta _ _ (branch eta heta x lam n)
          (R.get i.val).1 (.inr ⟨.inr (lam,n),v⟩) =
          edgeAt eta heta _ _ (branch eta heta y lam n) (R.get i.val).2 (.inr ⟨.inr (lam,n),w⟩) := by
        rw [← sourceEntry_vertex eta heta R hR (.inl lam.val) i,← targetEntry_vertex eta heta R (.inl lam.val) i]
        simpa only [edgeAt_inr] using hbranch i
      simpa only [hi] using he
    · have hy := (tokenAt_none_iff_sort eta heta (.inl lam.val) p.2).mpr ht
      have hx := (tokenAt_none_iff_sort eta heta (.inl lam.val) p.1).mpr
        (by rw [hR.sort_eq eta heta p hp]; exact ht)
      simp only [edgeAt,hx,hy,Option.elim_none]
  · exact (edgeAt_token_right_of_ne eta heta x _ _ _ (by exact fun h => hmn (Sum.inr.inj h)) _ v p.1).trans
      (edgeAt_token_right_of_ne eta heta y _ _ _ (by exact fun h => hmn (Sum.inr.inj h)) _ w p.2).symm

theorem column_requests_insert
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ)
    (v : Token (raw eta heta x (.inr (lam,n)))) (w : Token (raw eta heta y (.inr (lam,n))))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inr (lam,n),v⟩ : Vertex eta heta x) ≠ p.1)
    (hfresh' : ∀ p ∈ R, (.inr ⟨.inr (lam,n),w⟩ : Vertex eta heta y) ≠ p.2)
    (hw : OrdinaryRequestsRealized eta heta R hR (.inr (lam,n)) v w)
    (hbranch : ∀ i : SortEntries eta heta R (.inl lam.val),
      branch eta heta x lam n (sourceEntry eta heta R hR _ i) v =
        branch eta heta y lam n (targetEntry eta heta R _ i) w) :
    LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨.inr (lam,n),v⟩,.inr ⟨.inr (lam,n),w⟩)]} := by
  apply token_insert_compatible eta heta R hR _ v w hfresh hfresh'
  · exact ordinaryRequests_forward eta heta R hR _ v w hw
  · exact ordinaryRequests_backward eta heta R hR _ v w hw
  · intro mu m p _
    exact (edgeAt_token_left_of_ne eta heta x _ _ _ (by intro h; cases h) _ v p.1).trans
      (edgeAt_token_left_of_ne eta heta y _ _ _ (by intro h; cases h) _ w p.2).symm
  · exact column_branch_backward eta heta R hR lam n v w hbranch
  · intro mu m p _
    exact (edgeAt_token_left_of_ne eta heta x _ _ _ (by intro h; cases h) _ v p.1).trans
      (edgeAt_token_left_of_ne eta heta y _ _ _ (by intro h; cases h) _ w p.2).symm
  · intro p _
    exact (bottomEdge_token_left_of_ne eta heta x _ (by intro h; cases h) v p.1).trans
      (bottomEdge_token_left_of_ne eta heta y _ (by intro h; cases h) w p.2).symm

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.TokenOrdinaryExtensions
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)
variable {x y : (fsTower eta).Carrier}

theorem column_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (lam : LimitIndex eta) (n : ℕ) (v : Token (raw eta heta x (.inr (lam,n))))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inr (lam,n),v⟩ : Vertex eta heta x) ≠ p.1) :
    ∃ w : Token (raw eta heta y (.inr (lam,n))),
      LiteralCompatible eta heta (bottom eta heta) x y
        {p | p ∈ R ++ [(.inr ⟨.inr (lam,n),v⟩,.inr ⟨.inr (lam,n),w⟩)]} := by
  obtain ⟨w,hw,hOrd,hBr⟩ := column_requests_extension eta heta R hR lam n v
    (oldLabelBound eta heta R (.inr (lam,n)))
  exact ⟨w,column_requests_insert eta heta R hR lam n v w hfresh
    (token_fresh_of_labelBound eta heta R _ w hw) hOrd hBr⟩

theorem nonzero_nonlimit_main_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (a : MainIndex eta) (ha : ¬ Order.IsSuccLimit (Frame.rank a)) (hzero : Frame.rank a ≠ 0)
    (v : Token (raw eta heta x (.inl a)))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inl a,v⟩ : Vertex eta heta x) ≠ p.1) :
    ∃ w : Token (raw eta heta y (.inl a)), LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨.inl a,v⟩,.inr ⟨.inl a,w⟩)]} := by
  obtain ⟨w,hw,_,hOrd⟩ := ordinary_requests_extension eta heta R hR (.inl a) v []
    (oldLabelBound eta heta R (.inl a))
  have hz : zeroSort eta ≠ .inl a := by
    intro h
    have he := congrArg Frame.rank (Sum.inl.inj h)
    have hh : (0 : Ordinal.{0}) = Frame.rank a := by
      simpa only [zeroSort,mainSort,Frame.rank_ofOrdinal] using he
    exact hzero hh.symm
  refine ⟨w,nonlimit_requests_insert eta heta R hR a ha v w hfresh
    (token_fresh_of_labelBound eta heta R _ w hw) hOrd ?_⟩
  intro p _
  exact (bottomEdge_token_left_of_ne eta heta x _ hz v p.1).trans
    (bottomEdge_token_left_of_ne eta heta y _ hz w p.2).symm

private theorem coordinate_vertex_of_sort_none (z : (fsTower eta).Carrier)
    (u : Vertex eta heta z) (hu : sortOf eta heta u=none) :
    u = .inl ((coordinateAt eta heta u).getD 0) := by
  cases u with
  | inl n => rfl
  | inr t => cases hu

theorem bottom_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (v : Token (raw eta heta x (zeroSort eta)))
    (hfresh : ∀ p ∈ R, (.inr ⟨zeroSort eta,v⟩ : Vertex eta heta x) ≠ p.1) :
    ∃ w : Token (raw eta heta y (zeroSort eta)), LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨zeroSort eta,v⟩,.inr ⟨zeroSort eta,w⟩)]} := by
  let I := {i : Fin R.length // ∃ m : ℕ, (R.get i).2 = (.inl m : Vertex eta heta y)}
  letI : Fintype I := inferInstanceAs (Fintype {i : Fin R.length // _})
  let targetN (i : I) : ℕ := i.property.choose
  have target_spec (i : I) : (R.get i.val).2 = .inl (targetN i) := i.property.choose_spec
  let sourceN (i : I) : ℕ := (coordinateAt eta heta (R.get i.val).1).getD 0
  have source_spec (i : I) : (R.get i.val).1 = .inl (sourceN i) := by
    apply coordinate_vertex_of_sort_none eta heta x
    exact (hR.sort_eq eta heta _ (List.get_mem _ i.val)).trans (by rw [target_spec]; rfl)
  let epsilon (i : I) : Bool := bottom eta heta x v (sourceN i)
  have hconsistent (i j : I) (hij : targetN i=targetN j) : epsilon i=epsilon j := by
    have ht : (R.get i.val).2=(R.get j.val).2 := by rw [target_spec,target_spec,hij]
    have hs := (hR.1 _ (List.get_mem _ i.val) _ (List.get_mem _ j.val)).mpr ht
    exact congrArg (fun u => bottom eta heta x v ((coordinateAt eta heta u).getD 0)) hs
  let f : ℕ → Bool := fun m => if h : ∃ i : I, targetN i=m then epsilon h.choose else false
  have hf (i : I) : f (targetN i)=epsilon i := by
    dsimp [f]
    split_ifs with h
    · exact hconsistent h.choose i h.choose_spec
    · exact False.elim (h ⟨i,rfl⟩)
  let L := Finset.univ.sup targetN + 1
  let s := Bottom.bitsPrefix f L
  obtain ⟨w,hw,hOrd,hPref⟩ := ordinary_bottom_requests_extension eta heta R hR v s
    (oldLabelBound eta heta R (zeroSort eta))
  have hbits (i : I) : bottom eta heta y w (targetN i)=epsilon i := by
    have hi : targetN i < L := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
    have he := congrArg (fun t : List Bool => t[targetN i]?.getD false) hPref
    have he' : bottom eta heta y w (targetN i)=f (targetN i) := by
      simpa only [s,Bottom.bitsPrefix,List.length_ofFn,List.getElem?_ofFn,dif_pos hi,Option.getD_some] using he
    exact he'.trans (hf i)
  have hbottom (p : Vertex eta heta x × Vertex eta heta y) (hp : p ∈ R) :
      bottomEdge eta heta x (.inr ⟨zeroSort eta,v⟩) p.1 =
        bottomEdge eta heta y (.inr ⟨zeroSort eta,w⟩) p.2 := by
    cases ht : p.2 with
    | inl m =>
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hp
      let i : I := ⟨j,⟨m,by rw [hj]; exact ht⟩⟩
      have htarget : targetN i=m := Sum.inl.inj ((target_spec i).symm.trans (by rw [hj]; exact ht))
      have hsource : p.1 = .inl (sourceN i) :=
        (congrArg Prod.fst hj).symm.trans (source_spec i)
      rw [hsource]
      simp only [bottomEdge,tokenAt_inr,coordinateAt,Option.elim_some]
      have hh := hbits i
      rw [htarget] at hh
      exact hh.symm
    | inr t =>
      have hs := hR.sort_eq eta heta p hp
      have hn : coordinateAt eta heta p.1=none := by
        cases hx : p.1 with
        | inl m => simp only [hx,ht,sortOf] at hs; cases hs
        | inr u => rfl
      simp only [bottomEdge,tokenAt_inr,Option.elim_some]
      rw [hn]
      rfl
  have hnot : ¬ Order.IsSuccLimit (Frame.rank (Frame.ofOrdinal eta 0 zero_le)) := by
    intro h
    have hp := h.pos
    exact (lt_irrefl (0 : Ordinal.{0})) (by simpa only [Frame.rank_ofOrdinal] using hp)
  exact ⟨w,nonlimit_requests_insert eta heta R hR _ hnot v w hfresh
    (token_fresh_of_labelBound eta heta R _ w hw) hOrd hbottom⟩

theorem nonlimit_main_extension
    (R : List (Vertex eta heta x × Vertex eta heta y))
    (hR : LiteralCompatible eta heta (bottom eta heta) x y {p | p ∈ R})
    (a : MainIndex eta) (ha : ¬ Order.IsSuccLimit (Frame.rank a))
    (v : Token (raw eta heta x (.inl a)))
    (hfresh : ∀ p ∈ R, (.inr ⟨.inl a,v⟩ : Vertex eta heta x) ≠ p.1) :
    ∃ w : Token (raw eta heta y (.inl a)), LiteralCompatible eta heta (bottom eta heta) x y
      {p | p ∈ R ++ [(.inr ⟨.inl a,v⟩,.inr ⟨.inl a,w⟩)]} := by
  by_cases hz : Frame.rank a=0
  · have he : a=Frame.ofOrdinal eta 0 zero_le := by
      apply Ordinal.ToType.mk.symm.injective
      apply Subtype.ext
      change Frame.rank a=Frame.rank (Frame.ofOrdinal eta 0 zero_le)
      simpa only [Frame.rank_ofOrdinal] using hz
    subst a
    exact bottom_extension eta heta R hR v hfresh
  · exact nonzero_nonlimit_main_extension eta heta R hR a ha hz v hfresh

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.CosetConstructionCommonIsotype
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction.TokenModel
open PartialIso Tokens RawObjects GenericTables

variable (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1)

/-- Every finite atomic partial isomorphism between two actual outputs
extends over any prescribed new point. -/
theorem literal_forth (x y : (fsTower eta).Carrier) :
    LiteralForth (L := language eta heta) (diagram eta heta (bottom eta heta) x)
      (diagram eta heta (bottom eta heta) y) := by
  apply literalForth_of_fresh
  intro R hR u hfresh
  cases u with
  | inl n =>
    obtain ⟨m,hm⟩ := coordinate_extension eta heta R hR n hfresh
    exact ⟨.inl m,hm⟩
  | inr u =>
    rcases u with ⟨s,v⟩
    rcases s with a | ⟨lam,n⟩
    · by_cases ha : Order.IsSuccLimit (Frame.rank a)
      · obtain ⟨w,hw⟩ := limit_extension eta heta R hR ⟨a,ha⟩ v hfresh
        exact ⟨.inr ⟨.inl a,w⟩,hw⟩
      · obtain ⟨w,hw⟩ := nonlimit_main_extension eta heta R hR a ha v hfresh
        exact ⟨.inr ⟨.inl a,w⟩,hw⟩
    · obtain ⟨w,hw⟩ := column_extension eta heta R hR lam n v hfresh
      exact ⟨.inr ⟨.inr (lam,n),w⟩,hw⟩

theorem language_arity_positive (s : (language eta heta).Symbol) :
    0 < (language eta heta).arity s := by
  cases s <;> simp [language,arity]

theorem nativeModel_forth (x y : (fsTower eta).Carrier) :
    ForthExtension (nativeModel eta heta x) (nativeModel eta heta y) :=
  forth_modelWithEnumeration_of_literal eta heta (bottom eta heta) x y
    (nativeEnumeration eta heta x) (nativeEnumeration eta heta y) (literal_forth eta heta x y)

theorem nativeModel_isomorphic (x y : (fsTower eta).Carrier) :
    Isomorphic (nativeModel eta heta x) (nativeModel eta heta y) :=
  isomorphic_of_extensions
    (AtomicCompatible.empty_of_positive_arity _ _ (language_arity_positive eta heta))
    (nativeModel_forth eta heta x y) (nativeModel_forth eta heta y x)

theorem literal_isomorphic (x y : (fsTower eta).Carrier) :
    LiteralIsomorphic eta heta (bottom eta heta) x y :=
  (isomorphic_modelWithEnumeration_iff eta heta (bottom eta heta) x y
    (nativeEnumeration eta heta x) (nativeEnumeration eta heta y)).mp
      (nativeModel_isomorphic eta heta x y)

/-- The least-branch back-and-forth choice into any selected base output. -/
def chosenNativeIsomorphism (base : (fsTower eta).Carrier) :
    (fsTower eta).Carrier → PermutationGroup :=
  familyIsomorphism (nativeModel eta heta) (language_arity_positive eta heta)
    (nativeModel_forth eta heta) base

theorem chosenNativeIsomorphism_carries (base x : (fsTower eta).Carrier) :
    Carries (nativeModel eta heta x) (nativeModel eta heta base)
      (chosenNativeIsomorphism eta heta base x) :=
  familyIsomorphism_preserves (nativeModel eta heta) (language_arity_positive eta heta)
    (nativeModel_forth eta heta) base x

theorem measurable_chosenNativeIsomorphism (base : (fsTower eta).Carrier) :
    Measurable (chosenNativeIsomorphism eta heta base) :=
  measurable_familyIsomorphism (nativeModel eta heta) (language_arity_positive eta heta)
    (nativeModel_forth eta heta) base (measurable_nativeModel eta heta)

end FSCofinality.CosetConstruction.TokenModel

end
end

-- Original module: FSCofinalityProof.BorelClosedChoice
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology TopologicalSpace Metric

namespace FSCofinality.ClosedChoice

def radius (n : ℕ) : ℝ := (1/2)^n

theorem radius_pos (n : ℕ) : 0 < radius n := pow_pos (by norm_num) _

theorem radius_succ (n : ℕ) : radius (n+1) = radius n / 2 := by
  simp [radius,pow_succ,div_eq_mul_inv]

section MetricChoice
variable {X : Type} [MetricSpace X] [SeparableSpace X] [Nonempty X]

def Near (S : Set X) (n k : ℕ) : Prop :=
  (S ∩ ball (denseSeq X k) (radius n / 4)).Nonempty

theorem exists_initial (S : Set X) (hne : S.Nonempty) : ∃ k, Near S 0 k := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨k,hk⟩ := (denseRange_denseSeq X).exists_dist_lt x
    (ε := radius 0 / 4) (by norm_num [radius])
  exact ⟨k,x,hx,hk⟩

theorem exists_next (S : Set X) (n k : ℕ) (hk : Near S n k) :
    ∃ j, Near S (n+1) j ∧ dist (denseSeq X j) (denseSeq X k) < radius n := by
  obtain ⟨x,hx,hxk⟩ := hk
  obtain ⟨j,hj⟩ := (denseRange_denseSeq X).exists_dist_lt x
    (div_pos (radius_pos (n+1)) (by norm_num : (0:ℝ)<4))
  refine ⟨j,⟨x,hx,hj⟩,?_⟩
  have htri := dist_triangle (denseSeq X j) x (denseSeq X k)
  have hxk' : dist x (denseSeq X k) < radius n / 4 := hxk
  rw [dist_comm] at hj
  rw [radius_succ] at hj
  have hp := radius_pos n
  linarith

def Next (S : Set X) (n k j : ℕ) : Prop :=
  (Near S (n+1) j ∧ dist (denseSeq X j) (denseSeq X k) < radius n) ∨ ¬ Near S n k

theorem exists_next_total (S : Set X) (n k : ℕ) : ∃ j, Next S n k j := by
  by_cases hk : Near S n k
  · obtain ⟨j,hj⟩ := exists_next S n k hk
    exact ⟨j,Or.inl hj⟩
  · exact ⟨0,Or.inr hk⟩

def nextIndex (S : Set X) (n k : ℕ) : ℕ := Nat.find (exists_next_total S n k)

theorem nextIndex_spec (S : Set X) (n k : ℕ) (hk : Near S n k) :
    Near S (n+1) (nextIndex S n k) ∧
      dist (denseSeq X (nextIndex S n k)) (denseSeq X k) < radius n :=
  (Nat.find_spec (exists_next_total S n k)).resolve_right (not_not.mpr hk)

def index (S : Set X) (hne : S.Nonempty) : ℕ → ℕ
  | 0 => Nat.find (exists_initial S hne)
  | n+1 => nextIndex S n (index S hne n)

theorem index_near (S : Set X) (hne : S.Nonempty) (n : ℕ) : Near S n (index S hne n) := by
  induction n with
  | zero => exact Nat.find_spec (exists_initial S hne)
  | succ n ih => exact (nextIndex_spec S n _ ih).1

theorem index_step (S : Set X) (hne : S.Nonempty) (n : ℕ) :
    dist (denseSeq X (index S hne (n+1))) (denseSeq X (index S hne n)) < radius n :=
  (nextIndex_spec S n _ (index_near S hne n)).2

theorem index_congr {S T : Set X} (hST : S=T) (hS : S.Nonempty) (hT : T.Nonempty) :
    index S hS = index T hT := by subst T; rfl

end MetricChoice

section Measurability
variable {P X : Type} [MeasurableSpace P] [MetricSpace X] [SeparableSpace X] [Nonempty X]
    (S : P → Set X)
    (hHit : ∀ U : Set X, IsOpen U → MeasurableSet {p | (S p ∩ U).Nonempty})

include hHit

theorem measurableSet_near (n k : ℕ) : MeasurableSet {p | Near (S p) n k} :=
  hHit _ isOpen_ball

theorem measurableSet_variable_near (n : ℕ) :
    MeasurableSet {p : P × ℕ | Near (S p.1) n p.2} := by
  have hf : Measurable (fun p : P × ℕ => decide (Near (S p.1) n p.2)) := by
    apply measurable_from_prod_countable_left
    intro k
    exact Measurable.ite (measurableSet_near S hHit n k) measurable_const measurable_const
  have hm := (measurableSet_singleton true).preimage hf
  change MeasurableSet {p : P × ℕ | decide (Near (S p.1) n p.2) = true} at hm
  simpa only [decide_eq_true_eq] using hm

theorem measurable_nextIndex (n : ℕ) :
    Measurable (fun p : P × ℕ => nextIndex (S p.1) n p.2) := by
  apply measurable_find (fun p : P × ℕ => exists_next_total (S p.1) n p.2)
  intro j
  have hj : MeasurableSet {p : P × ℕ | Near (S p.1) (n+1) j} :=
    (measurableSet_near S hHit (n+1) j).preimage measurable_fst
  have hd : MeasurableSet {p : P × ℕ |
      dist (denseSeq X j) (denseSeq X p.2) < radius n} :=
    measurableSet_lt ((measurable_of_countable
      (fun k => dist (denseSeq X j) (denseSeq X k))).comp measurable_snd) measurable_const
  exact (hj.inter hd).union (measurableSet_variable_near S hHit n).compl

theorem measurable_index (hne : ∀ p, (S p).Nonempty) (n : ℕ) :
    Measurable (fun p => index (S p) (hne p) n) := by
  induction n with
  | zero =>
    exact measurable_find (fun p => exists_initial (S p) (hne p))
      (measurableSet_near S hHit 0)
  | succ n ih => exact (measurable_nextIndex S hHit n).comp (measurable_id.prodMk ih)

end Measurability

/-- Closed-set selection using only Borel open-set hit tests. The selector
is canonical as a function of the closed set, so equal sets give equal
selected points. -/
theorem exists_measurable_closed_selector {P X : Type}
    [MeasurableSpace P] [MetricSpace X] [CompleteSpace X]
    [SeparableSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (S : P → Set X) (hne : ∀ p, (S p).Nonempty) (hclosed : ∀ p, IsClosed (S p))
    (hHit : ∀ U : Set X, IsOpen U → MeasurableSet {p | (S p ∩ U).Nonempty}) :
    ∃ f : P → X, Measurable f ∧ (∀ p, f p ∈ S p) ∧
      ∀ p q, S p = S q → f p = f q := by
  have hc (p : P) : CauchySeq (fun n => denseSeq X (index (S p) (hne p) n)) := by
    apply cauchySeq_of_le_geometric (1/2) 1 (by norm_num)
    intro n
    simpa only [one_mul,radius,dist_comm] using (index_step (S p) (hne p) n).le
  choose f hf using fun p => cauchySeq_tendsto_of_complete (hc p)
  refine ⟨f,?_,?_,?_⟩
  · apply measurable_of_tendsto_metrizable _ (tendsto_pi_nhds.mpr hf)
    intro n
    exact (measurable_of_countable (denseSeq X)).comp (measurable_index S hHit hne n)
  · intro p
    have hy (n : ℕ) : ∃ y : X, y ∈ S p ∧
        dist y (denseSeq X (index (S p) (hne p) n)) < radius n / 4 :=
      index_near (S p) (hne p) n
    choose y hyS hyDist using hy
    have hr : Tendsto (fun n => radius n / 4) atTop (𝓝 0) := by
      have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)
      simpa only [radius,zero_div] using hh.div_const 4
    have hd : Tendsto (fun n => dist (denseSeq X (index (S p) (hne p) n)) (y n))
        atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [dist_comm] using (hyDist n).le) hr
    exact (hclosed p).mem_of_tendsto ((hf p).congr_dist hd) (Eventually.of_forall hyS)
  · intro p q hpq
    have heq : (fun n => denseSeq X (index (S p) (hne p) n)) =
        (fun n => denseSeq X (index (S q) (hne q) n)) := by
      rw [index_congr hpq (hne p) (hne q)]
    have ht := hf q
    rw [← heq] at ht
    exact tendsto_nhds_unique (hf p) ht

end FSCofinality.ClosedChoice

end
end

-- Original module: FSCofinalityProof.PolishHomImage
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology TopologicalSpace

namespace FSCofinality

/-- The image of a continuous homomorphism of Polish groups is Borel.
The proof selects a canonical point in each closed kernel coset and applies
Lusin--Souslin to the resulting Borel transversal. -/
theorem measurableSet_range_continuousHom {G H : Type}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [PolishSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (f : G →* H) (hf : Continuous f) : MeasurableSet (range f) := by
  letI := upgradeIsCompletelyMetrizable G
  let S : G → Set G := fun x => {y | f y = f x}
  have hne (x : G) : (S x).Nonempty := ⟨x,rfl⟩
  have hclosed (x : G) : IsClosed (S x) := isClosed_eq hf continuous_const
  have hHit (U : Set G) (hU : IsOpen U) : MeasurableSet {x | (S x ∩ U).Nonempty} := by
    have heq : {x | (S x ∩ U).Nonempty} = ⋃ n : f.ker, {x | x*n.val ∈ U} := by
      ext x
      simp only [mem_setOf_eq,mem_iUnion]
      constructor
      · rintro ⟨y,hy,hyU⟩
        have hfy : f y = f x := hy
        have hker : x⁻¹*y ∈ f.ker := by
          change f (x⁻¹*y) = 1
          rw [map_mul,map_inv,hfy,inv_mul_cancel]
        exact ⟨⟨x⁻¹*y,hker⟩,by simpa only [mul_inv_cancel_left] using hyU⟩
      · rintro ⟨n,hn⟩
        refine ⟨x*n.val,?_,hn⟩
        change f (x*n.val) = f x
        rw [map_mul,show f n.val = 1 from n.property,mul_one]
    rw [heq]
    exact (isOpen_iUnion (fun n : f.ker => hU.preimage
      (continuous_id.mul continuous_const))).measurableSet
  obtain ⟨s,hs,hmem,hconstant⟩ := ClosedChoice.exists_measurable_closed_selector S hne hclosed hHit
  have hvalue (x : G) : f (s x) = f x := hmem x
  have hequal (x y : G) (hxy : f x = f y) : S x = S y := by
    ext z
    change (f z = f x) ↔ f z = f y
    rw [hxy]
  let R : Set G := {x | s x = x}
  have hR : MeasurableSet R := measurableSet_eq_fun hs measurable_id
  have hinj : R.InjOn f := by
    intro x hx y hy hxy
    exact hx.symm.trans ((hconstant x y (hequal x y hxy)).trans hy)
  have himage : f '' R = range f := by
    apply Subset.antisymm
    · rintro _ ⟨x,_,rfl⟩
      exact mem_range_self x
    · rintro _ ⟨x,rfl⟩
      refine ⟨s x,?_,hvalue x⟩
      exact hconstant (s x) x (hequal (s x) x (hvalue x))
  rw [← himage]
  exact hR.image_of_measurable_injOn hf.measurable hinj

end FSCofinality

end
end

-- Original module: FSCofinalityProof.CosetConstructionCosets
section


set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set

namespace FSCofinality.CosetConstruction

/-- Restriction to the distinguished coordinates realizes each countable tower
level as cosets of a Borel image of a closed permutation group. -/
theorem coset_cofinality (eta : Ordinal.{0}) (heta : eta < Ordinal.omega 1) :
    ∃ G : Subgroup PermutationGroup,
      IsClosed (G : Set PermutationGroup) ∧
      ∃ π : G →* PermutationGroup,
        Continuous π ∧ Function.Injective π ∧
        MeasurableSet (π.range : Set PermutationGroup) ∧
        (fsTower eta).Reduces (imageCosetRelation π) := by
  obtain ⟨base⟩ := (regular_fsTower eta).nonempty
  let B := TokenModel.nativeModel eta heta base
  let Q := TokenModel.nativeQ eta heta
  let eQ := TokenModel.coordinateEquiv eta heta
  have hQ : ∀ p : automorphismGroup B, ∀ n, n ∈ Q ↔ p.val.toFun n ∈ Q := by
    intro p n
    exact TokenModel.nativeCarries_preservesQ eta heta base base p.val p.property n
  let π := DistinguishedRestriction.hom B Q eQ hQ
  have hfaithful : ∀ p q : automorphismGroup B,
      (∀ n ∈ Q, p.val.toFun n = q.val.toFun n) → p = q := by
    intro p q hpq
    let t : automorphismGroup B := q⁻¹ * p
    have hfix : ∀ n ∈ Q, t.val.toFun n = n := by
      intro n hn
      change q.val.symm.toFun (p.val.toFun n) = n
      rw [hpq n hn]
      exact q.val.left_inv n
    have htval := TokenModel.native_qFixed_rigid eta heta base t.val t.property hfix
    have ht : t = 1 := Subtype.ext htval
    exact (inv_mul_eq_one.mp ht).symm
  have hinj : Function.Injective π :=
    DistinguishedRestriction.hom_injective B Q eQ hQ hfaithful
  have hcont : Continuous π := DistinguishedRestriction.continuous_hom B Q eQ hQ
  have hclosed := isClosed_automorphismGroup B
  letI : PolishSpace (automorphismGroup B) := hclosed.polishSpace
  have hrange : MeasurableSet (π.range : Set PermutationGroup) := by
    change MeasurableSet (range π)
    exact measurableSet_range_continuousHom π hcont
  refine ⟨automorphismGroup B,hclosed,π,hcont,hinj,hrange,?_⟩
  let u := TokenModel.chosenNativeIsomorphism eta heta base
  have hu : ∀ x, Carries (TokenModel.nativeModel eta heta x) B (u x) :=
    TokenModel.chosenNativeIsomorphism_carries eta heta base
  have huQ : ∀ x n, n ∈ Q ↔ (u x).toFun n ∈ Q := by
    intro x n
    exact TokenModel.nativeCarries_preservesQ eta heta x base (u x) (hu x) n
  obtain ⟨f,hf,hred⟩ := DistinguishedRestriction.qFixed_reduces_coset
    (TokenModel.nativeModel eta heta) B Q eQ hQ u hu huQ
      (TokenModel.measurable_chosenNativeIsomorphism eta heta base)
  refine ⟨f,hf,?_⟩
  intro x y
  exact (TokenModel.native_qFixed_iff eta heta x y).trans (hred x y)

end FSCofinality.CosetConstruction

end
end

-- Original module: Solutions.CosetCofinality
section


set_option autoImplicit false

namespace FSCofinality



end FSCofinality

end

open FSCofinality in
theorem solution
    (a : Ordinal.{0}) (ha_countable : a < Ordinal.omega 1) :
    ∃ G : Subgroup FSCofinality.PermutationGroup,
      IsClosed (G : Set FSCofinality.PermutationGroup) ∧
      ∃ π : G →* FSCofinality.PermutationGroup,
        Continuous π ∧ Function.Injective π ∧
        MeasurableSet (π.range : Set FSCofinality.PermutationGroup) ∧
        (FSCofinality.fsTower a).Reduces (FSCofinality.imageCosetRelation π) :=
  CosetConstruction.coset_cofinality a ha_countable
