-- Prove2me | solution 1 for NoBorelUpperBoundFSigma.lemma2_category_transfer
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-11-02T06:13:51.541718+00:00
-- url     : https://prove2.me/submissions/05ba5476-31cf-4a9b-a570-ecc38e2f2d38

import Definitions.Def_NoBorelUpperBoundTransfer20261101
import Definitions.Def_NoUniversalFSigma261031052
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.MetricSpace.Polish

set_option autoImplicit false

-- BEGIN WHOLE MODULE NoBorelUpperBound.CategoryProduct

noncomputable section
open Set Filter TopologicalSpace Topology

namespace NoBorelUpperBoundFSigma
universe u v

section Product
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def sectionHit (U : Set (X × Y)) (V : Set Y) : Set X :=
  Prod.fst '' (U ∩ (univ ×ˢ V))

theorem isOpen_sectionHit {U : Set (X × Y)} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) : IsOpen (sectionHit U V) :=
  isOpenMap_fst _ (hU.inter (isOpen_univ.prod hV))

theorem dense_sectionHit {U : Set (X × Y)} {V : Set Y}
    (hU : Dense U) (hV : IsOpen V) (hne : V.Nonempty) : Dense (sectionHit U V) := by
  apply dense_iff_inter_open.mpr
  intro W hW hWne
  obtain ⟨p, hpWV, hpU⟩ := hU.inter_open_nonempty (W ×ˢ V) (hW.prod hV) (hWne.prod hne)
  exact ⟨p.1, hpWV.1, ⟨p, ⟨hpU, ⟨mem_univ _, hpWV.2⟩⟩, rfl⟩⟩

/-- The residual-section half of the Kuratowski--Ulam theorem. -/
theorem residual_sections [SecondCountableTopology Y] {s : Set (X × Y)}
    (hs : s ∈ residual (X × Y)) :
    ∀ᶠ x in residual X, {y | (x, y) ∈ s} ∈ residual Y := by
  classical
  obtain ⟨S, hSo, hSd, hSc, hSs⟩ := mem_residual_iff.mp hs
  letI : Countable S := hSc.to_subtype
  have hgood : ∀ᶠ x in residual X, ∀ U : S, ∀ V : countableBasis Y,
      x ∈ sectionHit U.val V.val := by
    apply eventually_countable_forall.mpr
    intro U
    apply eventually_countable_forall.mpr
    intro V
    exact residual_of_dense_open
      (isOpen_sectionHit (hSo U U.property) (isOpen_of_mem_countableBasis V.property))
      (dense_sectionHit (hSd U U.property) (isOpen_of_mem_countableBasis V.property)
        (nonempty_of_mem_countableBasis V.property))
  filter_upwards [hgood] with x hx
  have hsection (U : S) : {y | (x, y) ∈ U.val} ∈ residual Y := by
    apply residual_of_dense_open
    · exact (hSo U U.property).preimage (continuous_const.prodMk continuous_id)
    · apply (isBasis_countableBasis Y).dense_iff.mpr
      intro V hV _
      obtain ⟨⟨a,b⟩, ⟨hpU, hpV⟩, hpx⟩ := hx U ⟨V, hV⟩
      dsimp at hpx
      subst a
      exact ⟨b, hpV.2, hpU⟩
  have htotal : (⋂ U : S, {y | (x, y) ∈ U.val}) ∈ residual Y :=
    countable_iInter_mem.mpr hsection
  apply mem_of_superset htotal
  intro y hy
  apply hSs
  intro U hU
  exact mem_iInter.mp hy ⟨U, hU⟩

/-- A saturated residual set in a nonempty Baire product reflects to its
first factor. No regularity assumption on the saturated set is required. -/
theorem residual_of_preimage_fst [SecondCountableTopology Y] [BaireSpace Y] [Nonempty Y]
    {s : Set X} (hs : Prod.fst ⁻¹' s ∈ residual (X × Y)) : s ∈ residual X := by
  filter_upwards [residual_sections hs] with x hx
  obtain ⟨y, hy⟩ := (dense_of_mem_residual hx).nonempty
  exact hy

/-- The Kuratowski--Ulam equivalence for sets with the property of Baire. -/
theorem residual_product_iff [SecondCountableTopology Y] [BaireSpace X] [BaireSpace Y]
    {s : Set (X × Y)} (hs : BaireMeasurableSet s) :
    s ∈ residual (X × Y) ↔ ∀ᶠ x in residual X, {y | (x,y) ∈ s} ∈ residual Y := by
  refine ⟨residual_sections, ?_⟩
  intro hsec
  obtain ⟨U, hU, heq⟩ := hs.residualEq_isOpen
  have heqp : ∀ᶠ p in residual (X × Y), p ∈ s ↔ p ∈ U := eventuallyEq_set.mp heq
  have hUsec : ∀ᶠ x in residual X, {y | (x,y) ∈ U} ∈ residual Y := by
    filter_upwards [hsec, residual_sections heqp] with x hx hxEq
    filter_upwards [hx, hxEq] with y hy hEq
    exact hEq.mp hy
  have hUd : Dense U := by
    apply dense_iff_inter_open.mpr
    intro W hW hWne
    obtain ⟨⟨x,y⟩, hxy⟩ := hWne
    obtain ⟨A,B,hA,hB,hx,hy,hAB⟩ := isOpen_prod_iff.mp hW x y hxy
    obtain ⟨a,ha,haSec⟩ := (dense_of_mem_residual hUsec).inter_open_nonempty A hA ⟨x,hx⟩
    obtain ⟨b,hb,hab⟩ := (dense_of_mem_residual haSec).inter_open_nonempty B hB ⟨y,hy⟩
    exact ⟨(a,b), hAB ⟨ha,hb⟩, hab⟩
  filter_upwards [residual_of_dense_open hU hUd, heqp] with p hp hEq
  exact hEq.mpr hp

end Product
end NoBorelUpperBoundFSigma
end
-- END WHOLE MODULE NoBorelUpperBound.CategoryProduct

-- BEGIN WHOLE MODULE NoBorelUpperBound.CategoryTransfer

noncomputable section
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w z

section Collapse
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Y : Type v} (f : G → Y) (F : Setoid Y)

/-- Translation by `t` generically preserves the target equivalence class. -/
def GenericallyCollapses (t : G) : Prop :=
  ∀ᶠ g in residual G, F.r (f g) (f (g * t))

/-- The translations generically collapsed by any map form a subgroup. -/
def collapseSubgroup : Subgroup G where
  carrier := {t | GenericallyCollapses f F t}
  one_mem' := by
    change ∀ᶠ g in residual G, F.r (f g) (f (g*1))
    apply Eventually.of_forall
    intro g
    simpa only [mul_one] using F.refl (f g)
  mul_mem' := by
    intro a b ha hb
    change ∀ᶠ g in residual G, F.r (f g) (f (g*a)) at ha
    change ∀ᶠ g in residual G, F.r (f g) (f (g*b)) at hb
    change ∀ᶠ g in residual G, F.r (f g) (f (g*(a*b)))
    have hb' := tendsto_residual_of_isOpenMap (Homeomorph.mulRight a).continuous
      (Homeomorph.mulRight a).isOpenMap hb
    filter_upwards [ha, hb'] with g hga hgb
    simpa only [mul_assoc] using (F.trans hga hgb : F.r (f g) (f ((g*a)*b)))
  inv_mem' := by
    intro a ha
    change ∀ᶠ g in residual G, F.r (f g) (f (g*a)) at ha
    change ∀ᶠ g in residual G, F.r (f g) (f (g*a⁻¹))
    have ha' := tendsto_residual_of_isOpenMap (Homeomorph.mulRight a⁻¹).continuous
      (Homeomorph.mulRight a⁻¹).isOpenMap ha
    filter_upwards [ha'] with g hg
    apply F.symm
    change F.r (f (g*a⁻¹)) (f ((g*a⁻¹)*a)) at hg
    simpa only [inv_mul_cancel_right] using hg

@[simp] theorem mem_collapseSubgroup (t : G) :
    t ∈ collapseSubgroup f F ↔ GenericallyCollapses f F t := Iff.rfl

/-- A generic homomorphism test collapses every fixed image element. -/
theorem generic_homomorphism_fixed
    {A : Type w} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [SecondCountableTopology A] [BaireSpace A]
    (h : A →* G)
    (hgen : ∀ᶠ p : G × A in residual (G × A), F.r (f p.1) (f (p.1 * h p.2)))
    (a₀ : A) : GenericallyCollapses f F (h a₀) := by
  let e : G × A ≃ₜ G × A :=
    (Homeomorph.mulRight (h a₀)).prodCongr (Homeomorph.mulLeft a₀⁻¹)
  have hgen' := tendsto_residual_of_isOpenMap e.continuous e.isOpenMap hgen
  have hs : Prod.fst ⁻¹' {g | F.r (f g) (f (g * h a₀))} ∈ residual (G × A) := by
    filter_upwards [hgen,hgen'] with p hp hp'
    change F.r (f (p.1 * h a₀)) (f ((p.1 * h a₀) * h (a₀⁻¹*p.2))) at hp'
    have he : (p.1 * h a₀) * h (a₀⁻¹*p.2) = p.1 * h p.2 := by
      rw [map_mul,map_inv]
      group
    rw [he] at hp'
    exact F.trans hp (F.symm hp')
  exact residual_of_preimage_fst hs

/-- Simultaneous generic tests collapse the algebraic subgroup generated by
all homomorphism images. -/
theorem generated_subgroup_collapses
    {P : Type w} {A : ℕ → Type z} [∀ n, Group (A n)]
    [∀ n, TopologicalSpace (A n)] [∀ n, IsTopologicalGroup (A n)]
    [∀ n, SecondCountableTopology (A n)] [∀ n, BaireSpace (A n)]
    (h : ∀ n, P → (A n →* G)) (p : P)
    (hgen : ∀ n, ∀ᶠ ga : G × A n in residual (G × A n),
      F.r (f ga.1) (f (ga.1 * h n p ga.2))) :
    GeneratedSubgroup h p ≤ collapseSubgroup f F := by
  change Subgroup.closure _ ≤ _
  apply (Subgroup.closure_le _).2
  intro t ht
  obtain ⟨n, ht⟩ := mem_iUnion.mp ht
  obtain ⟨a, rfl⟩ := ht
  exact generic_homomorphism_fixed f F (h n p) (hgen n) a

/-- The generator tests and a generic separation test cannot coexist when
the designated element is in the algebraically generated subgroup. -/
theorem generic_tests_exclude_membership [BaireSpace G]
    {P : Type w} {A : ℕ → Type z} [∀ n, Group (A n)]
    [∀ n, TopologicalSpace (A n)] [∀ n, IsTopologicalGroup (A n)]
    [∀ n, SecondCountableTopology (A n)] [∀ n, BaireSpace (A n)]
    (h : ∀ n, P → (A n →* G)) (p : P) (t : G)
    (hgen : ∀ n, ∀ᶠ ga : G × A n in residual (G × A n),
      F.r (f ga.1) (f (ga.1 * h n p ga.2)))
    (hsep : ∀ᶠ g in residual G, ¬ F.r (f g) (f (g*t))) :
    t ∉ GeneratedSubgroup h p := by
  intro ht
  have hcollapse := generated_subgroup_collapses f F h p hgen ht
  have hfalse : ∀ᶠ g in residual G, False := by
    filter_upwards [hcollapse,hsep] with g hc hs
    exact hs hc
  obtain ⟨g,hg⟩ := (dense_of_mem_residual hfalse).nonempty
  exact hg

end Collapse

section Agreement
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type w} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    {Y : Type v}

/-- Triangular change of variables for right multiplication by a varying
continuous homomorphism value. -/
def homomorphismRightShear (h : A →* G) (hh : Continuous h) : G × A ≃ₜ G × A where
  toFun p := (p.1 * h p.2, p.2)
  invFun p := (p.1 * (h p.2)⁻¹, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := (continuous_fst.mul (hh.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.mul (hh.comp continuous_snd).inv).prodMk continuous_snd

theorem isOpenMap_mul_homomorphism (h : A →* G) (hh : Continuous h) :
    IsOpenMap (fun p : G × A => p.1 * h p.2) :=
  isOpenMap_fst.comp (homomorphismRightShear h hh).isOpenMap

/-- A map agreeing generically with an exact reduction passes the joint
generic homomorphism test. No measurable choice or category Fubini converse
is needed: both agreement sets are pulled back by continuous open maps. -/
theorem generic_test_of_reduction_agreement
    (f q : G → Y) (F : Setoid Y) (H : Subgroup G)
    (hred : ∀ g g', GroupCosetRelation H g g' ↔ F.r (f g) (f g'))
    (hag : ∀ᶠ g in residual G, q g = f g)
    (h : A →* G) (hh : Continuous h) (hH : ∀ a, h a ∈ H) :
    ∀ᶠ p : G × A in residual (G × A), F.r (q p.1) (q (p.1 * h p.2)) := by
  have hag₁ := tendsto_residual_of_isOpenMap
    (continuous_fst : Continuous (Prod.fst : G × A → G)) isOpenMap_fst hag
  have hag₂ := tendsto_residual_of_isOpenMap
    (continuous_fst.mul (hh.comp continuous_snd)) (isOpenMap_mul_homomorphism h hh) hag
  filter_upwards [hag₁,hag₂] with p hp₁ hp₂
  change q p.1 = f p.1 at hp₁
  change q (p.1 * h p.2) = f (p.1 * h p.2) at hp₂
  rw [hp₁,hp₂]
  apply (hred _ _).mp
  simpa only [GroupCosetRelation, inv_mul_cancel_left] using hH p.2

theorem generic_separation_of_reduction_agreement
    (f q : G → Y) (F : Setoid Y) (H : Subgroup G)
    (hred : ∀ g g', GroupCosetRelation H g g' ↔ F.r (f g) (f g'))
    (hag : ∀ᶠ g in residual G, q g = f g) (t : G) (ht : t ∉ H) :
    ∀ᶠ g in residual G, ¬ F.r (q g) (q (g*t)) := by
  have hag₂ := tendsto_residual_of_isOpenMap (Homeomorph.mulRight t).continuous
    (Homeomorph.mulRight t).isOpenMap hag
  filter_upwards [hag,hag₂] with g hg hg₂
  change q (g*t) = f (g*t) at hg₂
  rw [hg,hg₂]
  intro heq
  have hm := (hred g (g*t)).mpr heq
  exact ht (by simpa only [GroupCosetRelation, inv_mul_cancel_left] using hm)

end Agreement
end NoBorelUpperBoundFSigma
end
-- END WHOLE MODULE NoBorelUpperBound.CategoryTransfer

-- BEGIN WHOLE MODULE NoBorelUpperBound.CategoryQuantifier

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v

section LocalCategory
variable {X : Type u} [TopologicalSpace X] [SecondCountableTopology X] [BaireSpace X]

/-- The local category test for a Baire-measurable set can be witnessed on a
member of a fixed countable basis. -/
theorem nonmeagre_inter_iff_basic_meagre_compl {s U : Set X}
    (hs : BaireMeasurableSet s) (hU : IsOpen U) :
    ¬ IsMeagre (U ∩ s) ↔ ∃ V : countableBasis X,
      (V : Set X) ⊆ U ∧ IsMeagre ((V : Set X) ∩ sᶜ) := by
  classical
  constructor
  · intro hnon
    obtain ⟨O,hO,heq⟩ := hs.residualEq_isOpen
    have hdiff : IsMeagre {x | ¬ (x ∈ s ↔ x ∈ O)} := by
      change ∀ᶠ x in residual X, ¬¬(x ∈ s ↔ x ∈ O)
      exact (eventuallyEq_set.mp heq).mono (fun _ hx => not_not.mpr hx)
    have hUO : (U ∩ O).Nonempty := by
      by_contra hn
      apply hnon
      apply hdiff.mono
      intro x hx
      intro he
      exact hn ⟨x,hx.1,he.mp hx.2⟩
    obtain ⟨V,hV,hVne,hVsub⟩ :=
      (isBasis_countableBasis X).exists_nonempty_subset hUO (hU.inter hO)
    refine ⟨⟨V,hV⟩, (fun x hx => (hVsub hx).1), hdiff.mono ?_⟩
    intro x hx he
    exact hx.2 (he.mpr (hVsub hx.1).2)
  · rintro ⟨V,hVU,hVm⟩ hUm
    have hVmeagre : IsMeagre (V : Set X) := by
      have hVs : IsMeagre ((V : Set X) ∩ s) :=
        hUm.mono (inter_subset_inter_left _ hVU)
      have hu := hVs.union hVm
      exact hu.mono (by intro x hx; by_cases hxs : x ∈ s <;> simp_all)
    exact not_isMeagre_of_isOpen (isOpen_of_mem_countableBasis V.property)
      (nonempty_of_mem_countableBasis V.property) hVmeagre

end LocalCategory

section BorelQuantifier
variable {P : Type u} {X : Type v}
    [TopologicalSpace P] [PolishSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Nonmeagreness of a Borel section inside a fixed open set is a Borel
condition on the parameter. This is the Borel category quantifier. -/
theorem measurableSet_nonmeagre_sections {S : Set (P × X)} (hS : MeasurableSet S) :
    ∀ U : Set X, IsOpen U → MeasurableSet {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ S})} := by
  classical
  induction S,hS using MeasurableSet.induction_on_open with
  | isOpen S hS =>
    intro U hU
    have heq : {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ S})} = sectionHit S U := by
      ext p
      have hsec : IsOpen (U ∩ {x | (p,x) ∈ S}) :=
        hU.inter (hS.preimage (continuous_const.prodMk continuous_id))
      constructor
      · intro hn
        obtain ⟨x,hxU,hxS⟩ := nonempty_of_not_isMeagre hn
        exact ⟨(p,x),⟨hxS,mem_univ _,hxU⟩,rfl⟩
      · rintro ⟨⟨q,x⟩,⟨hxS,_,hxU⟩,hqp⟩
        dsimp at hqp
        subst q
        exact not_isMeagre_of_isOpen hsec ⟨x,hxU,hxS⟩
    rw [heq]
    exact (isOpen_sectionHit hS hU).measurableSet
  | compl S hS IH =>
    intro U hU
    have hsec (p : P) : BaireMeasurableSet {x | (p,x) ∈ Sᶜ} :=
      (hS.compl.preimage measurable_prodMk_left).baireMeasurableSet
    have heq : {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ Sᶜ})} =
        ⋃ V : countableBasis X, if (V : Set X) ⊆ U then
          {p | IsMeagre ((V : Set X) ∩ {x | (p,x) ∈ S})} else ∅ := by
      ext p
      simp only [mem_setOf_eq, mem_iUnion]
      rw [nonmeagre_inter_iff_basic_meagre_compl (hsec p) hU]
      constructor
      · rintro ⟨V,hVU,hVm⟩
        exact ⟨V, by simpa only [if_pos hVU, mem_setOf_eq, mem_compl_iff,
          Set.compl_setOf, not_not] using hVm⟩
      · rintro ⟨V,hVp⟩
        by_cases hVU : (V : Set X) ⊆ U
        · exact ⟨V,hVU,by simpa only [if_pos hVU, mem_setOf_eq, mem_compl_iff,
            Set.compl_setOf, not_not] using hVp⟩
        · simp only [if_neg hVU, mem_empty_iff_false] at hVp
    rw [heq]
    apply MeasurableSet.iUnion
    intro V
    split_ifs
    · simpa only [Set.compl_setOf, not_not] using
        (IH V (isOpen_of_mem_countableBasis V.property)).compl
    · exact MeasurableSet.empty
  | iUnion f _ hf IH =>
    intro U hU
    have heq : {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ ⋃ n, f n})} =
        ⋃ n, {p | ¬ IsMeagre (U ∩ {x | (p,x) ∈ f n})} := by
      ext p
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · intro hn
        by_contra he
        push Not at he
        apply hn
        have hi : IsMeagre (⋃ n, U ∩ {x | (p,x) ∈ f n}) := isMeagre_iUnion he
        convert hi using 1
        ext x
        simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion]
        tauto
      · rintro ⟨n,hn⟩ hm
        apply hn
        exact hm.mono (by intro x hx; exact ⟨hx.1,⟨n,hx.2⟩⟩)
    rw [heq]
    exact MeasurableSet.iUnion (fun n => IH n U hU)

/-- Comeagreness of Borel sections is a Borel parameter condition. -/
theorem measurableSet_residual_sections {S : Set (P × X)} (hS : MeasurableSet S) :
    MeasurableSet {p | {x | (p,x) ∈ S} ∈ residual X} := by
  have h := (measurableSet_nonmeagre_sections hS.compl Set.univ isOpen_univ).compl
  convert h using 1
  ext p
  simp only [mem_setOf_eq, mem_compl_iff, not_not, Set.univ_inter, IsMeagre,
    Set.compl_setOf, not_not]

end BorelQuantifier
end NoBorelUpperBoundFSigma
end
-- END WHOLE MODULE NoBorelUpperBound.CategoryQuantifier

-- BEGIN WHOLE MODULE NoBorelUpperBound.CategoryMembership

noncomputable section
open Set MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w

namespace FiniteGeneratorWord

/-- A finite sequence of parameters, with the generator index fixed in advance. -/
def Domain (A : ℕ → Type w) : List ℕ → Type w
  | [] => PUnit
  | n :: l => A n × Domain A l

instance domainMeasurableSpace {A : ℕ → Type w} [∀ n, MeasurableSpace (A n)] :
    (l : List ℕ) → MeasurableSpace (Domain A l)
  | [] => inferInstanceAs (MeasurableSpace PUnit)
  | n :: l => @Prod.instMeasurableSpace (A n) (Domain A l) inferInstance
      (domainMeasurableSpace l)

instance domainStandardBorelSpace {A : ℕ → Type w} [∀ n, MeasurableSpace (A n)]
    [∀ n, StandardBorelSpace (A n)] : (l : List ℕ) → StandardBorelSpace (Domain A l)
  | [] => inferInstanceAs (StandardBorelSpace PUnit)
  | n :: l => by
      letI := domainStandardBorelSpace (A := A) l
      exact inferInstanceAs (StandardBorelSpace (A n × Domain A l))

def value {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) :
    (l : List ℕ) → P → Domain A l → G
  | [], _, _ => 1
  | n :: l, p, a => h n p a.1 * value h l p a.2

theorem measurable_value {P : Type u} [MeasurableSpace P]
    {G : Type v} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, MeasurableSpace (A n)]
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2)) :
    ∀ l : List ℕ, Measurable (fun pa : P × Domain A l => value h l pa.1 pa.2) := by
  intro l
  induction l with
  | nil => exact measurable_const
  | cons n l IH =>
      exact ((hh n).comp (measurable_fst.prodMk measurable_snd.fst)).mul
        (IH.comp (measurable_fst.prodMk measurable_snd.snd))

theorem value_mem {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P) :
    ∀ (l : List ℕ) (a : Domain A l), value h l p a ∈ GeneratedSubgroup h p := by
  intro l
  induction l with
  | nil => intro a; exact (GeneratedSubgroup h p).one_mem
  | cons n l IH =>
      intro a
      exact (GeneratedSubgroup h p).mul_mem
        (Subgroup.subset_closure (mem_iUnion.mpr ⟨n,mem_range_self a.1⟩)) (IH a.2)

theorem list_representation {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P)
    (L : List (Σ n, A n)) :
    ∃ (l : List ℕ) (a : Domain A l),
      value h l p a = (L.map (fun x => h x.1 p x.2)).prod := by
  induction L with
  | nil => exact ⟨[],PUnit.unit,rfl⟩
  | cons x L IH =>
      obtain ⟨l,a,ha⟩ := IH
      exact ⟨x.1 :: l,(x.2,a),by simpa only [value,List.map_cons,List.prod_cons,ha]⟩

def listSubgroup {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P) : Subgroup G where
  carrier := {g | ∃ L : List (Σ n, A n), (L.map (fun x => h x.1 p x.2)).prod = g}
  one_mem' := ⟨[],rfl⟩
  mul_mem' := by
    rintro x y ⟨L,rfl⟩ ⟨M,rfl⟩
    exact ⟨L ++ M,by simp⟩
  inv_mem' := by
    rintro x ⟨L,rfl⟩
    refine ⟨(L.map (fun x => (⟨x.1,x.2⁻¹⟩ : Σ n, A n))).reverse,?_⟩
    simp only [List.map_reverse,List.map_map,Function.comp_def,map_inv]
    simpa only [List.map_map,Function.comp_def] using
      (List.prod_inv_reverse (L.map (fun x => h x.1 p x.2))).symm

theorem mem_iff_exists_value {P : Type u} {G : Type v} [Group G] {A : ℕ → Type w}
    [∀ n, Group (A n)] (h : ∀ n, P → (A n →* G)) (p : P) (g : G) :
    g ∈ GeneratedSubgroup h p ↔ ∃ (l : List ℕ) (a : Domain A l), value h l p a = g := by
  constructor
  · intro hg
    have hle : GeneratedSubgroup h p ≤ listSubgroup h p := by
      apply (Subgroup.closure_le _).2
      intro x hx
      obtain ⟨n,a,rfl⟩ := mem_iUnion.mp hx
      exact ⟨[⟨n,a⟩],by simp⟩
    obtain ⟨L,hL⟩ := hle hg
    obtain ⟨l,a,ha⟩ := list_representation h p L
    exact ⟨l,a,ha.trans hL⟩
  · rintro ⟨l,a,rfl⟩
    exact value_mem h p l a

end FiniteGeneratorWord

/-- Membership in an algebraically generated countable Borel family of
continuous-homomorphism images is analytic. Algebraic membership uses finite
words, with no topological closure involved. -/
theorem analyticSet_membershipSet
    {P : Type u} [TopologicalSpace P] [PolishSpace P] [MeasurableSpace P] [BorelSpace P]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, MeasurableSpace (A n)]
    [∀ n, StandardBorelSpace (A n)]
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (z₀ : P → G) (hz : Measurable z₀) : AnalyticSet (MembershipSet h z₀) := by
  classical
  have heq : MembershipSet h z₀ = ⋃ l : List ℕ,
      Prod.fst '' {pa : P × FiniteGeneratorWord.Domain A l |
        FiniteGeneratorWord.value h l pa.1 pa.2 = z₀ pa.1} := by
    ext p
    simp only [MembershipSet,mem_setOf_eq,mem_iUnion,mem_image,Prod.exists]
    rw [FiniteGeneratorWord.mem_iff_exists_value]
    constructor
    · rintro ⟨l,a,ha⟩
      exact ⟨l,p,a,ha,rfl⟩
    · rintro ⟨l,q,a,ha,rfl⟩
      exact ⟨l,a,ha⟩
  rw [heq]
  apply AnalyticSet.iUnion
  intro l
  have hS : MeasurableSet {pa : P × FiniteGeneratorWord.Domain A l |
      FiniteGeneratorWord.value h l pa.1 pa.2 = z₀ pa.1} :=
    measurableSet_eq_fun (FiniteGeneratorWord.measurable_value h hh l) (hz.comp measurable_fst)
  exact hS.analyticSet_image measurable_fst

end NoBorelUpperBoundFSigma
end
-- END WHOLE MODULE NoBorelUpperBound.CategoryMembership

-- BEGIN WHOLE MODULE NoBorelUpperBound.CategoryAnalytic

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w z t

section Witness
variable {P : Type u} {C : Type v} {G : Type w} {A : ℕ → Type z} {Y : Type t}
    [Group G] [TopologicalSpace G]
    [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]

/-- Generic generator invariance and generic designated-element separation. -/
def GenericWitness (h : ∀ n, P → (A n →* G)) (z₀ : P → G)
    (eval : C → G → Y) (F : Setoid Y) (pc : P × C) : Prop :=
  (∀ n, ∀ᶠ ga : G × A n in residual (G × A n),
    F.r (eval pc.2 ga.1) (eval pc.2 (ga.1 * h n pc.1 ga.2))) ∧
  (∀ᶠ g in residual G, ¬ F.r (eval pc.2 g) (eval pc.2 (g*z₀ pc.1)))

end Witness

section BorelWitness
variable {P : Type u} [TopologicalSpace P] [PolishSpace P]
    [MeasurableSpace P] [BorelSpace P]
    {C : Type v} [TopologicalSpace C] [PolishSpace C]
    [MeasurableSpace C] [BorelSpace C]
    {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {A : ℕ → Type z} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, IsTopologicalGroup (A n)] [∀ n, PolishSpace (A n)]
    [∀ n, MeasurableSpace (A n)] [∀ n, BorelSpace (A n)]
    {Y : Type t} [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]

/-- The set of generic tests is genuinely Borel, including its category
quantifiers. -/
theorem measurableSet_genericWitness
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (z₀ : P → G) (hz : Measurable z₀)
    (eval : C → G → Y) (heval : Measurable (fun cg : C × G => eval cg.1 cg.2))
    (F : Setoid Y) (hF : IsBorelRelation F.r) :
    MeasurableSet {pc | GenericWitness h z₀ eval F pc} := by
  have hFb : MeasurableSet {yy : Y × Y | F.r yy.1 yy.2} := by
    unfold IsBorelRelation at hF
    rwa [← BorelSpace.measurable_eq] at hF
  have hgen (n : ℕ) : MeasurableSet {pc : P × C |
      ∀ᶠ ga : G × A n in residual (G × A n),
        F.r (eval pc.2 ga.1) (eval pc.2 (ga.1 * h n pc.1 ga.2))} := by
    apply measurableSet_residual_sections (S := {p : (P × C) × (G × A n) |
      F.r (eval p.1.2 p.2.1) (eval p.1.2 (p.2.1 * h n p.1.1 p.2.2))})
    apply hFb.preimage (f := fun p : (P × C) × (G × A n) =>
      (eval p.1.2 p.2.1, eval p.1.2 (p.2.1 * h n p.1.1 p.2.2)))
    apply Measurable.prodMk
    · exact heval.comp (measurable_fst.snd.prodMk measurable_snd.fst)
    · exact heval.comp (measurable_fst.snd.prodMk
        (measurable_snd.fst.mul ((hh n).comp
          (measurable_fst.fst.prodMk measurable_snd.snd))))
  have hsep : MeasurableSet {pc : P × C | ∀ᶠ g in residual G,
      ¬ F.r (eval pc.2 g) (eval pc.2 (g*z₀ pc.1))} := by
    apply measurableSet_residual_sections (S := {p : (P × C) × G |
      ¬ F.r (eval p.1.2 p.2) (eval p.1.2 (p.2 * z₀ p.1.1))})
    apply hFb.compl.preimage (f := fun p : (P × C) × G =>
      (eval p.1.2 p.2, eval p.1.2 (p.2 * z₀ p.1.1)))
    apply Measurable.prodMk
    · exact heval.comp (measurable_fst.snd.prodMk measurable_snd)
    · exact heval.comp (measurable_fst.snd.prodMk
        (measurable_snd.mul (hz.comp measurable_fst.fst)))
  have hforall : MeasurableSet {pc : P × C | ∀ n,
      ∀ᶠ ga : G × A n in residual (G × A n),
        F.r (eval pc.2 ga.1) (eval pc.2 (ga.1 * h n pc.1 ga.2))} := by
    simpa only [setOf_forall] using MeasurableSet.iInter hgen
  exact hforall.inter hsep

/-- Analytic generic witness projection equals the complement of membership
when actual reductions are available there. -/
theorem genericWitness_projection_eq_compl
    (h : ∀ n, P → (A n →* G)) (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (eval : C → G → Y) (F : Setoid Y)
    (hrep : ∀ f : G → Y, NoUniversalFSigma.IsBorelMeasurable f →
      ∃ c, ∀ᶠ g in residual G, eval c g = f g)
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    Prod.fst '' {pc : P × C | GenericWitness h z₀ eval F pc} = (MembershipSet h z₀)ᶜ := by
  ext p
  constructor
  · rintro ⟨⟨q,c⟩,⟨hgen,hsep⟩,hqp⟩
    dsimp at hqp
    subst q
    exact generic_tests_exclude_membership (eval c) F h p (z₀ p) hgen hsep
  · intro hp
    obtain ⟨f,hf,hred⟩ := hbound p hp
    obtain ⟨c,hag⟩ := hrep f hf
    refine ⟨(p,c),⟨?_,?_⟩,rfl⟩
    · intro n
      exact generic_test_of_reduction_agreement f (eval c) F (GeneratedSubgroup h p)
        hred hag (h n p) (hc n p) (fun a => Subgroup.subset_closure (mem_iUnion.mpr ⟨n,mem_range_self a⟩))
    · exact generic_separation_of_reduction_agreement f (eval c) F (GeneratedSubgroup h p)
        hred hag (z₀ p) hp

/-- Category transfer once a universal Borel evaluation modulo meager
agreement and analyticity of the designated membership family are supplied.
Both premises are explicit infrastructure obligations. -/
theorem membership_measurable_of_generic_codes
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (hz : Measurable z₀)
    (eval : C → G → Y) (heval : Measurable (fun cg : C × G => eval cg.1 cg.2))
    (hrep : ∀ f : G → Y, NoUniversalFSigma.IsBorelMeasurable f →
      ∃ c, ∀ᶠ g in residual G, eval c g = f g)
    (F : Setoid Y) (hF : IsBorelRelation F.r)
    (hM : AnalyticSet (MembershipSet h z₀))
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    MeasurableSet (MembershipSet h z₀) := by
  have hW := measurableSet_genericWitness h hh z₀ hz eval heval F hF
  have hproj : AnalyticSet (Prod.fst '' {pc : P × C | GenericWitness h z₀ eval F pc}) :=
    hW.analyticSet.image_of_continuous continuous_fst
  rw [genericWitness_projection_eq_compl h hc z₀ eval F hrep hbound] at hproj
  exact hM.measurableSet_of_compl hproj

/-- The generic homomorphism category-transfer principle. The sole coding
input is a jointly Borel family representing all Borel maps modulo meager
agreement. -/
theorem category_transfer_of_generic_codes
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (hz : Measurable z₀)
    (eval : C → G → Y) (heval : Measurable (fun cg : C × G => eval cg.1 cg.2))
    (hrep : ∀ f : G → Y, NoUniversalFSigma.IsBorelMeasurable f →
      ∃ c, ∀ᶠ g in residual G, eval c g = f g)
    (F : Setoid Y) (hF : IsBorelRelation F.r)
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    MeasurableSet (MembershipSet h z₀) :=
  membership_measurable_of_generic_codes h hh hc z₀ hz eval heval hrep F hF
    (analyticSet_membershipSet h hh z₀ hz) hbound

end BorelWitness
end NoBorelUpperBoundFSigma
end
-- END WHOLE MODULE NoBorelUpperBound.CategoryAnalytic

-- BEGIN WHOLE MODULE NoBorelUpperBound.BaireContinuity

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v

/-- A Borel map admits a countable array of open dense-point tests which are
correct simultaneously outside a meager set. No uniform bound on Borel ranks
is required. -/
theorem exists_open_generic_approximation
    {G : Type u} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    {Y : Type v} [PseudoMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (f : G → Y) (hf : Measurable f) (y : ℕ → Y) (hy : DenseRange y)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ U : ℕ → ℕ → Set G, (∀ n j, IsOpen (U n j)) ∧
      ∀ᶠ g in residual G, ∀ n,
        (∃ j, g ∈ U n j) ∧ (∀ j, g ∈ U n j → dist (y j) (f g) < ε n) := by
  classical
  have htest (n j : ℕ) :
      ∃ U : Set G, IsOpen U ∧ {g | dist (y j) (f g) < ε n} =ᵇ U := by
    have hB : MeasurableSet {g | dist (y j) (f g) < ε n} := by
      have hO : IsOpen {q : Y | dist (y j) q < ε n} :=
        isOpen_lt (continuous_const.dist continuous_id) continuous_const
      exact hO.measurableSet.preimage hf
    exact hB.residualEq_isOpen
  choose U hU heq using htest
  refine ⟨U,hU,?_⟩
  have hag : ∀ᶠ g in residual G, ∀ n j,
      dist (y j) (f g) < ε n ↔ g ∈ U n j := by
    apply eventually_countable_forall.mpr
    intro n
    apply eventually_countable_forall.mpr
    intro j
    exact eventuallyEq_set.mp (heq n j)
  filter_upwards [hag] with g hg
  intro n
  refine ⟨?_,fun j hj => (hg n j).mpr hj⟩
  obtain ⟨j,hj⟩ := hy.exists_dist_lt (f g) (hε n)
  exact ⟨j,(hg n j).mp (by simpa only [dist_comm] using hj)⟩

/-- Distances bounded by a sequence tending to zero imply convergence. -/
theorem tendsto_of_dist_lt_approximation
    {Y : Type v} [PseudoMetricSpace Y] (s : ℕ → Y) (y : Y)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hs : ∀ n, dist (s n) y < ε n) : Tendsto s atTop (𝓝 y) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have he : ∀ᶠ n in atTop, ε n < δ := (tendsto_order.1 hε).2 δ hδ
  exact he.mono (fun n hn => lt_trans (hs n) hn)

end NoBorelUpperBoundFSigma
end
-- END WHOLE MODULE NoBorelUpperBound.BaireContinuity

-- BEGIN WHOLE MODULE NoBorelUpperBound.BorelEvaluator

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.BorelCodes

variable (G : Type*) [TopologicalSpace G] [SecondCountableTopology G]

/-- Countably many open sets, coded using a fixed countable topological basis. -/
def Code := (ℕ × ℕ × countableBasis G) → Bool

instance : TopologicalSpace (Code G) := inferInstanceAs (TopologicalSpace ((_ × _ × _) → Bool))
instance : PolishSpace (Code G) where
  toSecondCountableTopology := inferInstanceAs (SecondCountableTopology ((_ × _ × _) → Bool))
  toIsCompletelyMetrizableSpace := inferInstanceAs
    (IsCompletelyMetrizableSpace ((_ × _ × _) → Bool))
instance : MeasurableSpace (Code G) := borel (Code G)
instance : BorelSpace (Code G) := ⟨rfl⟩

variable {G}

def eligible (c : Code G) (g : G) (n j : ℕ) : Prop :=
  ∃ b : countableBasis G, c (n,j,b) = true ∧ g ∈ (b : Set G)

private theorem exists_candidate (c : Code G) (g : G) (n : ℕ) :
    ∃ j, eligible c g n j ∨ ¬ ∃ k, eligible c g n k := by
  by_cases h : ∃ j, eligible c g n j
  · obtain ⟨j,hj⟩ := h
    exact ⟨j,Or.inl hj⟩
  · exact ⟨0,Or.inr h⟩

def selected (c : Code G) (g : G) (n : ℕ) : ℕ := Nat.find (exists_candidate c g n)

theorem eligible_selected (c : Code G) (g : G) (n : ℕ)
    (h : ∃ j, eligible c g n j) : eligible c g n (selected c g n) := by
  exact (Nat.find_spec (exists_candidate c g n)).resolve_right (not_not.mpr h)

variable [MeasurableSpace G] [BorelSpace G]

theorem measurableSet_eligible (n j : ℕ) :
    MeasurableSet {p : Code G × G | eligible p.1 p.2 n j} := by
  have hb (b : countableBasis G) : MeasurableSet
      {p : Code G × G | p.1 (n,j,b) = true ∧ p.2 ∈ (b : Set G)} := by
    have hc : Measurable (fun c : Code G => c (n,j,b)) :=
      (show Continuous (fun c : Code G => c (n,j,b)) from continuous_apply _).measurable
    exact ((isClosed_discrete ({true} : Set Bool)).measurableSet.preimage
      (hc.comp measurable_fst)).inter
      ((isOpen_of_mem_countableBasis b.property).measurableSet.preimage measurable_snd)
  simpa only [eligible, setOf_exists] using MeasurableSet.iUnion hb

theorem measurable_selected (n : ℕ) :
    Measurable (fun p : Code G × G => selected p.1 p.2 n) := by
  apply measurable_find (fun p : Code G × G => exists_candidate p.1 p.2 n)
  intro j
  have hex : MeasurableSet {p : Code G × G | ∃ k, eligible p.1 p.2 n k} := by
    simpa only [setOf_exists] using
      MeasurableSet.iUnion (fun k => measurableSet_eligible (G := G) n k)
  exact (measurableSet_eligible n j).union hex.compl

variable {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]

def approximation (c : Code G) (g : G) (n : ℕ) : Y :=
  denseSeq Y (selected c g n)

def eval (c : Code G) (g : G) : Y :=
  limUnder atTop (fun n : ℕ => approximation c g n)

variable [MeasurableSpace Y] [BorelSpace Y]

theorem measurable_approximation (n : ℕ) :
    Measurable (fun p : Code G × G => (approximation p.1 p.2 n : Y)) := by
  exact (measurable_of_countable (denseSeq Y)).comp (measurable_selected n)

theorem measurable_eval :
    Measurable (fun p : Code G × G => (eval p.1 p.2 : Y)) := by
  exact (StronglyMeasurable.limUnder
    (fun n : ℕ => (measurable_approximation (Y := Y) (G := G) n).stronglyMeasurable)).measurable

end NoBorelUpperBoundFSigma.BorelCodes
end
-- END WHOLE MODULE NoBorelUpperBound.BorelEvaluator

-- BEGIN WHOLE MODULE NoBorelUpperBound.GenericRepresentation

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter TopologicalSpace Topology MeasureTheory

namespace NoBorelUpperBoundFSigma.BorelCodes
universe u v

variable {G : Type u} [TopologicalSpace G] [SecondCountableTopology G]

/-- Encode an array of open tests by all basis sets contained in each test. -/
def codeOfOpenTests (U : ℕ → ℕ → Set G) : Code G :=
  fun q => decide ((q.2.2 : Set G) ⊆ U q.1 q.2.1)

theorem eligible_codeOfOpenTests_iff (U : ℕ → ℕ → Set G)
    (hU : ∀ n j, IsOpen (U n j)) (g : G) (n j : ℕ) :
    eligible (codeOfOpenTests U) g n j ↔ g ∈ U n j := by
  classical
  constructor
  · rintro ⟨b,hb,hg⟩
    have hbU : (b : Set G) ⊆ U n j := by
      simpa only [codeOfOpenTests,decide_eq_true_eq] using hb
    exact hbU hg
  · intro hg
    obtain ⟨b,hb,hgb,hbU⟩ :=
      (isBasis_countableBasis G).exists_subset_of_mem_open hg (hU n j)
    exact ⟨⟨b,hb⟩,by simpa only [codeOfOpenTests,decide_eq_true_eq] using hbU,hgb⟩

/-- The fixed Borel evaluator represents every Borel map outside a meager
set. This concerns agreement modulo category, so Borel ranks need not be
bounded by a common ordinal. -/
theorem exists_code_residual_eq
    [MeasurableSpace G] [BorelSpace G]
    {Y : Type v} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (f : G → Y) (hf : Measurable f) :
    ∃ c : Code G, ∀ᶠ g in residual G, eval c g = f g := by
  letI := upgradeIsCompletelyMetrizable Y
  obtain ⟨U,hU,hag⟩ := NoBorelUpperBoundFSigma.exists_open_generic_approximation
    f hf (denseSeq Y) (denseRange_denseSeq Y)
    (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
    (fun n => div_pos zero_lt_one (by positivity))
  refine ⟨codeOfOpenTests U, hag.mono ?_⟩
  intro g hg
  change limUnder atTop (fun n : ℕ => (approximation (codeOfOpenTests U) g n : Y)) = f g
  apply Filter.Tendsto.limUnder_eq
  apply NoBorelUpperBoundFSigma.tendsto_of_dist_lt_approximation _ _
    (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
    tendsto_one_div_add_atTop_nhds_zero_nat
  intro n
  apply (hg n).2
  apply (eligible_codeOfOpenTests_iff U hU g n _).mp
  apply eligible_selected
  obtain ⟨j,hj⟩ := (hg n).1
  exact ⟨j,(eligible_codeOfOpenTests_iff U hU g n j).mpr hj⟩

/-- Topological Borel-measurability version used by the mission definitions. -/
theorem exists_code_of_isBorelMeasurable
    [MeasurableSpace G] [BorelSpace G]
    {Y : Type v} [TopologicalSpace Y] [PolishSpace Y] [Nonempty Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (f : G → Y) (hf : NoUniversalFSigma.IsBorelMeasurable f) :
    ∃ c : Code G, ∀ᶠ g in residual G, eval c g = f g := by
  apply exists_code_residual_eq f
  unfold NoUniversalFSigma.IsBorelMeasurable at hf
  rwa [← BorelSpace.measurable_eq,← BorelSpace.measurable_eq] at hf

end NoBorelUpperBoundFSigma.BorelCodes
end
-- END WHOLE MODULE NoBorelUpperBound.GenericRepresentation

-- BEGIN WHOLE MODULE NoBorelUpperBound.CategoryTransferFinal

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory

namespace NoBorelUpperBoundFSigma
universe u v w z

/-- Generic homomorphism category transfer, for a standard Borel parameter
space and countably many continuously parametrized Polish-group generators.
The Borel evaluator and the finite-word analytic membership witnesses are
constructed in the proof rather than assumed. -/
theorem category_transfer
    {P : Type u} [MeasurableSpace P] [StandardBorelSpace P]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, IsTopologicalGroup (A n)] [∀ n, PolishSpace (A n)]
    [∀ n, MeasurableSpace (A n)] [∀ n, BorelSpace (A n)]
    {Y : Type z} [TopologicalSpace Y] [PolishSpace Y]
    (h : ∀ n, P → (A n →* G))
    (hh : ∀ n, Measurable (fun pa : P × A n => h n pa.1 pa.2))
    (hc : ∀ n p, Continuous (h n p))
    (z₀ : P → G) (hz : Measurable z₀)
    (F : Setoid Y) (hF : IsBorelRelation F.r)
    (hbound : ∀ p, p ∉ MembershipSet h z₀ →
      BorelReducible (GroupCosetRelation (GeneratedSubgroup h p)) F.r) :
    MeasurableSet (MembershipSet h z₀) := by
  classical
  letI := upgradeStandardBorel P
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace Y := ⟨rfl⟩
  by_cases hfull : ∀ p, p ∈ MembershipSet h z₀
  · have heq : MembershipSet h z₀ = univ := by ext p; simp [hfull p]
    rw [heq]
    exact MeasurableSet.univ
  · obtain ⟨p,hp⟩ := not_forall.mp hfull
    obtain ⟨f,_,_⟩ := hbound p hp
    letI : Nonempty Y := ⟨f 1⟩
    exact category_transfer_of_generic_codes h hh hc z₀ hz
      (BorelCodes.eval (Y := Y)) BorelCodes.measurable_eval
      BorelCodes.exists_code_of_isBorelMeasurable F hF hbound

end NoBorelUpperBoundFSigma
end
-- END WHOLE MODULE NoBorelUpperBound.CategoryTransferFinal

universe u v w z t

theorem solution
    {P : Type u} [MeasurableSpace P] [StandardBorelSpace P]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    {A : ℕ → Type w} [∀ n, Group (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, IsTopologicalGroup (A n)] [∀ n, PolishSpace (A n)]
    {Y : Type z} [TopologicalSpace Y] [PolishSpace Y]
    (h : ∀ n, P → (A n →* G))
    (h_joint : ∀ n, @Measurable (P × A n) G
      ((inferInstance : MeasurableSpace P).prod (borel (A n))) (borel G)
      (fun pa => h n pa.1 pa.2))
    (h_cont : ∀ n p, Continuous (h n p))
    (z0 : P → G) (hz : @Measurable P G inferInstance (borel G) z0)
    (F : Setoid Y) (hF : NoBorelUpperBoundFSigma.IsBorelRelation F.r)
    (h_bound : ∀ p, p ∉ NoBorelUpperBoundFSigma.MembershipSet h z0 →
      NoBorelUpperBoundFSigma.BorelReducible
        (NoBorelUpperBoundFSigma.GroupCosetRelation
          (NoBorelUpperBoundFSigma.GeneratedSubgroup h p)) F.r) :
    MeasurableSet (NoBorelUpperBoundFSigma.MembershipSet h z0) := by
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  letI : ∀ n, MeasurableSpace (A n) := fun n => borel (A n)
  letI : ∀ n, BorelSpace (A n) := fun _ => ⟨rfl⟩
  exact NoBorelUpperBoundFSigma.category_transfer h h_joint h_cont z0 hz F hF h_bound
