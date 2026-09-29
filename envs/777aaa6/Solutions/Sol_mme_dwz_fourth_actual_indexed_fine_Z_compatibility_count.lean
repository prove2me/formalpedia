-- Prove2me | solution 1 for mme_dwz_fourth_actual_indexed_fine_Z_compatibility_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T21:47:40.286847+00:00
-- url     : https://prove2.me/submissions/b5441d6d-09df-4079-9f9d-8fdfb3ab0b27

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Theorems.Thm_mme_dwz_boundary_compatible_assignment_card_of_useful_witness
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Card
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.Pi

open BigOperators MME.CompleteSplit MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZActualFineZCompatibility

def totalTag (v : CompleteWord 3) : Fin 9 :=
  ⟨∑ r, (v r).val, by
    have h0 := (v 0).isLt
    have h1 := (v 1).isLt
    have h2 := (v 2).isLt
    have h3 := (v 3).isLt
    change (∑ r : Fin 4, (v r).val) < 9
    rw [Fin.sum_univ_four]
    omega⟩

def fineLabel {N : ℕ} (f : FineWord 3 N) (t : Fin N) : Fin 9 × Fin 5 :=
  (totalTag (f t), fourthLeftTag (f t))

def boundary {k : ℕ} (shape : Fin k → Fin 3 → ℕ) (c : Fin k) : Prop :=
  shape c 0 = 0 ∨ shape c 1 = 0

noncomputable def fineMass {k : ℕ} (coarse : Fin k → Fin 9)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (i : Fin 9 × Fin 5) : ℕ :=
  ∑ c : {c : Fin k // coarse c = i.1}, mu 2 c.val i.2

noncomputable def collapse {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (c : Fin k) : Fin k ⊕ Fin 9 :=
  if boundary shape c then Sum.inl c else Sum.inr (coarse c)

noncomputable def pooledMass {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ) :
    (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ
  | (Sum.inl c, (g,l)) => if boundary shape c ∧ coarse c = g then mu 2 c l else 0
  | (Sum.inr g', (g,l)) => if g' = g then fineMass coarse mu (g,l) -
      ∑ c ∈ Finset.univ.filter (fun c ↦ boundary shape c ∧ coarse c = g), mu 2 c l
    else 0

noncomputable def compatibilityCount {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ) : ℕ :=
  (∏ i : Fin 9 × Fin 5, (fineMass coarse mu i).factorial /
    ∏ di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
      (pooledMass shape coarse mu di.val).factorial) *
  (∏ d : Fin k ⊕ Fin 9, (∑ i, pooledMass shape coarse mu (d,i)).factorial /
    ∏ c : {c : Fin k // collapse shape coarse c = d}, (n c.val).factorial)

def assignmentCompatible {N k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (f : FineWord 3 N) (g : Fin N → Fin k) : Prop :=
  (∀ c, Fintype.card {t : Fin N // g t = c} = n c) ∧
  (∀ t, ∑ r, (f t r).val = shape (g t) 2) ∧
  ∀ c, boundary shape c → ∀ l,
    Fintype.card {t : Fin N // g t = c ∧ fourthLeftTag (f t) = l} = mu 2 c l

theorem sum_joint_pred {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq C] (g : A → C) (Q : C → Prop) [DecidablePred Q]
    (P : A → Prop) [DecidablePred P] :
    (∑ c : {c : C // Q c}, Fintype.card {a : A // g a = c.val ∧ P a}) =
      Fintype.card {a : A // Q (g a) ∧ P a} := by
  classical
  let e : (Σ c : {c : C // Q c}, {a : A // g a = c.val ∧ P a}) ≃
      {a : A // Q (g a) ∧ P a} := {
    toFun := fun x ↦ ⟨x.2.val, x.2.property.1.symm ▸ x.1.property, x.2.property.2⟩
    invFun := fun a ↦ ⟨⟨g a.val, a.property.1⟩, ⟨a.val, rfl, a.property.2⟩⟩
    left_inv := by rintro ⟨⟨c,hc⟩,⟨a,ha,hp⟩⟩; cases ha; rfl
    right_inv := fun _ ↦ rfl }
  simpa only [Fintype.card_sigma] using Fintype.card_congr e

theorem graded_coarse_eq {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (j : Fin R) (f : FineWord 3 N) (hg : Graded component shape j 2 f) (t : Fin N) :
    coarse (component j t) = (fineLabel f t).1 := by
  apply Fin.ext
  exact (hshape _).trans (hg t).symm

theorem useful_fine_histogram {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (j : Fin R) (f : FineWord 3 N)
    (hg : Graded component shape j 2 f) (hp : Profile component fourthLeftTag mu j 2 f)
    (i : Fin 9 × Fin 5) :
    Fintype.card {t : Fin N // fineLabel f t = i} = fineMass coarse mu i := by
  classical
  calc
    _ = Fintype.card {t : Fin N // coarse (component j t) = i.1 ∧
        fourthLeftTag (f t) = i.2} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro t
      rw [graded_coarse_eq component shape coarse hshape j f hg t]
      exact Prod.ext_iff
    _ = ∑ c : {c : Fin k // coarse c = i.1},
        Fintype.card {t : Fin N // component j t = c.val ∧ fourthLeftTag (f t) = i.2} :=
      (sum_joint_pred (component j) (fun c ↦ coarse c = i.1)
        (fun t ↦ fourthLeftTag (f t) = i.2)).symm
    _ = _ := Finset.sum_congr rfl (fun c _ ↦ hp c.val i.2)

theorem aggregate_of_useful {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (j b : Fin R) (f : FineWord 3 N)
    (hg : Graded component shape j 2 f) (hp : Profile component fourthLeftTag mu j 2 f)
    (hb : Graded component shape b 2 f) (g : Fin 9) (l : Fin 5) :
    Fintype.card {t : Fin N // shape (component b t) 2 = g.val ∧
      fourthLeftTag (f t) = l} = fineMass coarse mu (g,l) := by
  rw [← useful_fine_histogram component shape coarse hshape mu j f hg hp (g,l)]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  rw [← hb t]
  change (totalTag (f t)).val = g.val ∧ fourthLeftTag (f t) = l ↔ _
  rw [← Fin.ext_iff]
  change (totalTag (f t) = g ∧ fourthLeftTag (f t) = l) ↔
    (totalTag (f t), fourthLeftTag (f t)) = (g,l)
  exact ⟨fun h ↦ Prod.ext h.1 h.2, fun h ↦ ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

set_option maxHeartbeats 150000 in
theorem assignment_count_of_useful {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (j : Fin R) (f : FineWord 3 N)
    (hn : ∀ c, Fintype.card {t : Fin N // component j t = c} = n c)
    (hg : Graded component shape j 2 f) (hp : Profile component fourthLeftTag mu j 2 f) :
    Nat.card {g : Fin N → Fin k // assignmentCompatible shape mu n f g} =
      compatibilityCount shape coarse mu n := by
  classical
  have hf := useful_fine_histogram component shape coarse hshape mu j f hg hp
  have hc := mme_dwz_boundary_compatible_assignment_card_of_useful_witness
    (fineLabel f) coarse (boundary shape) (component j)
    (graded_coarse_eq component shape coarse hshape j f hg)
  dsimp only at hc
  have hpred (g : Fin N → Fin k) :
      assignmentCompatible shape mu n f g ↔
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) ∧
      (∀ t, coarse (g t) = (fineLabel f t).1) ∧
      ∀ c, boundary shape c → ∀ l,
        Fintype.card {t : Fin N // g t = c ∧ (fineLabel f t).2 = l} = mu 2 c l := by
    unfold assignmentCompatible
    apply and_congr_right
    intro _
    apply and_congr_left
    intro _
    apply forall_congr'
    intro t
    rw [Fin.ext_iff, hshape]
    exact eq_comm
  have hp' (c : Fin k) (l : Fin 5) :
      Fintype.card {t : Fin N // component j t = c ∧ (fineLabel f t).2 = l} = mu 2 c l := hp c l
  simp only [hn, hp', hf] at hc
  calc
    _ = Nat.card {g : Fin N → Fin k //
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) ∧
      (∀ t, coarse (g t) = (fineLabel f t).1) ∧
      ∀ c, boundary shape c → ∀ l,
        Fintype.card {t : Fin N // g t = c ∧ (fineLabel f t).2 = l} = mu 2 c l} :=
      Nat.card_congr (Equiv.subtypeEquivRight hpred)
    _ = _ := by
      refine hc.trans ?_
      unfold compatibilityCount collapse
      apply congrArg₂ Nat.mul
      · apply Finset.prod_congr rfl
        intro i _
        apply congrArg (fun d : ℕ ↦ (fineMass coarse mu i).factorial / d)
        apply Finset.prod_congr
        · ext di
          simp only [Finset.mem_univ]
        · intro di _
          apply congrArg Nat.factorial
          rcases di with ⟨⟨d,g,l⟩,hi⟩
          cases d <;> rfl
      · apply Finset.prod_congr rfl
        intro d _
        apply congrArg₂ Nat.div
        · apply congrArg Nat.factorial
          apply Finset.sum_congr rfl
          rintro ⟨g,l⟩ _
          cases d <;> rfl
        · apply Finset.prod_congr
          · ext c
            simp only [Finset.mem_univ]
          · intro c _
            rfl

end MME.DWZActualFineZCompatibility

open BigOperators MME.CompleteSplit MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZActualFineZCompatibility

theorem profile_component_count {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (j : Fin R) (f : FineWord 3 N)
    (hp : Profile component fourthLeftTag mu j 2 f) (c : Fin k) :
    Fintype.card {t : Fin N // component j t = c} = ∑ l, mu 2 c l := by
  classical
  let e : (Σ l : Fin 5, {t : Fin N // component j t = c ∧ fourthLeftTag (f t) = l}) ≃
      {t : Fin N // component j t = c} := {
    toFun := fun x ↦ ⟨x.2.val, x.2.property.1⟩
    invFun := fun t ↦ ⟨fourthLeftTag (f t.val), ⟨t.val,t.property,rfl⟩⟩
    left_inv := by rintro ⟨l,⟨t,ht,hl⟩⟩; cases hl; rfl
    right_inv := fun _ ↦ rfl }
  have hc := (Fintype.card_congr e).symm
  have hp' (l : Fin 5) :
      Fintype.card {t : Fin N // component j t = c ∧ fourthLeftTag (f t) = l} = mu 2 c l :=
    hp c l
  simpa only [Fintype.card_sigma, hp'] using hc

theorem assignment_iff_indexed {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (b : Fin R) (f : FineWord 3 N)
    (hn : ∀ c, Fintype.card {t : Fin N // component b t = c} = n c) :
    assignmentCompatible shape mu n f (component b) ↔
      ZCompatible component shape fourthLeftTag mu b f :=
  ⟨fun h ↦ ⟨h.2.1,h.2.2⟩, fun h ↦ ⟨hn,h.1,h.2⟩⟩

noncomputable def compatibleTargetEquiv {N k R : ℕ}
    (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (targets : Finset (Fin R)) (f : FineWord 3 N)
    (hn : ∀ b ∈ targets, ∀ c, Fintype.card {t : Fin N // component b t = c} = n c)
    (hinj : Set.InjOn component (targets : Set (Fin R)))
    (hcomplete : ∀ g : Fin N → Fin k,
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) →
      ∃ b ∈ targets, component b = g) :
    {b : Fin R // b ∈ targets.filter (fun b ↦ ZCompatible component shape fourthLeftTag mu b f)} ≃
      {g : Fin N → Fin k // assignmentCompatible shape mu n f g} := by
  classical
  let F : {b : Fin R // b ∈ targets.filter (fun b ↦ ZCompatible component shape fourthLeftTag mu b f)} →
      {g : Fin N → Fin k // assignmentCompatible shape mu n f g} := fun b ↦
    ⟨component b.val, (assignment_iff_indexed component shape mu n b.val f
      (hn b.val (Finset.mem_filter.mp b.property).1)).mpr (Finset.mem_filter.mp b.property).2⟩
  apply Equiv.ofBijective F
  constructor
  · intro b b' he
    apply Subtype.ext
    exact hinj (Finset.mem_filter.mp b.property).1 (Finset.mem_filter.mp b'.property).1
      (congrArg Subtype.val he)
  · intro g
    obtain ⟨b,hb,hbg⟩ := hcomplete g.val g.property.1
    have hbc : ZCompatible component shape fourthLeftTag mu b f :=
      (assignment_iff_indexed component shape mu n b f (hn b hb)).mp (hbg.symm ▸ g.property)
    refine ⟨⟨b,Finset.mem_filter.mpr ⟨hb,hbc⟩⟩,?_⟩
    exact Subtype.ext hbg

theorem indexed_compatible_count {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (targets : Finset (Fin R))
    (hn : ∀ b ∈ targets, ∀ c, Fintype.card {t : Fin N // component b t = c} = n c)
    (hinj : Set.InjOn component (targets : Set (Fin R)))
    (hcomplete : ∀ g : Fin N → Fin k,
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) →
      ∃ b ∈ targets, component b = g)
    (j : Fin R) (hj : j ∈ targets) (f : FineWord 3 N)
    (hg : Graded component shape j 2 f) (hp : Profile component fourthLeftTag mu j 2 f) :
    (targets.filter (fun b ↦ ZCompatible component shape fourthLeftTag mu b f)).card =
      compatibilityCount shape coarse mu n := by
  classical
  have hc := Nat.card_congr (compatibleTargetEquiv component shape mu n targets f hn hinj hcomplete)
  rw [assignment_count_of_useful component shape coarse hshape mu n j f (hn j hj) hg hp] at hc
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc

theorem indexed_compatible_excluding_owner_count {N k R : ℕ}
    (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (targets : Finset (Fin R))
    (hn : ∀ b ∈ targets, ∀ c, Fintype.card {t : Fin N // component b t = c} = n c)
    (hinj : Set.InjOn component (targets : Set (Fin R)))
    (hcomplete : ∀ g : Fin N → Fin k,
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) →
      ∃ b ∈ targets, component b = g)
    (j : Fin R) (hj : j ∈ targets) (f : FineWord 3 N)
    (hg : Graded component shape j 2 f) (hp : Profile component fourthLeftTag mu j 2 f) :
    (targets.filter (fun b ↦ b ≠ j ∧ ZCompatible component shape fourthLeftTag mu b f)).card =
      compatibilityCount shape coarse mu n - 1 := by
  classical
  have hjc : ZCompatible component shape fourthLeftTag mu j f :=
    ⟨hg,fun c _ l ↦ hp c l⟩
  have he : targets.filter (fun b ↦ b ≠ j ∧ ZCompatible component shape fourthLeftTag mu b f) =
      (targets.filter (fun b ↦ ZCompatible component shape fourthLeftTag mu b f)).erase j := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  rw [he, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hj,hjc⟩),
    indexed_compatible_count component shape coarse hshape mu n targets hn hinj hcomplete j hj f hg hp]

theorem uniform_hzCard {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (targets : Finset (Fin R))
    (hn : ∀ b ∈ targets, ∀ c, Fintype.card {t : Fin N // component b t = c} = n c)
    (hinj : Set.InjOn component (targets : Set (Fin R)))
    (hcomplete : ∀ g : Fin N → Fin k,
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) →
      ∃ b ∈ targets, component b = g) :
    ∀ j ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape j 2 f ∧ Profile component fourthLeftTag mu j 2 f →
      (targets.filter (fun b ↦ b ≠ j ∧ ZCompatible component shape fourthLeftTag mu b f)).card ≤
        compatibilityCount shape coarse mu n - 1 := by
  intro j hj f hf
  exact (indexed_compatible_excluding_owner_count component shape coarse hshape mu n
    targets hn hinj hcomplete j hj f hf.1 hf.2).le

end MME.DWZActualFineZCompatibility

open BigOperators MME.CompleteSplit MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZActualFineZCompatibility

theorem exists_prescribed_assignment {A L : Type*} [Fintype A] [DecidableEq A]
    [Fintype L] [DecidableEq L] (counts : L → ℕ)
    (hsum : (∑ l, counts l) = Fintype.card A) :
    ∃ g : A → L, ∀ l, Fintype.card {a : A // g a = l} = counts l := by
  classical
  have hc := mme_fintype_prescribed_fiber_function_card (α := A) counts hsum
  have hpos : 0 < Fintype.card
      {g : A → L // ∀ l, Fintype.card {a : A // g a = l} = counts l} := by
    rw [hc, ← hsum]
    exact Nat.multinomial_pos Finset.univ counts
  obtain ⟨g⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨g.val,g.property⟩

theorem useful_fine_exists {N k R : ℕ} (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (j : Fin R) (hn : ∀ c, Fintype.card {t : Fin N // component j t = c} = n c)
    (hrows : ∀ c, (∑ l, mu 2 c l) = n c)
    (hreal : ∀ c l, 0 < mu 2 c l → ∃ v : CompleteWord 3,
      (∑ r, (v r).val) = shape c 2 ∧ fourthLeftTag v = l) :
    ∃ f : FineWord 3 N, Graded component shape j 2 f ∧
      Profile component fourthLeftTag mu j 2 f := by
  classical
  have hassign (c : Fin k) : ∃ g : {t : Fin N // component j t = c} → Fin 5,
      ∀ l, Fintype.card {t // g t = l} = mu 2 c l := by
    have hsum : (∑ l, mu 2 c l) = Fintype.card {t : Fin N // component j t = c} :=
      (hrows c).trans (hn c).symm
    obtain ⟨g,hg⟩ := exists_prescribed_assignment
      (A := {t : Fin N // component j t = c}) (mu 2 c) hsum
    exact ⟨g,hg⟩
  let localTag := fun c ↦ Classical.choose (hassign c)
  let tag : Fin N → Fin 5 := fun t ↦ localTag (component j t) ⟨t,rfl⟩
  have htag (c : Fin k) (t : {t : Fin N // component j t = c}) : tag t.val = localTag c t := by
    rcases t with ⟨t,ht⟩
    cases ht
    rfl
  have hcounts (c : Fin k) (l : Fin 5) :
      Fintype.card {t : Fin N // component j t = c ∧ tag t = l} = mu 2 c l := by
    let e : {t : Fin N // component j t = c ∧ tag t = l} ≃
        {t : {t : Fin N // component j t = c} // localTag c t = l} := {
      toFun := fun t ↦ ⟨⟨t.val,t.property.1⟩,
        (htag c ⟨t.val,t.property.1⟩).symm.trans t.property.2⟩
      invFun := fun t ↦ ⟨t.val.val,t.val.property,(htag c t.val).trans t.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    exact (Fintype.card_congr e).trans (Classical.choose_spec (hassign c) l)
  have hpos (t : Fin N) : 0 < mu 2 (component j t) (tag t) := by
    rw [← hcounts]
    exact Fintype.card_pos_iff.mpr ⟨⟨t,rfl,rfl⟩⟩
  have hv (t : Fin N) := hreal (component j t) (tag t) (hpos t)
  let f : FineWord 3 N := fun t ↦ Classical.choose (hv t)
  refine ⟨f,fun t ↦ (Classical.choose_spec (hv t)).1,?_⟩
  intro c l
  calc
    _ = Fintype.card {t : Fin N // component j t = c ∧ tag t = l} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro t
      rw [(Classical.choose_spec (hv t)).2]
    _ = _ := hcounts c l

end MME.DWZActualFineZCompatibility

open BigOperators MME.CompleteSplit MME.DWZSimultaneous
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace MME.DWZQ5ExactData

theorem fourth_split_realization : ∀ (K : Fin 9) (a : Fin 5),
    a.val ≤ K.val ∧ K.val ≤ a.val + 4 →
    ∃ v : CompleteWord 3,
      (∑ r, (v r).val) = K.val ∧ fourthLeftTag v = a := by
  decide

end MME.DWZQ5ExactData

open BigOperators MME.CompleteSplit MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

namespace MME.DWZActualFineZCompatibility

theorem compatibilityCount_inline {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ) :
    compatibilityCount shape coarse mu n =
    let Boundary := fun c ↦ shape c 0 = 0 ∨ shape c 1 = 0
    let F : Fin 9 × Fin 5 → ℕ := fun i ↦
      ∑ c : {c : Fin k // coarse c = i.1}, mu 2 c.val i.2
    let collapse : Fin k → Fin k ⊕ Fin 9 := fun c ↦
      if Boundary c then Sum.inl c else Sum.inr (coarse c)
    let mass : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ
      | (Sum.inl c, (g,l)) => if Boundary c ∧ coarse c = g then mu 2 c l else 0
      | (Sum.inr g', (g,l)) => if g' = g then F (g,l) -
          ∑ c ∈ Finset.univ.filter (fun c ↦ Boundary c ∧ coarse c = g), mu 2 c l
        else 0
    let W : ℕ :=
      (∏ i : Fin 9 × Fin 5, (F i).factorial /
        ∏ di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
          (mass di.val).factorial) *
      (∏ d : Fin k ⊕ Fin 9, (∑ i, mass (d,i)).factorial /
        ∏ c : {c : Fin k // collapse c = d}, (n c.val).factorial)
    W := by
  classical
  dsimp only
  unfold compatibilityCount
  apply congrArg₂ Nat.mul
  · apply Finset.prod_congr rfl
    intro i _
    apply congrArg₂ Nat.div
    · rfl
    · apply Finset.prod_congr
      · ext di
        simp only [Finset.mem_univ]
      · intro di _
        apply congrArg Nat.factorial
        rcases di with ⟨⟨d,g,l⟩,hi⟩
        cases d <;> simp only [pooledMass, boundary, fineMass]
        all_goals split_ifs
        all_goals try rfl
        all_goals
          apply congrArg₂ Nat.sub
          · apply Finset.sum_congr
            · ext c
              simp
            · intro c _
              rfl
          · apply Finset.sum_congr
            · ext c
              simp
            · intro c _
              rfl
  · apply Finset.prod_congr rfl
    intro d _
    apply congrArg₂ Nat.div
    · apply congrArg Nat.factorial
      apply Finset.sum_congr rfl
      rintro ⟨g,l⟩ _
      cases d <;> simp only [pooledMass, boundary, fineMass]
      all_goals split_ifs
      all_goals try rfl
      all_goals
        apply congrArg₂ Nat.sub
        · apply Finset.sum_congr
          · ext c
            simp
          · intro c _
            rfl
        · apply Finset.sum_congr
          · ext c
            simp
          · intro c _
            rfl
    · let e : {c : Fin k // collapse shape coarse c = d} ≃
          {c : Fin k // (if shape c 0 = 0 ∨ shape c 1 = 0 then Sum.inl c else Sum.inr (coarse c)) = d} :=
        Equiv.subtypeEquivRight (fun c ↦ by
          by_cases hb : shape c 0 = 0 ∨ shape c 1 = 0 <;> simp only [collapse, boundary, hb, if_true, if_false])
      exact Fintype.prod_equiv e _ _ (fun _ ↦ rfl)

end MME.DWZActualFineZCompatibility

theorem solution {N k R : ℕ}
    (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (targets : Finset (Fin R))
    (hn : ∀ b ∈ targets, ∀ c, Fintype.card {t : Fin N // component b t = c} = n c)
    (hinj : Set.InjOn component (targets : Set (Fin R)))
    (hcomplete : ∀ g : Fin N → Fin k,
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) →
      ∃ b ∈ targets, component b = g)
    (hrows : ∀ c, (∑ l, mu 2 c l) = n c)
    (hsupport : ∀ c l, 0 < mu 2 c l →
      l.val ≤ (coarse c).val ∧ (coarse c).val ≤ l.val + 4) :
    let Boundary := fun c ↦ shape c 0 = 0 ∨ shape c 1 = 0
    let F : Fin 9 × Fin 5 → ℕ := fun i ↦
      ∑ c : {c : Fin k // coarse c = i.1}, mu 2 c.val i.2
    let collapse : Fin k → Fin k ⊕ Fin 9 := fun c ↦
      if Boundary c then Sum.inl c else Sum.inr (coarse c)
    let mass : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ
      | (Sum.inl c, (g,l)) => if Boundary c ∧ coarse c = g then mu 2 c l else 0
      | (Sum.inr g', (g,l)) => if g' = g then F (g,l) -
          ∑ c ∈ Finset.univ.filter (fun c ↦ Boundary c ∧ coarse c = g), mu 2 c l
        else 0
    let W : ℕ :=
      (∏ i : Fin 9 × Fin 5, (F i).factorial /
        ∏ di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
          (mass di.val).factorial) *
      (∏ d : Fin k ⊕ Fin 9, (∑ i, mass (d,i)).factorial /
        ∏ c : {c : Fin k // collapse c = d}, (n c.val).factorial)
    (∀ j ∈ targets, ∃ f : FineWord 3 N,
      Graded component shape j 2 f ∧ Profile component fourthLeftTag mu j 2 f) ∧
    ∀ j ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape j 2 f ∧ Profile component fourthLeftTag mu j 2 f →
      (∀ g : Fin 9, ∀ l : Fin 5,
        Fintype.card {t : Fin N // (∑ r, (f t r).val) = g.val ∧ fourthLeftTag (f t) = l} = F (g,l)) ∧
      (∀ b : Fin R, ZCompatible component shape fourthLeftTag mu b f ↔
        Graded component shape b 2 f ∧
        (∀ g : Fin 9, ∀ l : Fin 5,
          Fintype.card {t : Fin N // shape (component b t) 2 = g.val ∧ fourthLeftTag (f t) = l} = F (g,l)) ∧
        ∀ c, Boundary c → ∀ l,
          Fintype.card {t : Fin N // component b t = c ∧ fourthLeftTag (f t) = l} = mu 2 c l) ∧
      (targets.filter (fun b ↦ ZCompatible component shape fourthLeftTag mu b f)).card = W ∧
      (targets.filter (fun b ↦ b ≠ j ∧ ZCompatible component shape fourthLeftTag mu b f)).card = W - 1 := by
  classical
  dsimp only
  constructor
  · intro j hj
    apply MME.DWZActualFineZCompatibility.useful_fine_exists component shape mu n j (hn j hj) hrows
    intro c l hl
    obtain ⟨v,hv,htag⟩ := MME.DWZQ5ExactData.fourth_split_realization (coarse c) l (hsupport c l hl)
    exact ⟨v,hv.trans (hshape c),htag⟩
  · intro j hj f hf
    refine ⟨?_,?_,?_,?_⟩
    · intro g l
      have h := MME.DWZActualFineZCompatibility.useful_fine_histogram
        component shape coarse hshape mu j f hf.1 hf.2 (g,l)
      calc
        _ = Fintype.card {t : Fin N // MME.DWZActualFineZCompatibility.fineLabel f t = (g,l)} := by
          apply Fintype.card_congr
          apply Equiv.subtypeEquivRight
          intro t
          constructor
          · rintro ⟨ht,hl⟩
            exact Prod.ext (Fin.ext ht) hl
          · intro ht
            exact ⟨congrArg Fin.val (congrArg Prod.fst ht),congrArg Prod.snd ht⟩
        _ = _ := h
    · intro b
      constructor
      · intro hb
        exact ⟨hb.1,
          fun g l ↦ MME.DWZActualFineZCompatibility.aggregate_of_useful
            component shape coarse hshape mu j b f hf.1 hf.2 hb.1 g l,
          hb.2⟩
      · intro hb
        exact ⟨hb.1,hb.2.2⟩
    · exact (MME.DWZActualFineZCompatibility.indexed_compatible_count
        component shape coarse hshape mu n targets hn hinj hcomplete j hj f hf.1 hf.2).trans
        (MME.DWZActualFineZCompatibility.compatibilityCount_inline shape coarse mu n)
    · exact (MME.DWZActualFineZCompatibility.indexed_compatible_excluding_owner_count
        component shape coarse hshape mu n targets hn hinj hcomplete j hj f hf.1 hf.2).trans
        (congrArg (fun w : ℕ ↦ w - 1)
          (MME.DWZActualFineZCompatibility.compatibilityCount_inline shape coarse mu n))
