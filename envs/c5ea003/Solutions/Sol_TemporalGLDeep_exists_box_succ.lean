-- Prove2me | solution 1 for TemporalGLDeep.exists_box_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T02:07:28.891427+00:00
-- url     : https://prove2.me/submissions/e6810c02-5b7f-4751-be6b-a2eacc25eefc

import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGLCompleteness
import Definitions.Def_Logic_PosetTheory_TemporalGLDeduction
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax

open TemporalGLDeep
open TemporalGL

set_option maxHeartbeats 1000000 in


-- Plumbing: monotonicity of the provability box, and implication chaining.
set_option maxHeartbeats 1000000 in
theorem sol_boxMono {X Y : TForm} (h : Derivable (X ⟹ Y)) : Derivable ((◻X) ⟹ ◻Y) :=
  Derivable.mp Derivable.boxK (Derivable.boxNec h)

set_option maxHeartbeats 1000000 in
theorem sol_impTrans {X Y Z : TForm} (h1 : Derivable (X ⟹ Y)) (h2 : Derivable (Y ⟹ Z)) :
    Derivable (X ⟹ Z) :=
  Derivable.mp (Derivable.mp
    (Derivable.taut (fun v => by simp only [evalProp]; intro a b c; exact b (a c))) h1) h2

-- GL proves its own transitivity axiom.  Auxiliary formula: C := A ∧ ◻A.
set_option maxHeartbeats 1000000 in
theorem sol_derivable_four (A : TForm) : Derivable ((◻A) ⟹ ◻◻A) := by
  have h1 : Derivable (TForm.and A (◻A) ⟹ A) :=
    Derivable.taut (fun v => by simp only [evalProp, TForm.and]; tauto)
  have h2 : Derivable (TForm.and A (◻A) ⟹ (◻A)) :=
    Derivable.taut (fun v => by simp only [evalProp, TForm.and]; tauto)
  -- ◻C ⟹ ◻A  and  ◻C ⟹ ◻◻A
  have h3 : Derivable ((◻(TForm.and A (◻A))) ⟹ (◻A)) := sol_boxMono h1
  have h4 : Derivable ((◻(TForm.and A (◻A))) ⟹ ◻◻A) := sol_boxMono h2
  -- A ⟹ (◻C ⟹ C), using h3
  have h5 : Derivable (A ⟹ ((◻(TForm.and A (◻A))) ⟹ TForm.and A (◻A))) :=
    Derivable.mp
      (Derivable.taut (fun v => by simp only [evalProp, TForm.and]; tauto)) h3
  -- box it, then Löb
  have h6 : Derivable ((◻A) ⟹ ◻((◻(TForm.and A (◻A))) ⟹ TForm.and A (◻A))) := sol_boxMono h5
  have h7 : Derivable ((◻A) ⟹ ◻(TForm.and A (◻A))) := sol_impTrans h6 Derivable.loeb
  exact sol_impTrans h7 h4
set_option maxHeartbeats 1000000 in
theorem sol_boxDist : ∀ (Γ : List TForm) (X : TForm),
    Derivable ((◻(implFold Γ X)) ⟹ implFold (Γ.map TForm.box) (◻X)) := by
  intro Γ
  induction Γ with
  | nil =>
      intro X
      exact Derivable.taut (fun v => by simp only [evalProp, implFold, List.map_nil]; exact id)
  | cons Y Γ ih =>
      intro X
      have hK : Derivable ((◻(Y ⟹ implFold Γ X)) ⟹ ((◻Y) ⟹ ◻(implFold Γ X))) :=
        Derivable.boxK
      have hih := ih X
      refine Derivable.mp (Derivable.mp (Derivable.taut (fun v => ?_)) hK) hih
      simp only [evalProp, implFold, List.map_cons]
      intro hk hi hbox hby
      exact hi (hk hbox hby)

-- Necessitation for a whole hypothesis list.
set_option maxHeartbeats 1000000 in
theorem sol_derNec {Γ : List TForm} {X : TForm} (h : Der Γ X) :
    Der (Γ.map TForm.box) (◻X) :=
  Derivable.mp (sol_boxDist Γ X) (Derivable.boxNec h)
set_option maxHeartbeats 1000000 in
theorem sol_implFold_append : ∀ (Γ Δ : List TForm) (X : TForm),
    implFold (Γ ++ Δ) X = implFold Γ (implFold Δ X) := by
  intro Γ
  induction Γ with
  | nil => intro Δ X; rfl
  | cons Y Γ ih => intro Δ X; simp only [List.cons_append, implFold, ih]

-- Cut: extra hypotheses that are themselves derivable can be discharged.
set_option maxHeartbeats 1000000 in
theorem sol_der_cut : ∀ (Δ : List TForm) {Γ : List TForm} {X : TForm},
    Der (Γ ++ Δ) X → (∀ y ∈ Δ, Der Γ y) → Der Γ X := by
  intro Δ
  induction Δ with
  | nil => intro Γ X h _; simpa using h
  | cons Y Δ ih =>
      intro Γ X h hall
      refine ih (Γ := Γ) (X := X) ?_ (fun y hy => hall y (List.mem_cons_of_mem _ hy))
      have h' : Der Γ (implFold (Y :: Δ) X) := by
        rw [Der, ← sol_implFold_append]; exact h
      have hY : Der Γ Y := hall Y (by simp)
      have h2 : Der Γ (implFold Δ X) := Der_mp (by rw [Der]; exact h') hY
      rw [Der, sol_implFold_append]; exact h2

-- Membership facts for `boxList`, and that its members are literally boxes.
set_option maxHeartbeats 1000000 in
theorem sol_mem_boxList {Cl t : Finset TForm} {C : TForm} (h : C ∈ boxList Cl t) :
    C ∈ Cl ∧ C ∈ t ∧ C.isBox = true := by
  rw [boxList, List.mem_filter] at h
  obtain ⟨h1, h2⟩ := h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h2
  exact ⟨Finset.mem_toList.1 h1, h2.2, h2.1⟩

set_option maxHeartbeats 1000000 in
theorem sol_box_unbox_of_isBox {C : TForm} (h : C.isBox = true) : TForm.box (TForm.unbox C) = C := by
  cases C with
  | box D => rfl
  | atom p => simp [TForm.isBox] at h
  | bot => simp [TForm.isBox] at h
  | imp D E => simp [TForm.isBox] at h
  | glob D => simp [TForm.isBox] at h
set_option maxHeartbeats 1000000 in


-- Weakening: more hypotheses can only help.
set_option maxHeartbeats 1000000 in
theorem sol_der_weaken {Γ Γ' : List TForm} {X : TForm} (hsub : ∀ x ∈ Γ, x ∈ Γ')
    (h : Der Γ X) : Der Γ' X := by
  refine Derivable.mp (Derivable.taut (fun v => ?_)) h
  show evalProp v (implFold Γ X) → evalProp v (implFold Γ' X)
  intro hΓ
  refine (evalProp_implFold v Γ' X).2 (fun hall => ?_)
  exact (evalProp_implFold v Γ X).1 hΓ (fun x hx => hall x (hsub x hx))

-- Consistency of a longer list gives consistency of the prefix.
set_option maxHeartbeats 1000000 in
theorem sol_listCons_of_append {Γ Δ : List TForm} (h : ListCons (Γ ++ Δ)) : ListCons Γ :=
  fun hd => h (sol_der_weaken (fun x hx => List.mem_append_left _ hx) hd)

-- The case split (probed already, restated here as a named lemma).
set_option maxHeartbeats 1000000 in
theorem sol_listCons_cases {Γ : List TForm} (X : TForm) (hc : ListCons Γ) :
    ListCons (X :: Γ) ∨ ListCons (X.neg :: Γ) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨n1, n2⟩ := hcon
  rw [ListCons, not_not] at n1 n2
  refine hc ?_
  have key : Taut ((implFold (X :: Γ) TForm.bot) ⟹
      ((implFold (X.neg :: Γ) TForm.bot) ⟹ implFold Γ TForm.bot)) := by
    intro v
    simp only [evalProp, implFold, TForm.neg]
    intro ha hb
    by_cases hx : evalProp v X
    · exact ha hx
    · exact hb (fun hX => absurd hX hx)
  exact Derivable.mp (Derivable.mp (Derivable.taut key) n1) n2

-- THE CRUX: decide every formula of a duplicate-free list, keeping Γ₀ consistent.
set_option maxHeartbeats 1000000 in
theorem sol_build (Γ₀ : List TForm) (h0 : ListCons Γ₀) :
    ∀ L : List TForm, L.Nodup →
      ∃ f : TForm → Bool,
        ListCons ((L.map (fun B => if f B then B else B.neg)) ++ Γ₀) := by
  intro L
  induction L with
  | nil => exact fun _ => ⟨fun _ => true, by simpa using h0⟩
  | cons X L ih =>
      intro hnd
      obtain ⟨hXL, hndL⟩ := List.nodup_cons.1 hnd
      obtain ⟨f, hf⟩ := ih hndL
      rcases sol_listCons_cases X hf with h | h
      · refine ⟨Function.update f X true, ?_⟩
        have hmap : (L.map (fun B => if Function.update f X true B then B else B.neg))
            = L.map (fun B => if f B then B else B.neg) := by
          refine List.map_congr_left (fun B hB => ?_)
          rw [Function.update_of_ne (by rintro rfl; exact hXL hB)]
        simpa [hmap, Function.update_self] using h
      · refine ⟨Function.update f X false, ?_⟩
        have hmap : (L.map (fun B => if Function.update f X false B then B else B.neg))
            = L.map (fun B => if f B then B else B.neg) := by
          refine List.map_congr_left (fun B hB => ?_)
          rw [Function.update_of_ne (by rintro rfl; exact hXL hB)]
        simpa [hmap, Function.update_self] using h

-- THE MODAL CORE: the successor-witness set is consistent.
set_option maxHeartbeats 2000000 in
theorem sol_loeb_step {Cl t : Finset TForm} (hcons : Cons Cl t) {B : TForm}
    (hBCl : (◻B) ∈ Cl) (hBt : (◻B) ∉ t) :
    ListCons (B.neg :: (((boxList Cl t).map TForm.unbox ++ boxList Cl t) ++ [◻B])) := by
  set Lb := boxList Cl t with hLb
  set Lu := Lb.map TForm.unbox with hLu
  intro hder
  -- (a) from inconsistency with ¬B, derive B
  have ha : Der ((Lu ++ Lb) ++ [◻B]) B := by
    refine Derivable.mp (Derivable.taut (fun v => ?_)) hder
    simp only [evalProp, implFold, TForm.neg]
    intro h
    rw [evalProp_implFold]
    intro hall
    by_contra hb
    exact (evalProp_implFold v ((Lu ++ Lb) ++ [◻B]) TForm.bot).1 (h hb) hall
  -- (b) move the boxed hypothesis into the conclusion
  have hb : Der (Lu ++ Lb) ((◻B) ⟹ B) := by
    have hre : implFold ((Lu ++ Lb) ++ [◻B]) B = implFold (Lu ++ Lb) ((◻B) ⟹ B) := by
      rw [sol_implFold_append]
      rfl
    rw [Der, ← hre]; exact ha
  -- (c) necessitate the whole list
  have hc : Der ((Lu ++ Lb).map TForm.box) (◻((◻B) ⟹ B)) := sol_derNec hb
  have hmap : (Lu ++ Lb).map TForm.box = Lb ++ Lb.map TForm.box := by
    rw [List.map_append]
    congr 1
    have h2 : Lb.map (TForm.box ∘ TForm.unbox) = Lb.map id :=
      List.map_congr_left (fun C hC => sol_box_unbox_of_isBox (sol_mem_boxList hC).2.2)
    rw [hLu, List.map_map, h2, List.map_id]
  rw [hmap] at hc
  -- (d) Löb
  have hd : Der (Lb ++ Lb.map TForm.box) (◻B) :=
    Der_mp (Der_of_derivable Derivable.loeb) hc
  -- (e) discharge the doubly-boxed hypotheses using GL's own 4
  have he : Der Lb (◻B) := by
    refine sol_der_cut (Lb.map TForm.box) hd (fun y hy => ?_)
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hy
    have hbox : TForm.box (TForm.unbox C) = C := sol_box_unbox_of_isBox (sol_mem_boxList hC).2.2
    have h4 : Derivable (C ⟹ ◻C) := by
      have := sol_derivable_four (TForm.unbox C)
      rwa [hbox] at this
    exact Der_mp (Der_of_derivable h4) (Der_of_mem hC)
  -- (f) every boxed member of t is asserted in gammaList, so ◻B ∈ t — contradiction
  have hfin : Der (gammaList Cl t) (◻B) :=
    sol_der_weaken (fun x hx => by
      obtain ⟨h1, h2, _⟩ := sol_mem_boxList hx
      exact mem_gammaList_pos h1 h2) he
  exact hBt (mem_of_Der hcons hBCl hfin)

-- Two contradictory formulas cannot both sit in a consistent list.
set_option maxHeartbeats 1000000 in
theorem sol_not_listCons_of_mem_neg {L : List TForm} {X : TForm} (h1 : X ∈ L) (h2 : X.neg ∈ L) :
    ¬ ListCons L := fun hc => hc (Der_mp (Der_of_mem h2) (Der_of_mem h1))

set_option maxHeartbeats 1000000 in
theorem sol_mem_of_constraint {Cl s : Finset TForm} {Γ₀ : List TForm} {X : TForm}
    (hcl : ListCons (gammaList Cl s ++ Γ₀)) (hXCl : X ∈ Cl) (hXΓ : X ∈ Γ₀) : X ∈ s := by
  by_contra hns
  exact sol_not_listCons_of_mem_neg (List.mem_append_right _ hXΓ)
    (List.mem_append_left _ (mem_gammaList_neg hXCl hns)) hcl

set_option maxHeartbeats 1000000 in
theorem sol_not_mem_of_constraint {Cl s : Finset TForm} {Γ₀ : List TForm} {X : TForm}
    (hcl : ListCons (gammaList Cl s ++ Γ₀)) (hXCl : X ∈ Cl) (hXΓ : X.neg ∈ Γ₀) : X ∉ s := by
  intro hs
  exact sol_not_listCons_of_mem_neg (List.mem_append_left _ (mem_gammaList_pos hXCl hs))
    (List.mem_append_right _ hXΓ) hcl

set_option maxHeartbeats 4000000 in
open TemporalGLDeep TemporalGL in
theorem solution {Cl : Finset TForm} (hCl : Closed Cl) {t : Finset TForm}
    (hcons : Cons Cl t) {B : TForm} (hB : (◻B) ∈ Cl) (hnot : (◻B) ∉ t) :
    ∃ s, s ∈ CanW Cl ∧ filtR Cl t s ∧ B ∉ s := by
  classical
  set Lb := boxList Cl t with hLb
  set Lu := Lb.map TForm.unbox with hLu
  set G0 : List TForm := B.neg :: ((Lu ++ Lb) ++ [◻B]) with hG0
  have hG0cons : ListCons G0 := sol_loeb_step hcons hB hnot
  obtain ⟨f, hf⟩ := sol_build G0 hG0cons Cl.toList Cl.nodup_toList
  set s : Finset TForm := Cl.filter (fun Y => f Y = true) with hs
  have hmem_s : ∀ X, X ∈ s ↔ (X ∈ Cl ∧ f X = true) := by
    intro X; rw [hs]; exact Finset.mem_filter
  have hgamma : gammaList Cl s = Cl.toList.map (fun X => if f X then X else X.neg) := by
    unfold gammaList
    refine List.map_congr_left (fun X hX => ?_)
    have hXCl : X ∈ Cl := Finset.mem_toList.1 hX
    by_cases hfx : f X = true
    · rw [if_pos ((hmem_s X).2 ⟨hXCl, hfx⟩), if_pos hfx]
    · rw [if_neg (fun hm => hfx ((hmem_s X).1 hm).2), if_neg hfx]
  have hcl : ListCons (gammaList Cl s ++ G0) := by rw [hgamma]; exact hf
  -- membership of a boxed formula of t in the constraint list
  have hbox_mem : ∀ C, (◻C) ∈ Cl → (◻C) ∈ t → (◻C) ∈ Lb := by
    intro C h1 h2
    rw [hLb, boxList]
    exact List.mem_filter.2 ⟨Finset.mem_toList.2 h1, by simp [TForm.isBox, h2]⟩
  refine ⟨s, mem_CanW.2 ⟨?_, sol_listCons_of_append hcl⟩,
    ⟨fun C hCCl hCt => ⟨?_, ?_⟩, ⟨B, hB, ?_, hnot⟩⟩, ?_⟩
  · rw [hs]; exact Finset.filter_subset _ _
  · refine sol_mem_of_constraint hcl (hCl.box hCCl) ?_
    refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ ?_))
    rw [hLu]
    exact List.mem_map.2 ⟨◻C, hbox_mem C hCCl hCt, rfl⟩
  · refine sol_mem_of_constraint hcl hCCl ?_
    exact List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_append_right _ (hbox_mem C hCCl hCt)))
  · refine sol_mem_of_constraint hcl hB ?_
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp))
  · exact sol_not_mem_of_constraint hcl (hCl.box hB) (by rw [hG0]; exact List.mem_cons_self ..)
