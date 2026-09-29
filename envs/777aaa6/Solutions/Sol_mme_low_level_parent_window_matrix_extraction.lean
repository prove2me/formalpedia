-- Prove2me | solution 1 for mme_low_level_parent_window_matrix_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T12:20:02.360068+00:00
-- url     : https://prove2.me/submissions/b8cbf31a-c594-4f62-8ddf-30c0c9f494db

import Theorems.Thm_mme_logarithmic_regional_recipe_compilation
import Theorems.Thm_mme_entropy_regional_recipe_compilation
import Theorems.Thm_mme_integer_regional_recipe_compilation
import Theorems.Thm_mme_recursive_regional_CW_plan_sound
import Definitions.Def_mme_logarithmic_regional_CW_recipe
import Definitions.Def_mme_regional_tolerance_window_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false

private theorem word_grade_zero {ell : ℕ} (s : CompleteWord ell)
    (h : CWCells.grade s = 0) : s = fun _ ↦ 0 := by
  funext r
  apply Fin.ext
  have hh : ∀ r, (s r).val = 0 := by
    simpa [CWCells.grade] using (Finset.sum_eq_zero_iff_of_nonneg
      (fun r (_ : r ∈ (Finset.univ : Finset (Fin (2 ^ (ell - 1))))) ↦ Nat.zero_le (s r).val)).mp h
  exact hh r

private theorem zero_profile {ell L : ℕ} (mu : CompleteWord ell → ℕ)
    (hmass : ∑ s, mu s = L)
    (hgrade : ∀ s, 0 < mu s → CWCells.grade s = 0) :
    mu = fun s ↦ if s = (fun _ ↦ 0) then L else 0 := by
  classical
  have hs (s : CompleteWord ell) (h : s ≠ fun _ ↦ 0) : mu s = 0 := by
    by_contra hn
    exact h (word_grade_zero s (hgrade s (Nat.pos_of_ne_zero hn)))
  have hz : mu (fun _ ↦ 0) = L := by
    calc
      mu (fun _ ↦ 0) = ∑ s, mu s := (Finset.sum_eq_single (fun _ ↦ 0)
        (fun s _ h ↦ hs s h) (by simp)).symm
      _ = L := hmass
  funext s
  by_cases h : s = fun _ ↦ 0
  · simp [h, hz]
  · simp [h, hs s h]

private theorem flipLabel_eq_rev {ell : ℕ} (s : CompleteWord ell) :
    flipLabel s = fun r ↦ Fin.rev (s r) := by
  funext r
  apply Fin.ext
  simp [flipLabel, Fin.rev]

/-- An exact complementary profile is determined by mass and grade support. -/
theorem mme_boundary_profile_of_histogram_support
    (ell L : ℕ) (shape : Fin 3 → ℕ) (mu : Fin 3 → CompleteWord ell → ℕ)
    (ht : shape 0 + shape 1 + shape 2 = 2 * 2 ^ (ell - 1))
    (hm : ∀ i, ∑ s, mu i s = L)
    (hg : ∀ i s, 0 < mu i s → grade s = shape i)
    (hboundary :
      (shape 2 = 0 → ∀ s, mu 1 s = mu 0 (fun r ↦ Fin.rev (s r))) ∧
      (shape 0 = 0 → ∀ s, mu 2 s = mu 1 (fun r ↦ Fin.rev (s r))) ∧
      (shape 1 = 0 → ∀ s, mu 2 s = mu 0 (fun r ↦ Fin.rev (s r))))
    (z : Fin 3) (hz : shape z = 0) :
    ∃ B : Boundary.Profile ell L,
      (∀ i, shape i = B.shape z i) ∧ (∀ i, mu i = B.mu z i) := by
  classical
  have hb (i : Fin 3) : shape i ≤ 2 * 2 ^ (ell - 1) := by
    fin_cases i <;> dsimp <;> omega
  have hzero : mu z = fun s ↦ if s = (fun _ ↦ 0) then L else 0 :=
    zero_profile _ (hm z) (fun s hs ↦ (hg z s hs).trans hz)
  have hrevs (s : CompleteWord ell) :
      flipLabel (flipLabel s) = s := by
    funext r
    apply Fin.ext
    simp only [flipLabel]
    have := (s r).isLt
    omega
  fin_cases z
  · let B : Boundary.Profile ell (L) :=
      ⟨shape 1, hb 1, mu 1, hm 1,
        fun s hs ↦ hg 1 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hz
      · rfl
      · change shape 2 = 2 * 2 ^ (ell - 1) - shape 1
        change shape 0 = 0 at hz
        omega
    · intro i
      fin_cases i
      · exact hzero
      · rfl
      · funext s
        change mu 2 s = mu 1 (flipLabel s)
        rw [flipLabel_eq_rev]
        exact hboundary.2.1 hz s
  · let B : Boundary.Profile ell (L) :=
      ⟨shape 2, hb 2, mu 2, hm 2,
        fun s hs ↦ hg 2 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · change shape 0 = 2 * 2 ^ (ell - 1) - shape 2
        change shape 1 = 0 at hz
        omega
      · exact hz
      · rfl
    · intro i
      fin_cases i
      · funext s
        change mu 0 s = mu 2 (flipLabel s)
        rw [hboundary.2.2 hz, ← flipLabel_eq_rev, hrevs]
      · exact hzero
      · rfl
  · let B : Boundary.Profile ell (L) :=
      ⟨shape 0, hb 0, mu 0, hm 0,
        fun s hs ↦ hg 0 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · rfl
      · change shape 1 = 2 * 2 ^ (ell - 1) - shape 0
        change shape 2 = 0 at hz
        omega
      · exact hz
    · intro i
      fin_cases i
      · rfl
      · funext s
        change mu 1 s = mu 0 (flipLabel s)
        rw [flipLabel_eq_rev]
        exact hboundary.1 hz s
      · exact hzero


#print axioms mme_boundary_profile_of_histogram_support


open MME.RegionRealization

private theorem full_cell_fiber {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (r : Fin R)
    (c : MME.RecursiveThinSplit.Split half (parent r)) :
    Fintype.card {p : Position n // fullCell htotal a p = ⟨r,c⟩} =
      MME.RecursiveThinSplit.count (a r) c +
      MME.RecursiveThinSplit.count (a r) (complement (htotal r) c) := by
  classical
  let e : {p : Position n // fullCell htotal a p = ⟨r,c⟩} ≃
      {p : Fin (n r) × Fin 2 //
        (if p.2 = 0 then a r p.1 else complement (htotal r) (a r p.1)) = c} := {
    toFun := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨(t,h), eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun p ↦ ⟨⟨r,p.val⟩, by
      change (⟨r,_⟩ : Cell half R parent) = ⟨r,c⟩
      rw [p.property]⟩
    left_inv := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro p; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  have hc (t : Fin (n r)) : complement (htotal r) (a r t) = c ↔
      a r t = complement (htotal r) c := by
    constructor
    · intro h
      simpa only [complement_complement] using congrArg (complement (htotal r)) h
    · intro h
      rw [h, complement_complement]
  simp only [show (1 : Fin 2) ≠ 0 by decide, 
    MME.RecursiveThinSplit.count, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_add_distrib]
  simp only [ite_true, ite_false, hc]
  congr 1

private theorem count_reindex {A B C E W : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (d : C ≃ E) (cell : B → C) (f : B → W) (c : C) (w : W) :
    count (fun a ↦ d (cell (e a))) (fun a ↦ f (e a)) (d c) w =
      count cell f c w := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter, Equiv.apply_eq_iff_eq]
  exact Equiv.sum_comp e (fun b ↦ if cell b = c ∧ f b = w then 1 else 0)

/-- An integer regional step whose cells are all boundary cells has a concrete terminal
interface. The profiles and all three matrix dimensions are retained. -/
theorem mme_integer_step_boundary_end_of_zero_modes
    {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (part : Partition (fullCell D.total D.reference))
    (hz : ∀ j, ∃ z : Fin 3, ((part.cells j).2.val z).val = 0) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ B : BoundaryEnd ell M D.output,
        B.L = D.L ∧ B.a = ∏ j, (profiles j).a (z j) ∧
        B.b = ∏ j, (profiles j).b (z j) ∧
        B.c = ∏ j, (profiles j).c (z j) := by
  classical
  have htarget : ∀ r c, RecursiveThinSplit.count (D.reference r) c = D.m r c := by
    simpa only [RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ, true_and,
      RecursiveThinSplit.HasJointCounts] using D.reference_target
  have hm (j : Fin part.parts) (i : Fin 3) :
      ∑ w, D.mu i (part.cells j) w = part.size j := by
    rw [D.mass]
    have hf := full_cell_fiber D.total D.reference (part.cells j).1 (part.cells j).2
    rw [htarget, htarget] at hf
    rw [← hf, ← Fintype.card_congr (part.fiber j), Fintype.card_fin]
  choose z hz using hz
  have hp (j : Fin part.parts) : ∃ B : Boundary.Profile ell (part.size j),
      (∀ i, ((part.cells j).2.val i).val = B.shape (z j) i) ∧
      (∀ i, D.mu i (part.cells j) = B.mu (z j) i) := by
    apply mme_boundary_profile_of_histogram_support ell (part.size j)
      (fun i ↦ ((part.cells j).2.val i).val) (fun i ↦ D.mu i (part.cells j))
    · exact (part.cells j).2.property.1.trans D.half_eq
    · exact hm j
    · exact fun i w hw ↦ D.support i (part.cells j) w hw
    · exact ⟨D.boundary.1 (part.cells j), D.boundary.2.1 (part.cells j),
        D.boundary.2.2 (part.cells j)⟩
    · exact hz j
  choose profiles hsh hmu using hp
  let e := Fintype.equivFin (Cell D.half D.R D.parent)
  let cell : Fin D.L → Fin (Fintype.card (Cell D.half D.R D.parent)) :=
    fun p ↦ e (fullCell D.total D.reference (D.positions p))
  let pf (j : Fin part.parts) :
      {p : Position D.n // fullCell D.total D.reference p = part.cells j} ≃
      {p : Fin D.L // cell p = e (part.cells j)} := {
    toFun := fun p ↦ ⟨D.positions.symm p.val, by simp [cell, p.property]⟩
    invFun := fun p ↦ ⟨D.positions p.val, e.injective p.property⟩
    left_inv := by intro p; apply Subtype.ext; exact D.positions.apply_symm_apply p.val
    right_inv := by intro p; apply Subtype.ext; exact D.positions.symm_apply_apply p.val }
  let part' : Partition cell := {
    parts := part.parts
    cells := part.cells.trans e
    size := part.size
    fiber := fun j ↦ (part.fiber j).trans (pf j) }
  let B : BoundaryEnd ell M D.output := {
    L := D.L
    cells := Fintype.card (Cell D.half D.R D.parent)
    length := D.length
    cell := cell
    shape := fun c i ↦ ((e.symm c).2.val i).val
    mu := fun i c ↦ D.mu i (e.symm c)
    partition := part'
    profile := profiles
    zeroMode := z
    shapes := by
      intro j
      funext i
      exact (congrArg (fun c : Cell D.half D.R D.parent ↦ (c.2.val i).val)
        (e.symm_apply_apply (part.cells j))).trans (hsh j i)
    profiles := by intro j i; simpa [part'] using hmu j i
    inside := by
      intro i x hx
      have hs (p : Fin D.L) :
          split D.positions D.length x (D.positions p) =
            split (Equiv.refl (Fin D.L)) D.length x p := by
        funext r
        simp [split]
      refine ⟨?_, ?_⟩
      · intro p
        have hh := hx.1 (D.positions.symm p)
        have he : e.symm (cell (D.positions.symm p)) = fullCell D.total D.reference p := by
          simp [cell]
        exact hh.trans (congrArg (fun c : Cell D.half D.R D.parent ↦ (c.2.val i).val) he)
      · intro c w
        have hh := hx.2 (e c) w
        have hc := count_reindex D.positions e (fullCell D.total D.reference)
          (split D.positions D.length x) c w
        simp only [hs] at hc
        simpa only [cell, Equiv.symm_apply_apply, hc] using hh }
  exact ⟨z, profiles, hsh, hmu, B, rfl, rfl, rfl, rfl⟩

/-- Every elementary-depth integer step terminates in exact boundary profiles. -/
theorem mme_integer_step_low_level_boundary_end
    {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (hlevel : ell ≤ 1) (part : Partition (fullCell D.total D.reference)) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ B : BoundaryEnd ell M D.output,
        B.L = D.L ∧ B.a = ∏ j, (profiles j).a (z j) ∧
        B.b = ∏ j, (profiles j).b (z j) ∧
        B.c = ∏ j, (profiles j).c (z j) := by
  apply mme_integer_step_boundary_end_of_zero_modes D part
  intro j
  have ht := (part.cells j).2.property.1.trans D.half_eq
  simp only [Nat.sub_eq_zero_of_le hlevel, pow_zero, mul_one] at ht
  by_contra hn
  push_neg at hn
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  omega

#print axioms mme_integer_step_low_level_boundary_end

/-- A single elementary-depth regional extraction followed by its constructed boundary
profiles gives an logarithmic recipe with the chosen certified logarithmic rate. -/
theorem mme_integer_step_low_level_log_recipe
    {ell M upper : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (hlevel : ell ≤ 1) (hupper : ell < upper)
    (part : Partition (fullCell D.total D.reference))
    (rate : ℝ) (hrate : 0 ≤ rate) (hbudget : rate ≤ D.certifiedLogCopies) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : LogRecipe M upper P,
        E.inputs = 1 ∧ E.logOutputs = rate ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by
  obtain ⟨z, profiles, hsh, hmu, B, _, ha, hb, hc⟩ :=
    mme_integer_step_low_level_boundary_end D hlevel part
  let E : LogRecipe M upper P := LogRecipe.descend hupper 1 rate hrate
    (fun _ ↦ D) (fun _ ↦ hbudget) (fun _ _ _ h ↦ h)
    (fun _ _ hx ↦ ⟨0, hx, fun j _ ↦ Subsingleton.elim j 0⟩)
    (LogRecipe.boundary B)
  refine ⟨z, profiles, hsh, hmu, E, ?_, ?_, ?_⟩
  · rfl
  · simp [E, LogRecipe.logOutputs]
  · simp only [E, LogRecipe.dims, ha, hb, hc]

#print axioms mme_integer_step_low_level_log_recipe

/-- A single central-profile extraction gives a terminal logarithmic recipe for an
arbitrary larger parent tolerance window. Its budget is evaluated only at that profile. -/
theorem mme_low_level_parent_window_single_input_log_recipe
    {ell M upper : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (hlevel : ell ≤ 1) (hupper : ell < upper)
    (part : Partition (fullCell D.total D.reference))
    (eps eta rate : ℝ) (heps : 0 < eps) (heta : eps ≤ eta)
    (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤
        (D.minimum : ℝ) * eps^2)
    (hbudget : rate ≤ windowLogBudget D D.mu eps) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : LogRecipe M upper (parentWindow D eta),
        E.inputs = 1 ∧ E.logOutputs = rate ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by
  let S : IntegerStep ell M (parentWindow D eta) := {
    D with
    epsilon := eps
    epsilon_pos := heps
    size_test := hsize
    source_inside := by
      intro i x hx r w
      exact (hx r w).trans_le heta }
  have hb : rate ≤ S.certifiedLogCopies := by
    exact hbudget
  exact mme_integer_step_low_level_log_recipe S hlevel hupper part rate hrate hb

#print axioms mme_low_level_parent_window_single_input_log_recipe

/-- Exact boundary profiles lie inside every nonnegative child-frequency window,
so the window admits a terminal recipe with the same matrix dimensions. -/
theorem mme_integer_step_child_window_boundary_recipe
    {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (part : Partition (fullCell D.total D.reference))
    (hz : ∀ j, ∃ z : Fin 3, ((part.cells j).2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : LogRecipe M ell (childWindow D delta),
        E.inputs = 1 ∧ E.logOutputs = 0 ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by
  obtain ⟨z, profiles, hsh, hmu, B, _, ha, hb, hc⟩ :=
    mme_integer_step_boundary_end_of_zero_modes D part hz
  let B' : BoundaryEnd ell M (childWindow D delta) := {
    B with
    inside := by
      intro i x hx
      obtain ⟨hg, hu⟩ := B.inside i x hx
      refine ⟨hg, ?_⟩
      have hh : count (fullCell D.total D.reference) (split D.positions D.length x) =
          D.mu i := by
        funext c w
        exact hu c w
      intro c w
      rw [hh]
      simpa only [sub_self, abs_zero] using hdelta }
  refine ⟨z, profiles, hsh, hmu, LogRecipe.boundary B', rfl, rfl, ?_⟩
  change (B.a, B.b, B.c) = _
  rw [ha, hb, hc]

#print axioms mme_integer_step_child_window_boundary_recipe

open MME.TensorObj
universe u

/-- The elementary parent-window recipe compiles to an actual sum of matrix
multiplication tensors, with at least the exponential of the certified rate copies. -/
theorem solution
    {K : Type u} [Field K] {ell M : ℕ} {P : Predicate M}
    (D : IntegerStep ell M P) (hlevel : ell ≤ 1)
    (part : Partition (fullCell D.total D.reference))
    (eps eta rate : ℝ) (heps : 0 < eps) (heta : eps ≤ eta)
    (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤
        (D.minimum : ℝ) * eps^2)
    (hbudget : rate ≤ windowLogBudget D D.mu eps) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ k : ℕ, Real.exp rate ≤ (k : ℝ) ∧
        Restrict (bigAdd (fun _ : Fin k ↦ MMObj K
          (∏ j, (profiles j).a (z j)) (∏ j, (profiles j).b (z j))
          (∏ j, (profiles j).c (z j))))
          (bigAdd (fun _ : Fin 1 ↦ tensor K (parentWindow D eta))) := by
  obtain ⟨z, profiles, hsh, hmu, E, hi, ho, hd⟩ :=
    mme_low_level_parent_window_single_input_log_recipe D hlevel (Nat.lt_succ_self ell) part
      eps eta rate heps heta hrate hsize hbudget
  obtain ⟨A, hai, hao, had⟩ := mme_logarithmic_regional_recipe_compilation E
  obtain ⟨B, hbi, hbo, hbd⟩ := mme_entropy_regional_recipe_compilation A
  obtain ⟨C, hci, hco, hcd⟩ := mme_integer_regional_recipe_compilation B
  refine ⟨z, profiles, hsh, hmu, C.outputs, ?_, ?_⟩
  · simpa only [hco, hbo, ho] using hao
  · have h := mme_recursive_regional_CW_plan_sound (K := K) C
    have hinputs : C.inputs = 1 := hci.trans (hbi.trans (hai.trans hi))
    rw [hinputs] at h
    simpa only [RegionalPlan.a, RegionalPlan.b, RegionalPlan.c,
      hcd, hbd, had, hd] using h

#print axioms solution
