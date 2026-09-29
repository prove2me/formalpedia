-- Prove2me | solution 1 for mme_recursive_region_graded_source_exact_step_realization
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:48:52.881825+00:00
-- url     : https://prove2.me/submissions/899e66c3-7683-4868-b657-eb0f61a41f43

import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_recursive_region_computed_hash_selection
import Theorems.Thm_mme_recursive_region_derived_parent_hole_budget
import Mathlib.Data.Nat.Log

open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false

private theorem mme_exact_step_source_refinement_on_unbroken
    {ell N : ℕ} {P Q : Predicate N} (E : ExactStep ell N P)
    (hPQ : ∀ j i f, f ∈ unbrokenWords E.stage.total i (E.address j) (E.stage.mu i) →
      P i (flatten E.stage.positions E.length f) →
      Q i (flatten E.stage.positions E.length f)) :
    ∃ F : ExactStep ell N Q, F.count = E.count ∧
      F.stage.repairExponent = E.stage.repairExponent ∧
      F.copies = E.copies ∧ F.output = E.output := by
  classical
  let F : ExactStep ell N Q := {
    hash := E.hash
    stage := E.stage
    level := E.level
    length := E.length
    count := E.count
    state := E.state
    address := E.address
    injective := E.injective
    target := E.target
    bucketed := E.bucketed
    hashed := E.hashed
    isolated := E.isolated
    holes := by
      intro j i
      apply le_trans _ (E.holes j i)
      apply Nat.mul_le_mul_left
      apply Finset.card_le_card
      apply Finset.union_subset_union
      · intro f hf
        obtain ⟨hf, hnot⟩ := Finset.mem_filter.mp hf
        exact Finset.mem_filter.mpr ⟨hf, fun hp => hnot (hPQ j i f hf hp)⟩
      · exact Finset.Subset.refl _ }
  exact ⟨F,rfl,rfl,rfl,rfl⟩

private theorem split_flatten {S : Type} {ell L M : ℕ} (positions : Fin L ≃ S)
    (length : L * 2 ^ (ell - 1) = M) (f : S → CompleteSplit.CompleteWord ell) :
    ProfiledCW.split positions length (ProfiledCW.flatten positions length f) = f := by
  funext p h
  simp [ProfiledCW.split, ProfiledCW.flatten]

theorem solution {half R ell N L M : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (ell - 1) = M)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (hsupport : ∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val)
    (hboundary : BoundaryProfiles mu)
    (reference : Address half R parent n) (href : reference ∈ RecursiveXHash.target m)
    (k d : ℕ) (hk : 0 < k) (hd : 1 < d) (hkn : ∀ r, k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) ≤
      (k : ℝ) * eps ^ 2)
    (source : Predicate M)
    (hsource : ∀ i (a : Address half R parent n), a ∈ RecursiveXHash.target m →
      ∀ f : Position n → CompleteSplit.CompleteWord ell,
        Graded htotal i a f → parentTypical htotal n m (mu i) eps f →
        source i (ProfiledCW.flatten positions length f)) :
    let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
    let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
    let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
    ∃ E : ExactStep ell M source,
      ((RecursiveXHash.target (n := n) m).card : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
      E.stage.repairExponent = Nat.log d cap + 1 ∧
      E.output = fun i x ↦ Graded htotal i reference (ProfiledCW.split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (ProfiledCW.split positions length x) := by
  classical
  let P : Predicate M := fun i x ↦ parentTypical htotal n m (mu i) eps (ProfiledCW.split positions length x)
  let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
  let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
  let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
  have htype (i : Fin 3) (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m) :
      8 * d * (typeHoles htotal i a (mu i) (parentTypical htotal n m (mu i) eps)).card ≤
        (unbrokenWords htotal i a (mu i)).card :=
    mme_recursive_region_derived_parent_hole_budget parent n htotal m (mu i) (hmass i) i (hsupport i)
      k d hk hkn hdiv eps heps hscale a ha
  obtain ⟨p,hprime,hodd,hgrade,hlow,hupp,S,hSr,hSf,state,I,hIt,hIb,hIh,hIu,hIso,hIc⟩ :=
    mme_recursive_region_computed_hash_selection parent n htotal m e d (fun i ↦ mu (yzMode i))
      (fun i ↦ hmass (yzMode i)) keep (fun i a ha ↦ htype (yzMode i) a ha)
  let D : HashExtraction.HashData := {
    half := half
    R := R
    parent := parent
    n := n
    m := m
    N := N
    p := p
    prime := hprime
    odd := hodd
    grade_lt := hgrade
    positions := e
    labels := S
    labels_range := hSr
    labels_free := hSf
    good := fun state ↦ usable htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state d
      (fun i ↦ mu (yzMode i)) keep }
  let A : Stage D := {
    ell := ell
    L := L
    repairScale := d
    repairExponent := Nat.log d cap + 1
    total := htotal
    half_eq := hhalf
    positions := positions
    mu := mu
    boundary := hboundary
    mass := hmass
    reference := reference
    reference_target := href
    keep := keep
    good_eq := fun _ ↦ rfl
    capacity := Nat.lt_pow_succ_log_self hd cap }
  let address (j : Fin I.card) : Address half R parent n := (I.equivFin.symm j).val
  have hj (j : Fin I.card) : address j ∈ I := (I.equivFin.symm j).property
  have haddr : Function.Injective address := Subtype.val_injective.comp I.equivFin.symm.injective
  have hsplit (i : Fin 3) (f : Position n → CompleteSplit.CompleteWord ell) :
      P i (ProfiledCW.flatten positions length f) = parentTypical htotal n m (mu i) eps f := by
    simp only [P, split_flatten]
  have hholes (j : Fin I.card) (i : Fin 3) :
      4 * d * (((unbrokenWords htotal i (address j) (mu i)).filter
          (fun f ↦ ¬ P i (ProfiledCW.flatten positions length f))) ∪
        (if i = 1 then filterHoles htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state 0 (mu 1) (address j) (keep 0 (address j))
         else if i = 2 then filterHoles htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state 1 (mu 2) (address j) (keep 1 (address j))
         else ∅)).card ≤ (unbrokenWords htotal i (address j) (mu i)).card := by
    have hu : ∀ i : Fin 2,
        4 * d * (filterHoles htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state i
          (mu (yzMode i)) (address j) (keep i (address j))).card ≤
            (unbrokenWords htotal (yzMode i) (address j) (mu (yzMode i))).card :=
      (Finset.mem_filter.mp (hIu (hj j))).2
    fin_cases i
    · have hh := htype 0 (address j) (hIt (hj j))
      have hsmall : 4 * d * (typeHoles htotal 0 (address j) (mu 0) (parentTypical htotal n m (mu 0) eps)).card ≤
          (unbrokenWords htotal 0 (address j) (mu 0)).card :=
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right d (by decide : 4 ≤ 8))).trans hh
      simpa [hsplit, typeHoles] using hsmall
    · simpa [hsplit, keep, yzMode, filterHoles, typeHoles, ← Finset.union_assoc] using hu 0
    · simpa [hsplit, keep, yzMode, filterHoles, typeHoles, ← Finset.union_assoc] using hu 1
  let E : ExactStep ell M P := {
    hash := D
    stage := A
    level := rfl
    length := length
    count := I.card
    state := state
    address := address
    injective := haddr
    target := fun j ↦ hIt (hj j)
    bucketed := fun j ↦ hIb (hj j)
    hashed := fun j ↦ hIh (hj j)
    isolated := fun j b hb he ↦ hIso (address j) (hj j) b hb he
    holes := hholes }
  have hincl : ∀ j i f,
      f ∈ unbrokenWords E.stage.total i (E.address j) (E.stage.mu i) →
      P i (ProfiledCW.flatten E.stage.positions E.length f) →
      source i (ProfiledCW.flatten E.stage.positions E.length f) := by
    intro j i f hf hp
    apply hsource i (address j) (hIt (hj j)) f
    · exact (Finset.mem_filter.mp hf).2.1
    · exact (hsplit i f).mp hp
  obtain ⟨F, hcount, hexponent, _, houtput⟩ :=
    mme_exact_step_source_refinement_on_unbroken E hincl
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [hcount] using hIc
  · exact hexponent
  · exact houtput

private theorem mme_child_grading_implies_parent_grading
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n) (f : Position n → CompleteSplit.CompleteWord ell)
    (hf : Graded htotal i a f) (r : Fin R) (t : Fin (n r)) :
    (∑ h : Fin 2, ∑ q, (f ⟨r,t,h⟩ q).val) = parent r i := by
  rw [Fin.sum_univ_two, hf, hf]
  simp only [fullCell, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  change ((a r t).val i).val + (parent r i - ((a r t).val i).val) = parent r i
  exact Nat.add_sub_of_le ((a r t).property.2 i)

/-- The computed regional extraction admits exact parent grades in its source,
while retaining its quantitative count bound and concrete child-profile output. -/
private theorem mme_recursive_region_parent_graded_exact_step_realization {half R ell N L M : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (ell - 1) = M)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (hsupport : ∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val)
    (hboundary : BoundaryProfiles mu)
    (reference : Address half R parent n) (href : reference ∈ RecursiveXHash.target m)
    (k d : ℕ) (hk : 0 < k) (hd : 1 < d) (hkn : ∀ r, k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) ≤
      (k : ℝ) * eps ^ 2) :
    let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
    let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
    let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
    ∃ E : ExactStep ell M (fun i x =>
      parentTypical htotal n m (mu i) eps (ProfiledCW.split positions length x) ∧
      ∀ (r : Fin R) (t : Fin (n r)),
        (∑ h : Fin 2, ∑ q, ((ProfiledCW.split positions length x) ⟨r,t,h⟩ q).val) =
          parent r i),
      ((RecursiveXHash.target (n := n) m).card : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
      E.stage.repairExponent = Nat.log d cap + 1 ∧
      E.output = fun i x ↦ Graded htotal i reference (ProfiledCW.split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (ProfiledCW.split positions length x) := by
  apply solution parent n htotal hhalf m e
    positions length mu hmass hsupport hboundary reference href k d hk hd hkn hdiv
    eps heps hscale
  intro i a ha f hg ht
  refine ⟨?_, ?_⟩
  · simpa only [split_flatten] using ht
  · intro r t
    simpa only [split_flatten] using
      mme_child_grading_implies_parent_grading htotal i a f hg r t


#print axioms solution
