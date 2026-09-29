-- Prove2me | solution 1 for mme_recursive_region_exact_step_realization_of_graded_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T01:59:26.417901+00:00
-- url     : https://prove2.me/submissions/a8933902-de2f-400e-8ceb-a42037557a07

import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_recursive_region_computed_hash_selection
import Theorems.Thm_mme_recursive_region_derived_parent_hole_budget
import Mathlib.Data.Nat.Log

open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Same construction as `mme_recursive_region_actual_exact_step_realization`, but the
source predicate is arbitrary: any `P` that already holds at every unbroken word of every
target address.  The parent-typical predicate of the accepted theorem is the special case
supplied by its own hole budget; here the X-mode hole set is empty by hypothesis, and the
Y/Z hole sets are the ones selected by the hash. -/
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
    (P : Predicate M)
    (hP : ∀ (i : Fin 3) (a : Address half R parent n), a ∈ RecursiveXHash.target m →
      ∀ f ∈ unbrokenWords htotal i a (mu i), P i (ProfiledCW.flatten positions length f)) :
    let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
    let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
    let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
    ∃ E : ExactStep ell M P,
      ((RecursiveXHash.target (n := n) m).card : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
      E.stage.repairExponent = Nat.log d cap + 1 ∧
      E.output = fun i x ↦ Graded htotal i reference (ProfiledCW.split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (ProfiledCW.split positions length x) := by
  classical
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
  have hfilter (j : Fin I.card) (i : Fin 3) :
      ((unbrokenWords htotal i (address j) (mu i)).filter
        (fun f ↦ ¬ P i (ProfiledCW.flatten positions length f))) = ∅ :=
    Finset.filter_false_of_mem (fun f hf ↦ not_not.mpr (hP i (address j) (hIt (hj j)) f hf))
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
    · simp [hfilter]
    · simpa [hfilter, keep, yzMode, filterHoles] using hu 0
    · simpa [hfilter, keep, yzMode, filterHoles] using hu 1
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
  exact ⟨E,hIc,rfl,rfl⟩
