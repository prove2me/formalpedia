-- Prove2me | solution 1 for mme_global_CW_finite_count_budget
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:01:33.836249+00:00
-- url     : https://prove2.me/submissions/82bcf8b3-3f16-4d8b-af35-2968ad863da2

import Definitions.Def_mme_global_CW_counting_data
import Theorems.Thm_mme_global_CW_simultaneous_usable_incidence
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
open BigOperators MME MME.RecursiveYZ MME.GlobalCW MME.HashExtraction
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
private theorem bucket_eq (D : HashData) (q : D.State) :
    RecursiveXHash.hashed D.m D.positions (D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))) q = D.retained q := by
  classical
  letI : Fact D.p.Prime := ⟨D.prime⟩
  ext w
  simp only [RecursiveXHash.hashed,HashData.retained,RecursiveXHash.bucketed,Finset.mem_filter]
  have hs (t : Fin (D.N + 1)) :
      RecursiveXHash.fieldWord D.p D.positions 0 w t + RecursiveXHash.fieldWord D.p D.positions 1 w t +
        RecursiveXHash.fieldWord D.p D.positions 2 w t = (D.half : ZMod D.p) := by
    have H := (w (D.positions t).1 (D.positions t).2).property.1
    change (((w (D.positions t).1 (D.positions t).2).val 0).val : ZMod D.p) +
      (((w (D.positions t).1 (D.positions t).2).val 1).val : ZMod D.p) +
      (((w (D.positions t).1 (D.positions t).2).val 2).val : ZMod D.p) = _
    simpa only [Nat.cast_add] using congrArg (fun a : ℕ ↦ (a : ZMod D.p)) H
  have H := mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label D.odd D.labels D.labels_range D.labels_free
    (D.half : ZMod D.p) (RecursiveXHash.fieldWord D.p D.positions 0 w)
    (RecursiveXHash.fieldWord D.p D.positions 1 w) (RecursiveXHash.fieldWord D.p D.positions 2 w) hs q
  exact and_congr_right (fun _ ↦ H.symm)


private theorem holes_eq (D : HashData) {ell : ℕ}
    (mu : Fin 3 → Cell D.half D.R D.parent → CompleteSplit.CompleteWord ell → ℕ)
    (q : D.State) (a : D.Edge) (i : Fin 2) :
    hashHoles D.m D.positions (D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))) q i (mu (yzMode i)) a =
      holes D.m D.positions (D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))) q mu a (yzMode i) := by
  classical
  fin_cases i <;> ext f <;>
    simp [hashHoles,GlobalCW.ambiguous,holes,yzMode,yzBoundary,bucket_eq,HashData.retained,
      and_assoc,and_left_comm,and_comm]

theorem solution (D : HashData) {ell : ℕ} (d : ℕ)
    (mu : Fin 3 → Cell D.half D.R D.parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = D.m c.1 c.2)
    (hdegree : 8 * (RecursiveXHash.ambient (n := D.n) D.m).card ≤
      D.p * ((RecursiveXHash.ambient (n := D.n) D.m).image (RecursiveXHash.block 0)).card)
    (hload : ∀ i : Fin 2, ∀ a, a ∈ RecursiveXHash.target D.m →
      128 * d * ((RecursiveXHash.target (n := D.n) D.m).filter (fun b ↦
        RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
        compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) ≤
          D.p * modeNumber (yzMode i) (mu (yzMode i))) :
    let H : HashData := { D with good := (fun q ↦ hashUsable D.m D.positions
      (D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))) q d mu) }
    H.Budget ∧ ∀ q a, a ∈ H.good q → ∀ i,
      4 * d * (holes H.m H.positions (H.labels.image (fun a : ℕ ↦ (a : ZMod H.p))) q mu a i).card ≤
        (words i a (mu i)).card := by
  classical
  letI : Fact D.p.Prime := ⟨D.prime⟩
  let castS := D.labels.image (fun a : ℕ ↦ (a : ZMod D.p))
  have hcast : castS.card = D.labels.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have ha' : a < D.p := (Finset.mem_range.mp (D.labels_range ha)).trans_le (Nat.div_le_self _ _)
    have hb' : b < D.p := (Finset.mem_range.mp (D.labels_range hb)).trans_le (Nat.div_le_self _ _)
    have hv := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt ha',ZMod.val_natCast_of_lt hb'] using hv
  constructor
  · refine ⟨hdegree,?_⟩
    have H := mme_global_CW_simultaneous_usable_incidence D.parent D.n D.m D.positions castS
      D.odd D.grade_lt d mu hmass hload
    rw [hcast] at H
    have HR : (7 : ℝ) * (RecursiveXHash.target (n := D.n) D.m).card * D.labels.card *
        (D.p : ℝ) ^ (D.N+1) ≤ 8 * ∑ q : D.State,
          ((((RecursiveXHash.target D.m).filter (fun a ↦ a ∈ RecursiveXHash.hashed D.m D.positions castS q)) ∩
            hashUsable D.m D.positions castS q d mu).card : ℝ) := by exact_mod_cast H
    simp only [castS,bucket_eq] at HR
    change (7/8 : ℝ) * ((RecursiveXHash.target (n := D.n) D.m).card * D.labels.card *
      (D.p : ℝ) ^ (D.N+1)) ≤ ∑ q : D.State,
        ((((RecursiveXHash.target D.m).filter (fun a ↦ a ∈ D.retained q)) ∩
          hashUsable D.m D.positions castS q d mu).card : ℝ)
    dsimp only [castS]
    linarith
  · intro q a ha i
    have h := (Finset.mem_filter.mp ha).2
    fin_cases i
    · simp [holes]
    · have hi := h 0
      rw [holes_eq D mu q a 0] at hi
      exact hi
    · have hi := h 1
      rw [holes_eq D mu q a 1] at hi
      exact hi
