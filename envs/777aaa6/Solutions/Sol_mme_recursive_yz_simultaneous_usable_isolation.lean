-- Prove2me | solution 1 for mme_recursive_yz_simultaneous_usable_isolation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-12T11:04:27.830931+00:00
-- url     : https://prove2.me/submissions/8f9721db-bf8f-4087-99be-d4648397cd79

import Theorems.Thm_mme_recursive_yz_simultaneous_usable_incidence
import Theorems.Thm_mme_recursive_x_hash_finite_usable_isolation
open BigOperators MME MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem field_support {half R N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (w : RecursiveYZ.Address half R parent n) (t : Fin (N + 1)) :
    RecursiveXHash.fieldWord p e 0 w t + RecursiveXHash.fieldWord p e 1 w t + RecursiveXHash.fieldWord p e 2 w t = (half : ZMod p) := by
  have h := (w (e t).1 (e t).2).property.1
  change (((w (e t).1 (e t).2).val 0).val : ZMod p) +
      (((w (e t).1 (e t).2).val 1).val : ZMod p) +
      (((w (e t).1 (e t).2).val 2).val : ZMod p) = _
  simpa only [Nat.cast_add] using congrArg (fun a : ℕ ↦ (a : ZMod p)) h

theorem solution {half R ell N p : ℕ} [Fact p.Prime]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (hpodd : Odd p) (hgrade : half < p) (d : ℕ)
    (mu : Fin 2 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (keep : Fin 2 → Address half R parent n →
      (Position n → CompleteSplit.CompleteWord ell) → Prop)
    (htype : ∀ i a, a ∈ RecursiveXHash.target m →
      8 * d * (typeHoles htotal (yzMode i) a (mu i) (keep i a)).card ≤
        (unbrokenWords htotal (yzMode i) a (mu i)).card)
    (hbudget : ∀ i a, a ∈ RecursiveXHash.target m →
      ∀ f ∈ unbrokenWords htotal (yzMode i) a (mu i), keep i a f →
        128 * d * ((RecursiveXHash.target (n := n) m).filter (fun b ↦
          RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
            compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (mu i) ≤
          p * Nat.card {g : Position n → CompleteSplit.CompleteWord ell //
            ParentType (RecursiveXHash.block (yzMode i) a)
              (parentCounts (RecursiveXHash.block (yzMode i) a) f) g})
    (hxBudget : 8 * (RecursiveXHash.ambient (n := n) m).card ≤
      p * ((RecursiveXHash.ambient (n := n) m).image (RecursiveXHash.block 0)).card) :
    let castS := S.image (fun a : ℕ ↦ (a : ZMod p))
    ∃ q : (Fin (N + 2) → ZMod p) × ZMod p, ∃ I : Finset (Address half R parent n),
      I ⊆ RecursiveXHash.target m ∧
      I ⊆ RecursiveXHash.bucketed m e castS q ∧
      I ⊆ RecursiveXHash.hashed m e castS q ∧
      I ⊆ usable htotal m e castS q d mu keep ∧
      (∀ a ∈ I, ∀ b ∈ RecursiveXHash.bucketed m e castS q,
        RecursiveXHash.block 0 a = RecursiveXHash.block 0 b → a = b) ∧
      ((RecursiveXHash.target (n := n) m).card : ℝ) * S.card / (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  classical
  let castS := S.image (fun a : ℕ ↦ (a : ZMod p))
  have hcast : castS.card = S.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have ha' : a < p := (Finset.mem_range.mp (hSrange ha)).trans_le (Nat.div_le_self _ _)
    have hb' : b < p := (Finset.mem_range.mp (hSrange hb)).trans_le (Nat.div_le_self _ _)
    have hv := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hv
  have hbucket (q) : RecursiveXHash.hashed m e castS q = RecursiveXHash.bucketed m e castS q := by
    ext w
    simp only [RecursiveXHash.hashed, RecursiveXHash.bucketed, Finset.mem_filter]
    have hh := mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label hpodd S hSrange hSfree
      (half : ZMod p) (RecursiveXHash.fieldWord p e 0 w) (RecursiveXHash.fieldWord p e 1 w)
      (RecursiveXHash.fieldWord p e 2 w) (field_support e w) q
    exact and_congr_right (fun _ ↦ hh.symm)
  have H := mme_recursive_yz_simultaneous_usable_incidence parent n htotal m e castS hpodd hgrade
    d mu hmass keep htype hbudget
  rw [hcast] at H
  have Hreal : (7 : ℝ) * (RecursiveXHash.target (n := n) m).card * S.card * (p : ℝ) ^ (N + 1) ≤
      8 * ∑ q : (Fin (N + 2) → ZMod p) × ZMod p,
        ((((RecursiveXHash.target m).filter (fun a ↦ a ∈ RecursiveXHash.hashed m e castS q)) ∩
          usable htotal m e castS q d mu keep).card : ℝ) := by exact_mod_cast H
  obtain ⟨q,I,hT,hI,hgood,hiso,hsize⟩ := mme_recursive_x_hash_finite_usable_isolation
    half R parent n m hpodd hgrade e S hSrange hSfree hxBudget
    (fun q ↦ usable htotal m e castS q d mu keep) (by
      simp only [hbucket] at Hreal
      linarith)
  exact ⟨q,I,hT,hI,by change I ⊆ RecursiveXHash.hashed m e castS q; rw [hbucket]; exact hI,hgood,hiso,hsize⟩
