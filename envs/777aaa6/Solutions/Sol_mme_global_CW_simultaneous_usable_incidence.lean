-- Prove2me | solution 1 for mme_global_CW_simultaneous_usable_incidence
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T07:57:06.312954+00:00
-- url     : https://prove2.me/submissions/0c928067-8109-42aa-917f-4527353862b8

import Definitions.Def_mme_global_CW_counting_data
import Theorems.Thm_mme_global_CW_hash_ambiguity_bound
import Theorems.Thm_mme_global_CW_useful_mode_histogram
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Theorems.Thm_mme_dwz_asymmetric_hash_singleton_fiber_card

open BigOperators MME MME.RecursiveYZ MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

private theorem two_mode_good_fraction {Ω W : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq W]
    (R : Finset Ω) (U : Fin 2 → Finset W)
    (initial : Fin 2 → Finset W) (collision holes : Fin 2 → Ω → Finset W)
    (d : ℕ)
    (hinitial : ∀ i, 8 * d * (initial i).card ≤ (U i).card)
    (hholes : ∀ i q, (holes i q).card ≤ (initial i).card + (collision i q).card)
    (hsub : ∀ i q, holes i q ⊆ U i)
    (hcollision : ∀ i q, collision i q ⊆ U i)
    (hword : ∀ i f, f ∈ U i →
      128 * d * (R.filter (fun q ↦ f ∈ collision i q)).card ≤ R.card) :
    7 * R.card ≤ 8 * (R.filter (fun q ↦ ∀ i, 4 * d * (holes i q).card ≤ (U i).card)).card := by
  classical
  let bad := fun i : Fin 2 ↦ R.filter (fun q ↦ (U i).card < 4 * d * (holes i q).card)
  have hb (i : Fin 2) : 16 * (bad i).card ≤ R.card := by
    by_cases hU : (U i).card = 0
    · have he : U i = ∅ := Finset.card_eq_zero.mp hU
      have hz (q : Ω) : holes i q = ∅ := Finset.subset_empty.mp (he ▸ hsub i q)
      have hbe : bad i = ∅ := by simp [bad,hU,hz]
      simp [hbe]
    have hUpos : 0 < (U i).card := Nat.pos_of_ne_zero hU
    have hsum : 128 * d * (∑ q ∈ R, (collision i q).card) ≤ R.card * (U i).card := by
      have heq : (∑ q ∈ R, (collision i q).card) =
          ∑ f ∈ U i, (R.filter (fun q ↦ f ∈ collision i q)).card := by
        calc
          _ = ∑ q ∈ R, ((U i).filter (fun f ↦ f ∈ collision i q)).card := by
            apply Finset.sum_congr rfl
            intro q hq
            congr 1
            ext f
            simp only [Finset.mem_filter]
            exact ⟨fun hf ↦ ⟨hcollision i q hf,hf⟩, And.right⟩
          _ = _ := by
            simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
            rw [Finset.sum_comm]
      rw [heq, Finset.mul_sum]
      calc
        _ ≤ ∑ _f ∈ U i, R.card := Finset.sum_le_sum (fun f hf ↦ hword i f hf)
        _ = _ := by simp [Nat.mul_comm]
    have hsmall (q : Ω) (hq : q ∈ bad i) : (U i).card ≤ 8 * d * (collision i q).card := by
      have ht := (Finset.mem_filter.mp hq).2
      have hh := Nat.mul_le_mul_left (4 * d) (hholes i q)
      have hi := hinitial i
      nlinarith
    have hmarkov : (bad i).card * (U i).card ≤ 8 * d * (∑ q ∈ R, (collision i q).card) := by
      calc
        _ = ∑ _q ∈ bad i, (U i).card := by simp
        _ ≤ ∑ q ∈ bad i, 8 * d * (collision i q).card := Finset.sum_le_sum hsmall
        _ ≤ ∑ q ∈ R, 8 * d * (collision i q).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = _ := by rw [Finset.mul_sum]
    apply Nat.le_of_mul_le_mul_right (c := (U i).card) _ hUpos
    calc
      _ = 16 * ((bad i).card * (U i).card) := by ring
      _ ≤ 16 * (8 * d * ∑ q ∈ R, (collision i q).card) := Nat.mul_le_mul_left _ hmarkov
      _ = 128 * d * (∑ q ∈ R, (collision i q).card) := by ring
      _ ≤ _ := hsum
  let good := R.filter (fun q ↦ ∀ i, 4 * d * (holes i q).card ≤ (U i).card)
  let allbad := R.filter (fun q ↦ ¬ ∀ i, 4 * d * (holes i q).card ≤ (U i).card)
  have hcover : allbad ⊆ bad 0 ∪ bad 1 := by
    intro q hq
    obtain ⟨hqR, hq⟩ := Finset.mem_filter.mp hq
    push_neg at hq
    obtain ⟨i,hi⟩ := hq
    fin_cases i
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hqR,hi⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hqR,hi⟩))
  have hbad : allbad.card ≤ (bad 0).card + (bad 1).card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have htotal : good.card + allbad.card = R.card := Finset.card_filter_add_card_filter_not _
  have h0 := hb 0
  have h1 := hb 1
  change 7 * R.card ≤ 8 * good.card
  omega

private theorem field_support {half R N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (w : MME.RecursiveYZ.Address half R parent n) (t : Fin (N + 1)) :
    RecursiveXHash.fieldWord p e 0 w t + RecursiveXHash.fieldWord p e 1 w t + RecursiveXHash.fieldWord p e 2 w t = (half : ZMod p) := by
  have h := (w (e t).1 (e t).2).property.1
  change (((w (e t).1 (e t).2).val 0).val : ZMod p) +
      (((w (e t).1 (e t).2).val 1).val : ZMod p) +
      (((w (e t).1 (e t).2).val 2).val : ZMod p) = _
  simpa only [Nat.cast_add] using congrArg (fun a : ℕ ↦ (a : ZMod p)) h


private theorem retained_card {half R N p : ℕ} [Fact p.Prime]
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (hpodd : Odd p) (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m) :
    (Finset.univ.filter (fun q : (Fin (N + 2) → ZMod p) × ZMod p ↦
      a ∈ RecursiveXHash.hashed m e S q)).card = S.card * p ^ (N + 1) := by
  classical
  have haA := (mme_recursive_x_hash_family_counts half R parent n m).1 ha
  simpa only [RecursiveXHash.hashed, Finset.mem_filter, haA, true_and,
    dwzAsymmetricAffineStatesRetaining] using
    mme_dwz_asymmetric_hash_singleton_fiber_card hpodd (half : ZMod p) S
      (RecursiveXHash.fieldWord p e 0 a) (RecursiveXHash.fieldWord p e 1 a)
      (RecursiveXHash.fieldWord p e 2 a) (field_support e a)

private theorem collision_word_budget {half R ell N p : ℕ} [Fact p.Prime]
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N+1) ≃ Place n) (S : Finset (ZMod p)) (hgrade : half < p)
    (i : Fin 2) (d : ℕ) (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m)
    (mu : Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2)
    (hbudget : 128 * d * ((RecursiveXHash.target (n := n) m).filter (fun b ↦
      RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
        compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) mu ≤ p * modeNumber (yzMode i) mu)
    (f : Place n → CompleteSplit.CompleteWord ell) (hf : f ∈ words (yzMode i) a mu) :
    128 * d * ((Finset.univ.filter (fun q : (Fin (N+2) → ZMod p) × ZMod p ↦
      a ∈ RecursiveXHash.hashed m e S q)).filter (fun q ↦
        f ∈ hashHoles m e S q i mu a)).card ≤ S.card * p ^ (N+1) := by
  classical
  obtain ⟨ht,hcard⟩ := mme_global_CW_useful_mode_histogram (yzMode i) a mu f
    (Finset.mem_filter.mp hf).2.2
  let D := Nat.card {g : Place n → CompleteSplit.CompleteWord ell //
    ModeType (RecursiveXHash.block (yzMode i) a) (aggregate (yzMode i) mu) g}
  have hD : 0 < D := by
    letI : Nonempty {g : Place n → CompleteSplit.CompleteWord ell //
      ModeType (RecursiveXHash.block (yzMode i) a) (aggregate (yzMode i) mu) g} := ⟨⟨f,ht⟩⟩
    exact Nat.card_pos
  have hi : yzMode i = 1 ∨ yzMode i = 2 := by fin_cases i <;> simp [yzMode]
  have hloss := mme_global_CW_hash_ambiguity_bound parent n m e S hgrade (yzMode i) hi a ha
    (aggregate (yzMode i) mu) (yzBoundary i) (modeGroup (yzMode i)) mu hmass f ht
  have hcap : 128 * d * ((RecursiveXHash.target (n := n) m).filter (fun b ↦
      RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
        compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) mu ≤ p * D := by
    simpa only [D,hcard] using hbudget
  have hsets : ((Finset.univ.filter (fun q : (Fin (N+2) → ZMod p) × ZMod p ↦
      a ∈ RecursiveXHash.hashed m e S q)).filter (fun q ↦ f ∈ hashHoles m e S q i mu a)) =
      Finset.univ.filter (fun q : (Fin (N+2) → ZMod p) × ZMod p ↦
        a ∈ RecursiveXHash.hashed m e S q ∧ GlobalCW.ambiguous m e S q i mu a f) := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hashHoles,hf,true_and]
  apply Nat.le_of_mul_le_mul_right (c := D) _ hD
  rw [hsets]
  calc
    _ = 128 * d * ((Finset.univ.filter (fun q : (Fin (N+2) → ZMod p) × ZMod p ↦
      a ∈ RecursiveXHash.hashed m e S q ∧ GlobalCW.ambiguous m e S q i mu a f)).card * D) := by ring
    _ ≤ 128 * d * (((RecursiveXHash.target (n := n) m).filter (fun b ↦
        RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
        compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) mu * S.card * p ^ N) := by
      convert Nat.mul_le_mul_left (128*d) hloss using 1
      congr 3
      ext q
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,GlobalCW.ambiguous]
    _ ≤ (p * D) * (S.card * p ^ N) := by
      nlinarith [Nat.mul_le_mul_right (S.card * p ^ N) hcap]
    _ = _ := by simp only [pow_succ]; ring

theorem solution {half R ell N p : ℕ} [Fact p.Prime]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N+1) ≃ Place n) (S : Finset (ZMod p))
    (hpodd : Odd p) (hgrade : half < p) (d : ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2)
    (hbudget : ∀ i : Fin 2, ∀ a, a ∈ RecursiveXHash.target m →
      128 * d * ((RecursiveXHash.target (n := n) m).filter (fun b ↦
        RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
        compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (mu (yzMode i)) ≤
          p * modeNumber (yzMode i) (mu (yzMode i))) :
    7 * (RecursiveXHash.target (n := n) m).card * S.card * p ^ (N+1) ≤
      8 * ∑ q : (Fin (N+2) → ZMod p) × ZMod p,
        (((RecursiveXHash.target m).filter (fun a ↦ a ∈ RecursiveXHash.hashed m e S q)) ∩
          hashUsable m e S q d mu).card := by
  classical
  have haGood (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m) :
      7 * (S.card * p ^ (N+1)) ≤ 8 * (Finset.univ.filter
        (fun q : (Fin (N+2) → ZMod p) × ZMod p ↦
          a ∈ RecursiveXHash.hashed m e S q ∧ a ∈ hashUsable m e S q d mu)).card := by
    let Ra := Finset.univ.filter (fun q : (Fin (N+2) → ZMod p) × ZMod p ↦
      a ∈ RecursiveXHash.hashed m e S q)
    let U := fun i : Fin 2 ↦ words (yzMode i) a (mu (yzMode i))
    let holes := fun i q ↦ hashHoles m e S q i (mu (yzMode i)) a
    have hc : ∀ i q, holes i q ⊆ U i := fun _ _ ↦ Finset.filter_subset _ _
    have h := two_mode_good_fraction Ra U (fun _ ↦ ∅) holes holes d
      (by intro i; simp) (by intro i q; simp) hc hc (by
        intro i f hf
        rw [retained_card m e S hpodd a ha]
        exact collision_word_budget m e S hgrade i d a ha (mu (yzMode i))
          (hmass (yzMode i)) (hbudget i a ha) f hf)
    rw [retained_card m e S hpodd a ha] at h
    convert h using 1
    congr 2
    ext q
    simp only [Ra,U,holes,Finset.mem_filter,Finset.mem_univ,true_and,hashUsable,ha,true_and]
  have hs := Finset.sum_le_sum haGood
  have heq : (∑ a ∈ RecursiveXHash.target (n := n) m,
      (Finset.univ.filter (fun q : (Fin (N+2) → ZMod p) × ZMod p ↦
        a ∈ RecursiveXHash.hashed m e S q ∧ a ∈ hashUsable m e S q d mu)).card) =
      ∑ q : (Fin (N+2) → ZMod p) × ZMod p,
        (((RecursiveXHash.target m).filter (fun a ↦ a ∈ RecursiveXHash.hashed m e S q)) ∩
          hashUsable m e S q d mu).card := by
    simp only [← Finset.filter_mem_eq_inter,Finset.filter_filter,
      Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> rfl
  rw [← Finset.mul_sum (a := 8),heq] at hs
  simpa only [Finset.sum_const,nsmul_eq_mul,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hs
