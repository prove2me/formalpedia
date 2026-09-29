-- Prove2me | solution 1 for mme_global_CW_hash_ambiguity_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T07:54:41.4846+00:00
-- url     : https://prove2.me/submissions/7bb665e9-98d6-492c-aee0-80609dd5c560

import Definitions.Def_mme_global_CW_counting_data
import Theorems.Thm_mme_global_CW_compatible_competitor_bound
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_Z_pair_fiber_card_le

open BigOperators MME MME.RecursiveXHash
open MME.RecursiveYZ MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem field_eq_iff {half R N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (hp : half < p)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (i : Fin 3) (u v : MME.RecursiveYZ.Address half R parent n) :
    fieldWord p e i u = fieldWord p e i v ↔ block i u = block i v := by
  constructor
  · intro h
    funext r t
    obtain ⟨s, hs⟩ := e.surjective ⟨r,t⟩
    have ht := congrFun h s
    change ((block i u (e s).1 (e s).2).val : ZMod p) =
      ((block i v (e s).1 (e s).2).val : ZMod p) at ht
    rw [hs] at ht
    have hv := congrArg ZMod.val ht
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext hv
  · intro h
    funext t
    simp only [fieldWord, h]

private theorem xy_injective {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (u v : MME.RecursiveYZ.Address half R parent n)
    (hx : block 0 u = block 0 v) (hy : block 1 u = block 1 v) : u = v := by
  funext r t
  apply Subtype.ext
  have h0 := congrFun (congrFun hx r) t
  have h1 := congrFun (congrFun hy r) t
  change (u r t).val 0 = (v r t).val 0 at h0
  change (u r t).val 1 = (v r t).val 1 at h1
  have hu := (u r t).property.1
  have hv := (v r t).property.1
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · apply Fin.ext
    change ((u r t).val 2).val = ((v r t).val 2).val
    have hxv := congrArg Fin.val h0
    have hyv := congrArg Fin.val h1
    omega


private theorem xz_injective {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (u v : MME.RecursiveYZ.Address half R parent n)
    (hx : block 0 u = block 0 v) (hz : block 2 u = block 2 v) : u = v := by
  funext r t
  apply Subtype.ext
  have h0 := congrFun (congrFun hx r) t
  have h2 := congrFun (congrFun hz r) t
  change (u r t).val 0 = (v r t).val 0 at h0
  change (u r t).val 2 = (v r t).val 2 at h2
  have hu := (u r t).property.1
  have hv := (v r t).property.1
  funext i
  fin_cases i
  · exact h0
  · apply Fin.ext
    change ((u r t).val 1).val = ((v r t).val 1).val
    have hxv := congrArg Fin.val h0
    have hzv := congrArg Fin.val h2
    omega
  · exact h2

private theorem pair_bound {half R N p : ℕ} [Fact p.Prime]
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (hgrade : half < p) (i : Fin 3) (hi : i = 1 ∨ i = 2)
    (a b : MME.RecursiveYZ.Address half R parent n)
    (ha : a ∈ target m) (hb : b ∈ target m) (hne : a ≠ b)
    (hshare : block i a = block i b) :
    (Finset.univ.filter (fun q : (Fin (N + 2) → ZMod p) × ZMod p ↦
      a ∈ hashed m e S q ∧ b ∈ hashed m e S q)).card ≤ S.card * p ^ N := by
  classical
  have hTA := (mme_recursive_x_hash_family_counts half R parent n m).1
  have haA := hTA ha
  have hbA := hTA hb
  have hx : fieldWord p e 0 a ≠ fieldWord p e 0 b := by
    intro hx
    have hx' := (field_eq_iff hgrade e 0 a b).mp hx
    rcases hi with rfl | rfl
    · exact hne (xy_injective a b hx' hshare)
    · exact hne (xz_injective a b hx' hshare)
  have heq : (Finset.univ.filter (fun q : (Fin (N + 2) → ZMod p) × ZMod p ↦
      a ∈ hashed m e S q ∧ b ∈ hashed m e S q)) =
      dwzAsymmetricAffineStatesRetaining (half : ZMod p) S
        (fieldWord p e 0 a) (fieldWord p e 1 a) (fieldWord p e 2 a) ∩
      dwzAsymmetricAffineStatesRetaining (half : ZMod p) S
        (fieldWord p e 0 b) (fieldWord p e 1 b) (fieldWord p e 2 b) := by
    ext q
    simp [hashed, haA, hbA, dwzAsymmetricAffineStatesRetaining]
  rw [heq]
  have hs := (field_eq_iff hgrade e i a b).mpr hshare
  rcases hi with rfl | rfl
  · exact mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
      (half : ZMod p) S _ _ _ _ _ _ (Or.inr ⟨hs,hx⟩)
  · rw [← hs]
    exact mme_dwz_asymmetric_hash_shared_Z_pair_fiber_card_le
      (half : ZMod p) S _ _ _ _ _ hx

private theorem union_bound {Ω A : Type*} [Fintype Ω] [DecidableEq A]
    (E : Ω → Finset A) (C : Finset A) (a : A) (B : ℕ)
    (hpair : ∀ b ∈ C, b ≠ a →
      (Finset.univ.filter (fun q ↦ a ∈ E q ∧ b ∈ E q)).card ≤ B) :
    (Finset.univ.filter (fun q : Ω ↦
      a ∈ E q ∧ ∃ b ∈ C, b ≠ a ∧ b ∈ E q)).card ≤ C.card * B := by
  classical
  let H := fun b ↦ Finset.univ.filter (fun q : Ω ↦ a ∈ E q ∧ b ∈ E q)
  have hsub : (Finset.univ.filter (fun q : Ω ↦
      a ∈ E q ∧ ∃ b ∈ C, b ≠ a ∧ b ∈ E q)) ⊆ (C.erase a).biUnion H := by
    intro q hq
    obtain ⟨ha,b,hb,hne,hbq⟩ := (Finset.mem_filter.mp hq).2
    exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_erase.mpr ⟨hne,hb⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,hbq⟩⟩
  calc
    _ ≤ ((C.erase a).biUnion H).card := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ C.erase a, (H b).card := Finset.card_biUnion_le
    _ ≤ ∑ b ∈ C.erase a, B := by
      apply Finset.sum_le_sum
      intro b hb
      exact hpair b (Finset.mem_erase.mp hb).2 (Finset.mem_erase.mp hb).1
    _ = (C.erase a).card * B := by simp
    _ ≤ C.card * B := Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.erase_subset _ _))

theorem solution {half R N p : ℕ} [Fact p.Prime]
    {W G : Type*} [Fintype W] [Fintype G]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (hgrade : half < p) (i : Fin 3) (hi : i = 1 ∨ i = 2)
    (a : MME.RecursiveYZ.Address half R parent n) (ha : a ∈ target m)
    (eta : Fin R → Fin (half + 1) → W → ℕ)
    (boundary : Cell half R parent → Prop) (group : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2)
    (f : Place n → W) (hf : ModeType (block i a) eta f) :
    (Finset.univ.filter (fun q : (Fin (N + 2) → ZMod p) × ZMod p ↦
      a ∈ hashed m e S q ∧ ∃ b ∈ target m,
        block i b = block i a ∧ Compatible (cell b) boundary group mu f ∧
          b ≠ a ∧ b ∈ hashed m e S q)).card *
      Nat.card {g : Place n → W // ModeType (block i a) eta g} ≤
    ((target (n := n) m).filter (fun b ↦ block i b = block i a)).card *
      compatibilityNumber boundary group mu * S.card * p ^ N := by
  classical
  let C := (target (n := n) m).filter (fun b ↦
    block i b = block i a ∧ Compatible (cell b) boundary group mu f)
  have hpairs (b : MME.RecursiveYZ.Address half R parent n) (hb : b ∈ C) (hne : b ≠ a) :
      (Finset.univ.filter (fun q : (Fin (N + 2) → ZMod p) × ZMod p ↦
        a ∈ hashed m e S q ∧ b ∈ hashed m e S q)).card ≤ S.card * p ^ N := by
    obtain ⟨hbT, hblock, hcompat⟩ := Finset.mem_filter.mp hb
    exact pair_bound m e S hgrade i hi a b ha hbT (Ne.symm hne) hblock.symm
  have hu := union_bound (hashed m e S) C a (S.card * p ^ N) (by
    intro b hb hne
    convert hpairs b hb hne using 1
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and])
  have hc := mme_global_CW_compatible_competitor_bound parent n m i (block i a)
    eta boundary group mu hmass f hf
  let D := Nat.card {g : Place n → W // ModeType (block i a) eta g}
  have hmul := Nat.mul_le_mul_right D hu
  calc
    _ ≤ C.card * (S.card * p ^ N) * D := by
      convert hmul using 1
      congr 2
      ext q
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and,
        exists_prop, and_assoc]
    _ = C.card * D * S.card * p ^ N := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
