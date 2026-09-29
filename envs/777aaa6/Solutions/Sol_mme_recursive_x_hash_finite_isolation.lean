-- Prove2me | solution 1 for mme_recursive_x_hash_finite_isolation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-11T22:48:07.638527+00:00
-- url     : https://prove2.me/submissions/eadb292a-94db-482e-995b-bf6c212658b9

import Definitions.Def_mme_recursive_x_hash_families
import Theorems.Thm_mme_recursive_x_hash_family_counts
import Theorems.Thm_mme_finset_weighted_collision_averaging_isolated
import Theorems.Thm_mme_dwz_target_two_mode_collision_card_le_of_degree
import Theorems.Thm_mme_dwz_asymmetric_hash_exact_incidence_sums
import Theorems.Thm_mme_dwz_asymmetric_hash_singleton_fiber_card
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label

open BigOperators MME MME.RecursiveThinSplit MME.RecursiveXHash
set_option autoImplicit false


private theorem averaging {Ω Edge X : Type} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [DecidableEq Edge] [DecidableEq X]
    (A T : Finset Edge) (x : Edge → X) (E : Ω → Finset Edge) (N p B d : ℕ)
    (hp : 0 < p) (hmod : 8 * d ≤ p)
    (hE : ∀ q, E q ⊆ A)
    (hx : ∀ a ∈ T, (A.filter (fun b ↦ x b = x a)).card ≤ d)
    (hstate : Fintype.card Ω = p ^ (N + 3))
    (hsingle : ∀ a ∈ T, (Finset.univ.filter (fun q : Ω ↦ a ∈ E q)).card = B * p ^ (N + 1))
    (hpair : ∀ pair ∈ (T.product A).filter (fun pair ↦
        pair.1 ≠ pair.2 ∧ (x pair.1 = x pair.2 ∨ x pair.1 = x pair.2)),
      (Finset.univ.filter (fun q : Ω ↦ pair.1 ∈ E q ∧ pair.2 ∈ E q)).card ≤ B * p ^ N) :
    ∃ q I, I ⊆ T ∧ I ⊆ E q ∧
      (∀ a ∈ I, ∀ b ∈ E q, x a = x b → a = b) ∧
      3 * (T.card : ℝ) * B / (4 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  classical
  have sums := mme_dwz_asymmetric_hash_exact_incidence_sums A T x x E N p B hE hsingle hpair
  have pairs := mme_dwz_target_two_mode_collision_card_le_of_degree A T x x d hx hx
  have hcoll : (∑ q, (((T.filter (fun a ↦ a ∈ E q)).product (E q)).filter
      (fun pair ↦ pair.1 ≠ pair.2 ∧ (x pair.1 = x pair.2 ∨ x pair.1 = x pair.2))).card)
      ≤ 2 * T.card * d * B * p ^ N := by
    exact sums.2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ pairs))
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hd : 8 * (d : ℝ) ≤ p := by exact_mod_cast hmod
  have hscale : (p : ℝ) ^ (N + 3) * (3 * (T.card : ℝ) * B / (4 * (p : ℝ) ^ 2)) =
      3 * (T.card : ℝ) * B * (p : ℝ) ^ (N + 1) / 4 := by
    rw [show N + 3 = (N + 1) + 2 by omega, pow_add]
    field_simp
  have harith : (p : ℝ) ^ (N + 3) * (3 * (T.card : ℝ) * B / (4 * (p : ℝ) ^ 2)) +
      2 * (T.card : ℝ) * d * B * (p : ℝ) ^ N ≤ T.card * B * (p : ℝ) ^ (N + 1) := by
    rw [hscale, pow_succ]
    have h := mul_le_mul_of_nonneg_right hd
      (show (0 : ℝ) ≤ (T.card : ℝ) * B * (p : ℝ) ^ N by positivity)
    nlinarith
  have budget : (Fintype.card Ω : ℝ) * (3 * (T.card : ℝ) * B / (4 * (p : ℝ) ^ 2)) +
      ∑ q, ((1 * (((T.filter (fun a ↦ a ∈ E q)).product (E q)).filter
        (fun pair ↦ pair.1 ≠ pair.2 ∧ (x pair.1 = x pair.2 ∨ x pair.1 = x pair.2))).card : ℕ) : ℝ) ≤
      ∑ q, (((∑ a ∈ T.filter (fun a ↦ a ∈ E q), (1 : ℕ)) : ℕ) : ℝ) := by
    simp only [one_mul, Finset.sum_const, smul_eq_mul, mul_one, ← Nat.cast_sum]
    rw [sums.1, hstate]
    push_cast
    have hc : ((∑ q, (((T.filter (fun a ↦ a ∈ E q)).product (E q)).filter
        (fun pair ↦ pair.1 ≠ pair.2 ∧ (x pair.1 = x pair.2 ∨ x pair.1 = x pair.2))).card : ℕ) : ℝ)
        ≤ 2 * (T.card : ℝ) * d * B * (p : ℝ) ^ N := by exact_mod_cast hcoll
    rw [Nat.cast_sum] at hc
    linarith
  obtain ⟨q, I, hT, hI, hiso, hsize⟩ :=
    mme_finset_weighted_collision_averaging_isolated T E x x (fun _ _ ↦ 1) 1
      (3 * (T.card : ℝ) * B / (4 * (p : ℝ) ^ 2)) (by intros; rfl) budget
  refine ⟨q, I, hT, hI, ?_, ?_⟩
  · intro a ha b hb hab
    exact hiso a ha b hb (Or.inl hab)
  · simpa using hsize



private theorem field_support {half R N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (w : Address half R parent n) (t : Fin (N + 1)) :
    fieldWord p e 0 w t + fieldWord p e 1 w t + fieldWord p e 2 w t = (half : ZMod p) := by
  have h := (w (e t).1 (e t).2).property.1
  change (((w (e t).1 (e t).2).val 0).val : ZMod p) +
      (((w (e t).1 (e t).2).val 1).val : ZMod p) +
      (((w (e t).1 (e t).2).val 2).val : ZMod p) = _
  simpa only [Nat.cast_add] using congrArg (fun a : ℕ ↦ (a : ZMod p)) h

private theorem field_eq_iff {half R N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (hp : half < p)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (i : Fin 3) (u v : Address half R parent n) :
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
    {n : Fin R → ℕ} (u v : Address half R parent n)
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

theorem solution (half R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    {N p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hgrade : half < p)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2)) (hSfree : ThreeAPFree (S : Set ℕ))
    (hbudget : 8 * (ambient (n := n) m).card ≤
      p * ((ambient (n := n) m).image (block 0)).card) :
    ∃ q : (Fin (N + 2) → ZMod p) × ZMod p, ∃ I : Finset (Address half R parent n),
      I ⊆ target m ∧
      I ⊆ bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q ∧
      (∀ a ∈ I, ∀ b ∈ bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q,
        block 0 a = block 0 b → a = b) ∧
      3 * ((target (n := n) m).card : ℝ) * S.card / (4 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  classical
  let A := ambient (n := n) m
  let T := target (n := n) m
  let castS := S.image (fun a : ℕ ↦ (a : ZMod p))
  let E := hashed m e castS
  have families := mme_recursive_x_hash_family_counts half R parent n m
  have hTA : T ⊆ A := families.1
  have hcast : castS.card = S.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have ha' : a < p := (Finset.mem_range.mp (hSrange ha)).trans_le (Nat.div_le_self _ _)
    have hb' : b < p := (Finset.mem_range.mp (hSrange hb)).trans_le (Nat.div_le_self _ _)
    have hv := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using hv
  have hbucket (q) : E q = bucketed m e castS q := by
    ext w
    simp only [E, hashed, bucketed, Finset.mem_filter]
    have hh := mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label hpodd S hSrange hSfree
      (half : ZMod p) (fieldWord p e 0 w) (fieldWord p e 1 w) (fieldWord p e 2 w)
      (field_support e w) q
    exact and_congr_right (fun _ ↦ hh.symm)
  by_cases hTempty : T = ∅
  · refine ⟨(0,0), ∅, Finset.empty_subset _, Finset.empty_subset _, ?_, ?_⟩
    · simp
    · change 3 * (T.card : ℝ) * S.card / (4 * (p : ℝ) ^ 2) ≤ _
      simp [hTempty]
  have hTnonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTempty
  obtain ⟨a, ha⟩ := hTnonempty
  have haA := hTA ha
  let V := (A.image (block 0)).card
  let d := (A.filter (fun b ↦ block 0 b = block 0 a)).card
  have hV : 0 < V := Finset.card_pos.mpr ⟨block 0 a, Finset.mem_image_of_mem _ haA⟩
  have hAd : A.card = V * d := families.2.1 a haA
  have hmod : 8 * d ≤ p := by
    apply Nat.le_of_mul_le_mul_left (c := V) _ hV
    calc
      V * (8 * d) = 8 * A.card := by rw [hAd]; ring
      _ ≤ V * p := by simpa only [A, V, mul_comm p] using hbudget
  have hx (b) (hb : b ∈ T) : (A.filter (fun c ↦ block 0 c = block 0 b)).card ≤ d := by
    have hbA := families.2.1 b (hTA hb)
    have heq : V * (A.filter (fun c ↦ block 0 c = block 0 b)).card = V * d := hbA.symm.trans hAd
    exact (Nat.eq_of_mul_eq_mul_left hV heq).le
  have hE (q) : E q ⊆ A := Finset.filter_subset _ _
  have hstate : Fintype.card ((Fin (N + 2) → ZMod p) × ZMod p) = p ^ (N + 3) := by
    simp [pow_succ]
  have hsingle (w) (hw : w ∈ T) :
      (Finset.univ.filter (fun q : (Fin (N + 2) → ZMod p) × ZMod p ↦ w ∈ E q)).card =
        castS.card * p ^ (N + 1) := by
    have hwA : w ∈ ambient (n := n) m := hTA hw
    simpa only [E, hashed, Finset.mem_filter, hwA, true_and,
      dwzAsymmetricAffineStatesRetaining] using
      mme_dwz_asymmetric_hash_singleton_fiber_card hpodd (half : ZMod p) castS
        (fieldWord p e 0 w) (fieldWord p e 1 w) (fieldWord p e 2 w) (field_support e w)
  have hpair : ∀ pair ∈ (T.product A).filter (fun pair ↦ pair.1 ≠ pair.2 ∧
      (block 0 pair.1 = block 0 pair.2 ∨ block 0 pair.1 = block 0 pair.2)),
      (Finset.univ.filter (fun q : (Fin (N + 2) → ZMod p) × ZMod p ↦
        pair.1 ∈ E q ∧ pair.2 ∈ E q)).card ≤ castS.card * p ^ N := by
    intro pair hp
    obtain ⟨⟨haT, hbA⟩, hab, hx⟩ := by simpa using hp
    have haA : pair.1 ∈ ambient (n := n) m := hTA haT
    change pair.2 ∈ ambient (n := n) m at hbA
    have hx' := (field_eq_iff hgrade e 0 pair.1 pair.2).mpr hx
    have hy' : fieldWord p e 1 pair.1 ≠ fieldWord p e 1 pair.2 := by
      intro hy
      exact hab (xy_injective pair.1 pair.2 hx ((field_eq_iff hgrade e 1 pair.1 pair.2).mp hy))
    have bound := mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
      (half : ZMod p) castS
      (fieldWord p e 0 pair.1) (fieldWord p e 1 pair.1) (fieldWord p e 2 pair.1)
      (fieldWord p e 0 pair.2) (fieldWord p e 1 pair.2) (fieldWord p e 2 pair.2)
      (Or.inl ⟨hx', hy'⟩)
    have heq : (Finset.univ.filter (fun q : (Fin (N + 2) → ZMod p) × ZMod p ↦
        pair.1 ∈ E q ∧ pair.2 ∈ E q)) =
        dwzAsymmetricAffineStatesRetaining (half : ZMod p) castS
          (fieldWord p e 0 pair.1) (fieldWord p e 1 pair.1) (fieldWord p e 2 pair.1) ∩
        dwzAsymmetricAffineStatesRetaining (half : ZMod p) castS
          (fieldWord p e 0 pair.2) (fieldWord p e 1 pair.2) (fieldWord p e 2 pair.2) := by
      ext q
      simp [E, hashed, haA, hbA, dwzAsymmetricAffineStatesRetaining]
    rw [heq]
    exact bound
  obtain ⟨q,I,hIT,hIE,hiso,hsize⟩ := averaging A T (block 0) E N p castS.card d
    (Fact.out : p.Prime).pos hmod hE hx hstate hsingle (by
      intro pair hp
      have hh := hpair pair (by simpa only [Finset.mem_filter, or_self] using hp)
      convert hh using 1
      congr 1
      ext q
      simp)
  refine ⟨q,I,hIT,?_,?_,?_⟩
  · change I ⊆ bucketed m e castS q
    rw [← hbucket q]
    exact hIE
  · change ∀ a ∈ I, ∀ b ∈ bucketed m e castS q, block 0 a = block 0 b → a = b
    rw [← hbucket q]
    exact hiso
  · simpa only [hcast, T] using hsize
