-- Prove2me | solution 1 for lean_workbook_plus_57913
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:22:54.738364+00:00
-- url     : https://prove2.me/submissions/ef1eabc7-6d54-470f-9953-383d01cf0f4d

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Tactic.NormNum

theorem disjoint_monochromatic_pairs {α β : Type*} [DecidableEq α] [Fintype β]
    (color : α → β) (N : ℕ) (s : Finset α)
    (hcard : 2 * N + Fintype.card β ≤ s.card + 1) :
    ∃ T : Finset (Finset α), T.card = N ∧
      (∀ t ∈ T, t ⊆ s ∧ t.card = 2 ∧ ∃ b, ∀ x ∈ t, color x = b) ∧
      (↑T : Set (Finset α)).PairwiseDisjoint id := by
  classical
  induction N generalizing s with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ N ih =>
      have hc : (Finset.univ : Finset β).card < s.card := by
        simp only [Finset.card_univ]
        omega
      obtain ⟨x, hxs, y, hys, hxy, hcolor⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
          (fun z _ => Finset.mem_univ (color z))
      let r := (s.erase x).erase y
      have hyerase : y ∈ s.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hys⟩
      have hcr : r.card + 2 = s.card := by
        have hxcard := Finset.card_erase_add_one hxs
        have hycard := Finset.card_erase_add_one hyerase
        dsimp [r]
        omega
      have hrsub : r ⊆ s := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hxr : x ∉ r := by simp [r]
      have hyr : y ∉ r := by simp [r]
      obtain ⟨T, hTcard, hT, hdis⟩ := ih r (by omega)
      let q : Finset α := {x, y}
      have hxq : x ∈ q := by simp [q]
      have hqcard : q.card = 2 := by simp [q, hxy]
      have hqsub : q ⊆ s := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hxs
        · exact Finset.mem_singleton.mp hz ▸ hys
      have hqcolor : ∃ b, ∀ z ∈ q, color z = b := by
        refine ⟨color x, ?_⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · rfl
        · have hzy := Finset.mem_singleton.mp hz
          exact hzy ▸ hcolor.symm
      have hqnot : q ∉ T := fun h => hxr ((hT q h).1 hxq)
      have hqdis (t : Finset α) (ht : t ∈ T) : Disjoint q t := by
        apply Finset.disjoint_left.mpr
        intro z hz hzt
        have hzr := (hT t ht).1 hzt
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hxr hzr
        · exact hyr (Finset.mem_singleton.mp hz ▸ hzr)
      refine ⟨insert q T, by simp [hqnot, hTcard], ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact ⟨hqsub, hqcard, hqcolor⟩
        · exact ⟨(hT t ht).1.trans hrsub, (hT t ht).2⟩
      · intro t ht u hu hne
        rcases Finset.mem_insert.mp ht with rfl | ht
        · rcases Finset.mem_insert.mp hu with rfl | hu
          · exact (hne rfl).elim
          · exact hqdis u hu
        · rcases Finset.mem_insert.mp hu with rfl | hu
          · exact (hqdis t ht).symm
          · exact hdis ht hu hne

private theorem fourth_power_of_divisible_factors {n : ℕ} (hn : n ≠ 0)
    (hf : ∀ p, 4 ∣ n.factorization p) : ∃ k, n = k ^ 4 := by
  refine ⟨∏ p ∈ n.factorization.support, p ^ (n.factorization p / 4), ?_⟩
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn, Finsupp.prod]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_mul, Nat.div_mul_cancel (hf p)]

theorem four_factor_of_prime_support (M P : Finset ℕ)
    (hpos : ∀ m ∈ M, 0 < m)
    (hsupport : ∀ m ∈ M, ∀ p, p.Prime → p ∣ m → p ∈ P)
    (hcard : 3 * 2 ^ P.card + 1 ≤ M.card) :
    ∃ S ⊆ M, S.card = 4 ∧ ∃ k, S.prod id = k ^ 4 := by
  classical
  let V := P → ZMod 2
  have hV : Fintype.card V = 2 ^ P.card := by simp [V]
  let color : ℕ → V := fun m p => m.factorization p
  obtain ⟨T, hTcard, hT, hdis⟩ := disjoint_monochromatic_pairs color
    (Fintype.card V + 1) M (by omega)
  have heven (t : Finset ℕ) (ht : t ∈ T) (p : P) :
      (∑ m ∈ t, m.factorization p) % 2 = 0 := by
    obtain ⟨a, b, hab, htab⟩ := Finset.card_eq_two.mp (hT t ht).2.1
    obtain ⟨c, hc⟩ := (hT t ht).2.2
    have ha : a ∈ t := htab.symm ▸ (by simp)
    have hb : b ∈ t := htab.symm ▸ (by simp)
    have hcolor := congr_fun ((hc a ha).trans (hc b hb).symm) p
    change (a.factorization p : ZMod 2) = (b.factorization p : ZMod 2) at hcolor
    have hmod := congrArg ZMod.val hcolor
    simp only [ZMod.val_natCast] at hmod
    rw [htab, Finset.sum_pair hab]
    omega
  let halfColor : Finset ℕ → V := fun t p =>
    ((∑ m ∈ t, m.factorization p) / 2 : ℕ)
  have htc : (Finset.univ : Finset V).card < T.card := by
    simp only [Finset.card_univ, hTcard]
    omega
  obtain ⟨t, ht, u, hu, htu, hhalf⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to htc
      (fun t _ => Finset.mem_univ (halfColor t))
  have hdu : Disjoint t u := hdis ht hu htu
  have hsub : t ∪ u ⊆ M := Finset.union_subset (hT t ht).1 (hT u hu).1
  refine ⟨t ∪ u, hsub, ?_, fourth_power_of_divisible_factors ?_ ?_⟩
  · rw [Finset.card_union_of_disjoint hdu, (hT t ht).2.1, (hT u hu).2.1]
  · exact Finset.prod_ne_zero_iff.mpr (fun m hm => (hpos m (hsub hm)).ne')
  · intro p
    have hfactor : ((t ∪ u).prod id).factorization p =
        (∑ m ∈ t, m.factorization p) + ∑ m ∈ u, m.factorization p := by
      change (∏ m ∈ t ∪ u, m).factorization p = _
      rw [Nat.factorization_prod (fun m hm => (hpos m (hsub hm)).ne'),
        Finsupp.finset_sum_apply, Finset.sum_union hdu]
    rw [hfactor]
    by_cases hp : p ∈ P
    · have ht2 := heven t ht ⟨p, hp⟩
      have hu2 := heven u hu ⟨p, hp⟩
      change (∑ m ∈ t, m.factorization p) % 2 = 0 at ht2
      change (∑ m ∈ u, m.factorization p) % 2 = 0 at hu2
      have hhalfmod := congrArg ZMod.val (congr_fun hhalf ⟨p, hp⟩)
      change (((∑ m ∈ t, m.factorization p) / 2 : ℕ) : ZMod 2).val =
        (((∑ m ∈ u, m.factorization p) / 2 : ℕ) : ZMod 2).val at hhalfmod
      simp only [ZMod.val_natCast] at hhalfmod
      apply Nat.dvd_of_mod_eq_zero
      omega
    · have hzero (m : ℕ) (hm : m ∈ M) : m.factorization p = 0 := by
        by_cases hprime : p.Prime
        · exact Nat.factorization_eq_zero_of_not_dvd
            (fun hd => hp (hsupport m hm p hprime hd))
        · exact Nat.factorization_eq_zero_of_not_prime _ hprime
      have htzero := Finset.sum_eq_zero (fun m hm => hzero m ((hT t ht).1 hm))
      have huzero := Finset.sum_eq_zero (fun m hm => hzero m ((hT u hu).1 hm))
      rw [htzero, huzero]
      exact dvd_zero 4

theorem four_factor_fourth_power_bounded_primes (M : Finset ℕ)
    (hpos : ∀ m ∈ M, 0 < m)
    (hsupport : ∀ m ∈ M, ∀ p, p.Prime → p ∣ m → p ≤ 23)
    (hcard : 1537 ≤ M.card) :
    ∃ S ⊆ M, S.card = 4 ∧ ∃ k, S.prod id = k ^ 4 := by
  apply four_factor_of_prime_support M ((Finset.range 24).filter Nat.Prime) hpos
  · intro m hm p hp hpm
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := hsupport m hm p hp hpm
      omega), hp⟩
  · have hcount : ((Finset.range 24).filter Nat.Prime).card = 9 := by decide
    rw [hcount]
    exact hcard

theorem solution (M : Finset ℕ) (Mpos : ∀ m ∈ M, 0 < m)
    (_Mdivisors : ∀ m ∈ M, ∀ n, m.Prime ∧ n ∣ m → m ≤ 23) :
    ∃ M' : Finset ℕ, M' ⊆ M ∧ ∃ k, M'.prod id = k ^ 4 := by
  classical
  by_cases hfull : 1537 ≤ M.card ∧
      ∀ m ∈ M, ∀ p, p.Prime → p ∣ m → p ≤ 23
  · obtain ⟨S, hSM, _, k, hk⟩ :=
      four_factor_fourth_power_bounded_primes M Mpos hfull.2 hfull.1
    exact ⟨S, hSM, k, hk⟩
  · exact ⟨∅, Finset.empty_subset M, 1, by simp⟩
