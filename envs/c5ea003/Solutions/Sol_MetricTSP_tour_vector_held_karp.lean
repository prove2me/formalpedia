-- Prove2me | solution 1 for MetricTSP.tour_vector_held_karp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T19:22:38.86673+00:00
-- url     : https://prove2.me/submissions/eb75edd7-8199-4afc-83d4-361b36dae6e2

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_tour_vector

namespace MetricTSP

open Finset

variable {n : ℕ}

lemma rot_val (i : Fin n) : (finRotate n i).val = (i.val + 1) % n := by
  have : NeZero n := ⟨Nat.pos_iff_ne_zero.mp i.pos⟩
  rw [finRotate_apply, Fin.add_def, Fin.val_one']
  conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

lemma rot_ne (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [rot_val] at hv
  have hlt := i.isLt
  rcases Nat.lt_or_ge (i.val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv; omega
  · have he : i.val + 1 = n := by omega
    rw [he, Nat.mod_self] at hv
    omega

lemma rot_rot_ne (hn : 3 ≤ n) (i : Fin n) : finRotate n (finRotate n i) ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [rot_val, rot_val] at hv
  have hlt := i.isLt
  rcases Nat.lt_or_ge (i.val + 1) n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv
    rcases Nat.lt_or_ge (i.val + 1 + 1) n with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at hv; omega
    · have he : i.val + 1 + 1 = n := by omega
      rw [he, Nat.mod_self] at hv; omega
  · have he : i.val + 1 = n := by omega
    rw [he, Nat.mod_self] at hv
    have h01 : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h01] at hv
    omega

/-- A set of positions that is nonempty, proper, and closed under the cyclic shift
would be everything; hence a proper nonempty set has an exit step. -/
lemma exists_exit (hn : 2 ≤ n) (T : Finset (Fin n)) (hT : T.Nonempty) (hTu : T ≠ univ) :
    ∃ i ∈ T, finRotate n i ∉ T := by
  by_contra hcon
  push_neg at hcon
  apply hTu
  obtain ⟨a, ha⟩ := hT
  have hcyc := isCycle_finRotate_of_le hn
  have key : ∀ k : ℕ, ((finRotate n) ^ k) a ∈ T := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hcon _ ih
  apply Finset.eq_univ_iff_forall.mpr
  intro j
  have hsc := hcyc.sameCycle (rot_ne hn a) (rot_ne hn j)
  obtain ⟨k, _, hk⟩ := hsc.exists_pow_eq'
  exact hk ▸ key k

lemma exists_entry (hn : 2 ≤ n) (T : Finset (Fin n)) (hT : T.Nonempty) (hTu : T ≠ univ) :
    ∃ i ∉ T, finRotate n i ∈ T := by
  have hc1 : Tᶜ.Nonempty := by
    by_contra h
    apply hTu
    apply Finset.eq_univ_iff_forall.mpr
    intro a
    by_contra ha
    exact h ⟨a, Finset.mem_compl.mpr ha⟩
  have hc2 : Tᶜ ≠ univ := by
    intro h
    obtain ⟨a, ha⟩ := hT
    have : a ∈ Tᶜ := h ▸ Finset.mem_univ a
    exact (Finset.mem_compl.mp this) ha
  obtain ⟨i, hi, hi'⟩ := exists_exit hn Tᶜ hc1 hc2
  exact ⟨i, Finset.mem_compl.mp hi, by simpa using hi'⟩

lemma tourSteps_symm (π : Equiv.Perm (Fin n)) (u v : Fin n) : tourSteps π u v = tourSteps π v u := by
  unfold tourSteps
  apply Finset.filter_congr
  intro i _
  constructor <;> (intro h; tauto)

lemma tourVec_symm (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    tourVec π u v = tourVec π v u := by
  unfold tourVec; rw [tourSteps_symm]

lemma tourSteps_diag (hn : 2 ≤ n) (π : Equiv.Perm (Fin n)) (v : Fin n) : tourSteps π v v = ∅ := by
  unfold tourSteps
  rw [Finset.filter_eq_empty_iff]
  intro i _
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
    exact rot_ne hn i (π.injective (h2.trans h1.symm))

lemma tourVec_diag (hn : 2 ≤ n) (π : Equiv.Perm (Fin n)) (v : Fin n) :
    tourVec π v v = 0 := by
  unfold tourVec; rw [tourSteps_diag hn]; simp

lemma tourVec_nonneg (π : Equiv.Perm (Fin n)) (u v : Fin n) : 0 ≤ tourVec π u v :=
  Nat.cast_nonneg _

lemma tourSteps_card_le_one (hn : 3 ≤ n) (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    (tourSteps π u v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [tourSteps, Finset.mem_filter] at ha hb
  rcases ha.2 with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rcases hb.2 with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · exact π.injective (ha1.trans hb1.symm)
  · -- a goes u→v, b goes v→u
    have h1 : a = finRotate n b := π.injective (ha1.trans hb2.symm)
    have h2 : finRotate n a = b := π.injective (ha2.trans hb1.symm)
    exfalso
    apply rot_rot_ne hn b
    rw [← h1, h2]
  · have h1 : b = finRotate n a := π.injective (hb1.trans ha2.symm)
    have h2 : finRotate n b = a := π.injective (hb2.trans ha1.symm)
    exfalso
    apply rot_rot_ne hn a
    rw [← h1, h2]
  · exact π.injective (ha1.trans hb1.symm)

lemma tourVec_le_one (hn : 3 ≤ n) (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    tourVec π u v ≤ 1 := by
  unfold tourVec
  exact_mod_cast tourSteps_card_le_one hn π u v

/-- The incidence vector as a sum of step indicators. -/
lemma tourVec_eq_sum (hn : 2 ≤ n) (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    tourVec π u v = ∑ i : Fin n,
      ((if π i = u ∧ π (finRotate n i) = v then (1 : ℝ) else 0)
        + (if π i = v ∧ π (finRotate n i) = u then (1 : ℝ) else 0)) := by
  unfold tourVec tourSteps
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hnab : ¬((π i = u ∧ π (finRotate n i) = v) ∧ (π i = v ∧ π (finRotate n i) = u)) := by
    rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have huv : u = v := h1.symm.trans h3
    exact rot_ne hn i (π.injective (h2.trans (huv ▸ h1.symm)))
  rcases Classical.em (π i = u ∧ π (finRotate n i) = v) with hA | hA <;>
    rcases Classical.em (π i = v ∧ π (finRotate n i) = u) with hB | hB
  · exact absurd ⟨hA, hB⟩ hnab
  · rw [if_pos (Or.inl hA), if_pos hA, if_neg hB]; norm_num
  · rw [if_pos (Or.inr hB), if_neg hA, if_pos hB]; norm_num
  · have hor : ¬((π i = u ∧ π (finRotate n i) = v) ∨ (π i = v ∧ π (finRotate n i) = u)) := by
      rintro (h | h)
      exacts [hA h, hB h]
    rw [if_neg hor, if_neg hA, if_neg hB]; norm_num

/-- Every city has degree exactly `2` in the tour vector. -/
lemma tourVec_degree (hn : 3 ≤ n) (π : Equiv.Perm (Fin n)) (v : Fin n) :
    ∑ u, tourVec π v u = 2 := by
  have h2 : 2 ≤ n := by omega
  calc ∑ u, tourVec π v u
      = ∑ u, ∑ i : Fin n,
          ((if π i = v ∧ π (finRotate n i) = u then (1 : ℝ) else 0)
            + (if π i = u ∧ π (finRotate n i) = v then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl fun u _ => tourVec_eq_sum h2 π v u
    _ = ∑ i : Fin n, ∑ u,
          ((if π i = v ∧ π (finRotate n i) = u then (1 : ℝ) else 0)
            + (if π i = u ∧ π (finRotate n i) = v then (1 : ℝ) else 0)) :=
        Finset.sum_comm
    _ = ∑ i : Fin n,
          ((if π i = v then (1 : ℝ) else 0)
            + (if π (finRotate n i) = v then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_add_distrib]
        congr 1
        · by_cases h : π i = v <;> simp [h]
        · rcases Classical.em (π (finRotate n i) = v) with h | h
          · rw [if_pos h,
              Finset.sum_congr rfl fun u _ => if_congr (and_iff_left h) rfl rfl]
            simp
          · rw [if_neg h,
              Finset.sum_congr rfl fun u _ => if_neg (fun hc => h hc.2)]
            simp
    _ = 1 + 1 := by
        rw [Finset.sum_add_distrib]
        congr 1
        · have hpred : ∀ i : Fin n, (π i = v) ↔ (i = π.symm v) := fun i => by
            constructor
            · intro h; rw [← h]; simp
            · intro h; rw [h]; simp
          rw [Finset.sum_congr rfl fun i _ => if_congr (hpred i) rfl rfl]
          simp
        · have hpred : ∀ i : Fin n, (π (finRotate n i) = v) ↔
              (i = (finRotate n).symm (π.symm v)) := fun i => by
            constructor
            · intro h
              apply (finRotate n).injective
              rw [Equiv.apply_symm_apply]
              apply π.injective
              rw [Equiv.apply_symm_apply, h]
            · intro h
              rw [h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          rw [Finset.sum_congr rfl fun i _ => if_congr (hpred i) rfl rfl]
          simp
    _ = 2 := by norm_num

/-- The tour crosses every nontrivial cut at least twice. -/
lemma tourVec_cut (hn : 3 ≤ n) (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hS : S.Nonempty) (hSu : S ≠ univ) :
    2 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, tourVec π u v := by
  have h1 : 2 ≤ n := by omega
  -- the positions whose city lies in S
  set T : Finset (Fin n) := Finset.univ.filter (fun i => π i ∈ S) with hT
  have hTne : T.Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨π.symm s, by simp [hT, hs]⟩
  have hTu : T ≠ univ := by
    intro h
    apply hSu
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    have : π.symm v ∈ T := h ▸ Finset.mem_univ _
    simpa [hT] using this
  obtain ⟨i, hiT, hiT'⟩ := exists_exit h1 T hTne hTu
  obtain ⟨j, hjT, hjT'⟩ := exists_entry h1 T hTne hTu
  rw [hT, Finset.mem_filter] at hiT hjT'
  have hiS : π i ∈ S := hiT.2
  have hiS' : π (finRotate n i) ∉ S := by
    intro h
    apply hiT'
    rw [hT, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h⟩
  have hjS : π j ∉ S := by
    intro h
    apply hjT
    rw [hT, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h⟩
  have hjS' : π (finRotate n j) ∈ S := hjT'.2
  -- the two crossing cells
  have hij : i ≠ j := fun h => hjS (h ▸ hiS)
  set a : Fin n × Fin n := (π i, π (finRotate n i)) with ha
  set b : Fin n × Fin n := (π (finRotate n j), π j) with hb
  have hab : a ≠ b := by
    intro h
    rw [ha, hb, Prod.ext_iff] at h
    have e1 : i = finRotate n j := π.injective h.1
    have e2 : finRotate n i = j := π.injective h.2
    apply rot_rot_ne hn j
    rw [← e1, e2]
  have hmem_a : a ∈ S ×ˢ Sᶜ := by
    rw [Finset.mem_product]
    exact ⟨hiS, Finset.mem_compl.mpr hiS'⟩
  have hmem_b : b ∈ S ×ˢ Sᶜ := by
    rw [Finset.mem_product]
    exact ⟨hjS', Finset.mem_compl.mpr hjS⟩
  have hfa : (1 : ℝ) ≤ tourVec π a.1 a.2 := by
    have : i ∈ tourSteps π a.1 a.2 := by
      rw [tourSteps, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Or.inl ⟨rfl, rfl⟩⟩
    unfold tourVec
    exact_mod_cast Finset.card_pos.mpr ⟨i, this⟩
  have hfb : (1 : ℝ) ≤ tourVec π b.1 b.2 := by
    have : j ∈ tourSteps π b.1 b.2 := by
      rw [tourSteps, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩
    unfold tourVec
    exact_mod_cast Finset.card_pos.mpr ⟨j, this⟩
  calc (2 : ℝ) = 1 + 1 := by norm_num
    _ ≤ tourVec π a.1 a.2 + tourVec π b.1 b.2 := add_le_add hfa hfb
    _ = ∑ p ∈ ({a, b} : Finset (Fin n × Fin n)), tourVec π p.1 p.2 := by
        rw [Finset.sum_pair hab]
    _ ≤ ∑ p ∈ S ×ˢ Sᶜ, tourVec π p.1 p.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rcases Finset.mem_insert.mp hp with h | h
          · exact h ▸ hmem_a
          · exact (Finset.mem_singleton.mp h) ▸ hmem_b
        · intro p _ _
          exact tourVec_nonneg π p.1 p.2
    _ = ∑ u ∈ S, ∑ v ∈ Sᶜ, tourVec π u v := by rw [Finset.sum_product']

/-- The tour vector is Held–Karp feasible. -/
lemma tourVec_feasible (hn : 3 ≤ n) (π : Equiv.Perm (Fin n)) :
    IsHeldKarp (tourVec π) := by
  have h2 : 2 ≤ n := by omega
  refine ⟨tourVec_symm π, tourVec_diag h2 π, tourVec_nonneg π,
    tourVec_le_one hn π, tourVec_degree hn π, tourVec_cut hn π⟩


end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (hn : 3 ≤ n) (π : Equiv.Perm (Fin n)) :
    IsHeldKarp (tourVec π) :=
  MetricTSP.tourVec_feasible hn π
