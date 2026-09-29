-- Prove2me | solution 1 for mme_dwz_hole_lemma_cover_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T10:06:31.815001+00:00
-- url     : https://prove2.me/submissions/44683661-0b22-47e5-aae2-e99a13022624

import Mathlib.Tactic
import Definitions.Def_mme_dwz_hole_cover_data

/-! A standalone proof of the finite probabilistic covering core. -/

open BigOperators Finset

open MME.DWZSquare

universe u v

variable {Block : Type u} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]

private lemma card_good_mul_card
    (system : AvailableBlockShuffle Block Shuffle)
    (copy : BrokenBlockCopy Block) (block : Block) :
    (univ.filter (fun g : Shuffle =>
        (system.move g).symm block ∈ copy.nonholes)).card * Fintype.card Block =
      copy.nonholes.card * Fintype.card Shuffle := by
  classical
  let preimage : Shuffle → Block := fun g => (system.move g).symm block
  have hpartition := Finset.sum_card_fiberwise_eq_card_filter
    (univ : Finset Shuffle) copy.nonholes preimage
  calc
    (univ.filter (fun g : Shuffle =>
          (system.move g).symm block ∈ copy.nonholes)).card * Fintype.card Block =
        (∑ source ∈ copy.nonholes,
          (univ.filter (fun g : Shuffle => preimage g = source)).card) *
            Fintype.card Block := by
              rw [hpartition]
    _ = ∑ source ∈ copy.nonholes,
          (univ.filter (fun g : Shuffle => preimage g = source)).card *
            Fintype.card Block := by rw [Finset.sum_mul]
    _ = ∑ _source ∈ copy.nonholes, Fintype.card Shuffle := by
      apply Finset.sum_congr rfl
      intro source hsource
      have hfiber := system.uniform_fiber source block
      have heq :
          univ.filter (fun g : Shuffle => preimage g = source) =
            univ.filter (fun g : Shuffle => system.move g source = block) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, preimage,
          Equiv.symm_apply_eq]
        exact eq_comm
      rw [heq]
      exact hfiber
    _ = copy.nonholes.card * Fintype.card Shuffle := by simp

private lemma card_bad_mul_card
    (system : AvailableBlockShuffle Block Shuffle)
    (copy : BrokenBlockCopy Block) (block : Block) :
    (univ.filter (fun g : Shuffle =>
        (system.move g).symm block ∉ copy.nonholes)).card * Fintype.card Block =
      Fintype.card Shuffle * (Fintype.card Block - copy.nonholes.card) := by
  classical
  let good : Finset Shuffle := univ.filter (fun g : Shuffle =>
    (system.move g).symm block ∈ copy.nonholes)
  let bad : Finset Shuffle := univ.filter (fun g : Shuffle =>
    (system.move g).symm block ∉ copy.nonholes)
  have hpart : good.card + bad.card = Fintype.card Shuffle := by
    simpa only [good, bad, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not
        (s := (univ : Finset Shuffle))
        (p := fun g : Shuffle => (system.move g).symm block ∈ copy.nonholes))
  have hgood : good.card * Fintype.card Block =
      copy.nonholes.card * Fintype.card Shuffle := by
    simpa only [good] using card_good_mul_card system copy block
  have hcopy : copy.nonholes.card ≤ Fintype.card Block := by
    simpa using copy.nonholes.card_le_univ
  have hbad : bad.card = Fintype.card Shuffle - good.card := by omega
  change bad.card * Fintype.card Block = _
  calc
    bad.card * Fintype.card Block =
      (Fintype.card Shuffle - good.card) * Fintype.card Block := by
        rw [hbad]
    _ = Fintype.card Shuffle * Fintype.card Block -
        good.card * Fintype.card Block := by rw [Nat.sub_mul]
    _ = Fintype.card Shuffle * Fintype.card Block -
        copy.nonholes.card * Fintype.card Shuffle := by rw [hgood]
    _ = Fintype.card Shuffle * (Fintype.card Block - copy.nonholes.card) := by
      rw [Nat.mul_sub]
      ac_rfl

private lemma sum_remaining_card_mul_card
    (system : AvailableBlockShuffle Block Shuffle)
    (copy : BrokenBlockCopy Block) (remaining : Finset Block) :
    (∑ g : Shuffle,
        (remaining.filter (fun block =>
          (system.move g).symm block ∉ copy.nonholes)).card) *
          Fintype.card Block =
      remaining.card *
        (Fintype.card Shuffle * (Fintype.card Block - copy.nonholes.card)) := by
  classical
  have hswap :
      ∑ g : Shuffle,
          (remaining.filter (fun block =>
            (system.move g).symm block ∉ copy.nonholes)).card =
        ∑ block ∈ remaining,
          (univ.filter (fun g : Shuffle =>
            (system.move g).symm block ∉ copy.nonholes)).card := by
    calc
      ∑ g : Shuffle,
          (remaining.filter (fun block =>
            (system.move g).symm block ∉ copy.nonholes)).card =
        ∑ g : Shuffle, ∑ block ∈ remaining,
          if (system.move g).symm block ∉ copy.nonholes then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro g hg
            simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ block ∈ remaining, ∑ g : Shuffle,
          if (system.move g).symm block ∉ copy.nonholes then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ block ∈ remaining,
          (univ.filter (fun g : Shuffle =>
            (system.move g).symm block ∉ copy.nonholes)).card := by
            apply Finset.sum_congr rfl
            intro block hblock
            simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hswap, Finset.sum_mul]
  calc
    ∑ block ∈ remaining,
        (univ.filter (fun g : Shuffle =>
          (system.move g).symm block ∉ copy.nonholes)).card *
            Fintype.card Block =
      ∑ _block ∈ remaining,
        Fintype.card Shuffle * (Fintype.card Block - copy.nonholes.card) := by
          apply Finset.sum_congr rfl
          intro block hblock
          exact card_bad_mul_card system copy block
    _ = remaining.card *
        (Fintype.card Shuffle * (Fintype.card Block - copy.nonholes.card)) := by simp

private lemma exists_shuffle_card_le
    (system : AvailableBlockShuffle Block Shuffle)
    (copy : BrokenBlockCopy Block) (remaining : Finset Block) :
    ∃ g : Shuffle,
      ((remaining.filter (fun block =>
        (system.move g).symm block ∉ copy.nonholes)).card : ℝ) ≤
        (remaining.card : ℝ) * (1 - nonholeFraction copy) := by
  classical
  let missed : Shuffle → ℝ := fun g =>
    ((remaining.filter (fun block =>
      (system.move g).symm block ∉ copy.nonholes)).card : ℝ)
  obtain ⟨g, hgmem, hgmin⟩ :=
    Finset.exists_min_image (univ : Finset Shuffle) missed Finset.univ_nonempty
  refine ⟨g, ?_⟩
  have hQpos : (0 : ℝ) < Fintype.card Shuffle := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  have hBpos : (0 : ℝ) < Fintype.card Block := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  have hminsum : (Fintype.card Shuffle : ℝ) * missed g ≤
      ∑ h : Shuffle, missed h := by
    calc
      (Fintype.card Shuffle : ℝ) * missed g =
          ∑ _h : Shuffle, missed g := by simp
      _ ≤ ∑ h : Shuffle, missed h := by
        apply Finset.sum_le_sum
        intro h hh
        exact hgmin h (by simp)
  have hsumNat := sum_remaining_card_mul_card system copy remaining
  have hsumReal :
      (∑ h : Shuffle, missed h) * (Fintype.card Block : ℝ) =
        (remaining.card : ℝ) *
          ((Fintype.card Shuffle : ℝ) *
            ((Fintype.card Block : ℝ) - copy.nonholes.card)) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hsumNat
    simpa only [Nat.cast_mul, Nat.cast_sum, missed, Nat.cast_sub
      (by simpa using copy.nonholes.card_le_univ)] using hcast
  have hsum :
      ∑ h : Shuffle, missed h =
        (Fintype.card Shuffle : ℝ) *
          ((remaining.card : ℝ) *
            (1 - (copy.nonholes.card : ℝ) / Fintype.card Block)) := by
    apply mul_right_cancel₀ hBpos.ne'
    rw [hsumReal]
    field_simp
  rw [hsum] at hminsum
  have hbound : missed g ≤
      (remaining.card : ℝ) *
        (1 - (copy.nonholes.card : ℝ) / Fintype.card Block) := by
    exact le_of_mul_le_mul_left (by simpa [mul_assoc] using hminsum) hQpos
  simpa only [missed, nonholeFraction] using hbound

private lemma nonholeFraction_le_one
    (copy : BrokenBlockCopy Block) : nonholeFraction copy ≤ 1 := by
  rw [nonholeFraction]
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast copy.nonholes.card_le_univ

private lemma nonholeFraction_nonneg
    (copy : BrokenBlockCopy Block) : 0 ≤ nonholeFraction copy := by
  rw [nonholeFraction]
  positivity

private lemma exists_shuffles_card_le_prod
    (system : AvailableBlockShuffle Block Shuffle)
    {s : ℕ} (copies : Fin s → BrokenBlockCopy Block)
    (indices : Finset (Fin s)) (initial : Finset Block) :
    ∃ shuffles : Fin s → Shuffle,
      ((initial.filter (fun block => ∀ t ∈ indices,
        (system.move (shuffles t)).symm block ∉ (copies t).nonholes)).card : ℝ) ≤
        (initial.card : ℝ) *
          ∏ t ∈ indices, (1 - nonholeFraction (copies t)) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      let shuffles : Fin s → Shuffle := fun _ => Classical.choice inferInstance
      refine ⟨shuffles, ?_⟩
      simp
  | @insert a indices ha ih =>
      obtain ⟨shuffles, hshuffles⟩ := ih
      let current : Finset Block := initial.filter (fun block => ∀ t ∈ indices,
        (system.move (shuffles t)).symm block ∉ (copies t).nonholes)
      obtain ⟨g, hg⟩ := exists_shuffle_card_le system (copies a) current
      let shuffles' : Fin s → Shuffle := Function.update shuffles a g
      refine ⟨shuffles', ?_⟩
      have hfilter :
          initial.filter (fun block => ∀ t ∈ insert a indices,
              (system.move (shuffles' t)).symm block ∉ (copies t).nonholes) =
            current.filter (fun block =>
              (system.move g).symm block ∉ (copies a).nonholes) := by
        ext block
        simp only [Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp,
          current, shuffles', Function.update_self]
        constructor
        · intro h
          refine ⟨⟨h.1, ?_⟩, h.2.1⟩
          intro t ht
          have hta : t ≠ a := fun hta => ha (hta ▸ ht)
          simpa [Function.update_of_ne hta] using h.2.2 t ht
        · rintro ⟨⟨hinit, hrest⟩, haGood⟩
          refine ⟨hinit, haGood, ?_⟩
          intro t ht
          have hta : t ≠ a := fun hta => ha (hta ▸ ht)
          simpa [Function.update_of_ne hta] using hrest t ht
      rw [hfilter]
      calc
        ((current.filter (fun block =>
            (system.move g).symm block ∉ (copies a).nonholes)).card : ℝ) ≤
          (current.card : ℝ) * (1 - nonholeFraction (copies a)) := hg
        _ ≤ ((initial.card : ℝ) *
            ∏ t ∈ indices, (1 - nonholeFraction (copies t))) *
              (1 - nonholeFraction (copies a)) := by
          apply mul_le_mul_of_nonneg_right hshuffles
          exact sub_nonneg.mpr (nonholeFraction_le_one (copies a))
        _ = (initial.card : ℝ) *
            ∏ t ∈ insert a indices, (1 - nonholeFraction (copies t)) := by
          rw [Finset.prod_insert ha]
          ring

private lemma card_mul_uncovered_product_lt_one
    {s : ℕ} (copies : Fin s → BrokenBlockCopy Block)
    (N ell : ℕ)
    (hcard : Fintype.card Block ≤ 2 ^ (N * ell))
    (hsum : ((N * ell + 1 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t)) :
    (Fintype.card Block : ℝ) *
        ∏ t : Fin s, (1 - nonholeFraction (copies t)) < 1 := by
  classical
  let total : ℝ := ∑ t : Fin s, nonholeFraction (copies t)
  have hproduct_exp :
      ∏ t : Fin s, (1 - nonholeFraction (copies t)) ≤ Real.exp (-total) := by
    calc
      ∏ t : Fin s, (1 - nonholeFraction (copies t)) ≤
          ∏ t : Fin s, Real.exp (-nonholeFraction (copies t)) := by
        apply Finset.prod_le_prod
        · intro t ht
          exact sub_nonneg.mpr (nonholeFraction_le_one (copies t))
        · intro t ht
          simpa only [sub_eq_add_neg, add_comm] using
            Real.add_one_le_exp (-nonholeFraction (copies t))
      _ = Real.exp (-total) := by
        rw [← Real.exp_sum]
        simp only [Finset.sum_neg_distrib, total]
  have hexp_mono : Real.exp (-total) ≤
      Real.exp (-((N * ell + 1 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg hsum
  have htwo : (2 : ℝ) < Real.exp 1 := by
    convert Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  have hbase : (2 : ℝ) ≤ Real.exp 1 := htwo.le
  have hpow : (2 : ℝ) ^ (N * ell) ≤
      (Real.exp 1) ^ (N * ell) :=
    pow_le_pow_left₀ (by norm_num) hbase (N * ell)
  have hpow_succ : (Real.exp 1) ^ (N * ell) <
      (Real.exp 1) ^ (N * ell + 1) :=
    pow_lt_pow_right₀ (Real.one_lt_exp_iff.mpr (by norm_num)) (Nat.lt_succ_self _)
  have hblock_exp : (Fintype.card Block : ℝ) <
      Real.exp ((N * ell + 1 : ℕ) : ℝ) := by
    calc
      (Fintype.card Block : ℝ) ≤ ((2 ^ (N * ell) : ℕ) : ℝ) := by
        exact_mod_cast hcard
      _ = (2 : ℝ) ^ (N * ell) := by norm_num
      _ ≤ (Real.exp 1) ^ (N * ell) := hpow
      _ < (Real.exp 1) ^ (N * ell + 1) := hpow_succ
      _ = Real.exp ((N * ell + 1 : ℕ) : ℝ) := by
        simpa using (Real.exp_nat_mul 1 (N * ell + 1)).symm
  have hlast : (Fintype.card Block : ℝ) *
      Real.exp (-((N * ell + 1 : ℕ) : ℝ)) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_lt_one (Real.exp_pos _)).mpr hblock_exp
  calc
    (Fintype.card Block : ℝ) *
        ∏ t : Fin s, (1 - nonholeFraction (copies t)) ≤
      (Fintype.card Block : ℝ) * Real.exp (-total) := by
        exact mul_le_mul_of_nonneg_left hproduct_exp (by positivity)
    _ ≤ (Fintype.card Block : ℝ) *
        Real.exp (-((N * ell + 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hexp_mono (by positivity)
    _ < 1 := hlast

theorem solution
    {Block : Type u} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]
    (system : AvailableBlockShuffle Block Shuffle)
    (N ell s : ℕ) (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy Block)
    (hcard : Fintype.card Block ≤ 2 ^ (N * ell))
    (hsum : ((N * ell + 1 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t)) :
    ∃ shuffles : Fin s → Shuffle, ∀ block : Block,
      ∃ t : Fin s,
        (system.move (shuffles t)).symm block ∈ (copies t).nonholes := by
  classical
  obtain ⟨shuffles, hremaining⟩ :=
    exists_shuffles_card_le_prod system copies (univ : Finset (Fin s))
      (univ : Finset Block)
  refine ⟨shuffles, ?_⟩
  let remaining : Finset Block := univ.filter (fun block => ∀ t : Fin s,
    (system.move (shuffles t)).symm block ∉ (copies t).nonholes)
  have hremaining' : (remaining.card : ℝ) ≤
      (Fintype.card Block : ℝ) *
        ∏ t : Fin s, (1 - nonholeFraction (copies t)) := by
    simpa only [remaining, Finset.mem_univ, forall_const, Finset.card_univ] using hremaining
  have hproduct_lt := card_mul_uncovered_product_lt_one copies N ell hcard hsum
  have hcard_lt_one : (remaining.card : ℝ) < 1 := lt_of_le_of_lt hremaining' hproduct_lt
  have hempty : remaining = ∅ := by
    apply Finset.card_eq_zero.mp
    have hnat : remaining.card < 1 := by exact_mod_cast hcard_lt_one
    omega
  intro block
  have hnot : block ∉ remaining := by simp [hempty]
  simp only [remaining, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hnot
  simpa only [not_not] using hnot
