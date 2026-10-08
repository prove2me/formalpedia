-- Prove2me | solution 1 for ProofsInTheBook.Chapter11.ungar_directions_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:12:57.967985+00:00
-- url     : https://prove2.me/submissions/b975fad9-9814-4404-b02d-e3fcaaac4052

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter11


/-!
# Chapter 11: The slope problem

From "Proofs from THE BOOK":

**The slope problem (Ungar's theorem)**: Given `n` points in the plane,
not all on a line, the number of distinct projective directions determined by
connecting pairs of points is at least `2 * ⌊n / 2⌋`.

The book's proof uses an elegant inductive argument combined with
a "rotating calipers" technique: consider the convex hull and analyze
how slopes change as we rotate a direction vector.

The Lean statement uses projective `Direction`s, so the vertical parallel class
is counted.  The fixed-axis finite slope set `slopesDeterminedBy` intentionally
omits vertical directions and is therefore only a corollary with a possible
loss of one.

This is closely related to the Sylvester-Gallai theorem (Chapter 10).
-/

namespace ProofsInTheBook.Chapter11









































































namespace PointLabeling



end PointLabeling

namespace DirectionLabeling



end DirectionLabeling

/-! ### Sweep construction via oriented levels -/



















































/-! ### Level-block extraction from monotone functions -/











































































namespace DirectionLabeling







end DirectionLabeling



theorem not_all_pair_directions_eq_of_noncollinearSet {points : Finset Point2}
    (hncoll : NoncollinearSet points) :
    ¬ ∃ d : Direction,
      ∀ p ∈ points, ∀ q ∈ points, p ≠ q → direction p q = d := by
  rintro ⟨d, hall⟩
  rcases hncoll with ⟨p, hp, q, hq, r, hr, hnon⟩
  have hpq : p ≠ q := left_ne_right_of_noncollinear hnon
  have hpr : p ≠ r := left_ne_third_of_noncollinear hnon
  have hdir_pq : direction p q = d := hall p hp q hq hpq
  have hdir_pr : direction p r = d := hall p hp r hr hpr
  exact directions_from_noncollinear_triple_ne hnon (hdir_pq.trans hdir_pr.symm)

theorem not_all_directionLevels_eq_of_noncollinearSet {points : Finset Point2}
    (hncoll : NoncollinearSet points) (d : Direction) :
    ¬ ∃ c : ℝ, ∀ p ∈ points, directionLevel d p = c := by
  rintro ⟨c, hall⟩
  exact not_all_pair_directions_eq_of_noncollinearSet hncoll
    ⟨d, by
      intro p hp q hq hpq
      exact direction_eq_of_directionLevel_eq hpq
        ((hall p hp).trans (hall q hq).symm)⟩



theorem directionsDeterminedBy_mono {A B : Finset Point2} (hAB : A ⊆ B) :
    directionsDeterminedBy A ⊆ directionsDeterminedBy B := by
  classical
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨pq, hpq_mem, hpq_dir⟩
  rcases pq with ⟨p, q⟩
  rcases Finset.mem_filter.mp hpq_mem with ⟨hpq_prod, hpq_ne⟩
  rcases Finset.mem_product.mp hpq_prod with ⟨hpA, hqA⟩
  refine Finset.mem_image.mpr ⟨(p, q), ?_, hpq_dir⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hAB hpA, hAB hqA⟩, hpq_ne⟩



theorem exists_erase_noncollinear {points : Finset Point2}
    (hcard : 3 < points.card) (hncoll : NoncollinearSet points) :
    ∃ x ∈ points, NoncollinearSet (points.erase x) := by
  classical
  rcases hncoll with ⟨p, hp, q, hq, r, hr, hnon⟩
  let T : Finset Point2 := {p, q, r}
  have hexists : ∃ x ∈ points, x ∉ T := by
    by_contra hnot
    push Not at hnot
    have hsub : points ⊆ T := by
      intro x hx
      exact hnot x hx
    have hle : points.card ≤ T.card := Finset.card_le_card hsub
    have hT : T.card ≤ 3 := by
      dsimp [T]
      exact Finset.card_le_three
    omega
  rcases hexists with ⟨x, hxpoints, hxnotT⟩
  have hxnep : x ≠ p := by
    intro h
    exact hxnotT (by simp [T, h])
  have hxneq : x ≠ q := by
    intro h
    exact hxnotT (by simp [T, h])
  have hxner : x ≠ r := by
    intro h
    exact hxnotT (by simp [T, h])
  refine ⟨x, hxpoints, p, ?_, q, ?_, r, ?_, hnon⟩
  · exact Finset.mem_erase.mpr ⟨hxnep.symm, hp⟩
  · exact Finset.mem_erase.mpr ⟨hxneq.symm, hq⟩
  · exact Finset.mem_erase.mpr ⟨hxner.symm, hr⟩























/--
Book reduction, direction version: if every even non-collinear set determines
at least as many directions as points, then every non-collinear set of size at
least four determines at least `n - 1` directions.
-/
theorem directions_lower_bound_of_even_direction_bound (points : Finset Point2)
    (hcard : 4 ≤ points.card) (hncoll : NoncollinearSet points)
    (heven_bound : ∀ S : Finset Point2, Even S.card → NoncollinearSet S →
      S.card ≤ (directionsDeterminedBy S).card) :
    points.card - 1 ≤ (directionsDeterminedBy points).card := by
  classical
  by_cases hEven : Even points.card
  · have hdirs := heven_bound points hEven hncoll
    omega
  · obtain ⟨x, hx, hncollErase⟩ :=
      exists_erase_noncollinear (points := points) (by omega) hncoll
    have hcardErase : (points.erase x).card = points.card - 1 :=
      Finset.card_erase_of_mem hx
    have hEvenErase : Even (points.erase x).card := by
      rw [hcardErase, Nat.even_sub (by omega : 1 ≤ points.card)]
      simp [hEven]
    have hdirsErase := heven_bound (points.erase x) hEvenErase hncollErase
    have hmono : directionsDeterminedBy (points.erase x) ⊆ directionsDeterminedBy points :=
      directionsDeterminedBy_mono (Finset.erase_subset x points)
    have hcardDirs :
        (directionsDeterminedBy (points.erase x)).card ≤
          (directionsDeterminedBy points).card :=
      Finset.card_le_card hmono
    omega

theorem directions_lower_bound_three (points : Finset Point2)
    (hcard : points.card = 3) (hncoll : NoncollinearSet points) :
    points.card - 1 ≤ (directionsDeterminedBy points).card := by
  classical
  rcases hncoll with ⟨p, hp, q, hq, r, hr, hnon⟩
  let witness : Bool → Direction := fun b => cond b (direction p r) (direction p q)
  have hwitness : ∀ b, witness b ∈ directionsDeterminedBy points := by
    intro b
    cases b
    · exact direction_mem_directionsDeterminedBy hp hq
        (left_ne_right_of_noncollinear hnon)
    · exact direction_mem_directionsDeterminedBy hp hr
        (left_ne_third_of_noncollinear hnon)
  have hinj : Function.Injective witness := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exfalso
      have hdir : direction p q = direction p r := by
        simpa [witness] using hab
      exact hnon (determinant_eq_zero_of_same_direction_from_left hdir)
    · exfalso
      have hdir : direction p q = direction p r := by
        simpa [witness] using hab.symm
      exact hnon (determinant_eq_zero_of_same_direction_from_left hdir)
    · rfl
  have htwo : Fintype.card Bool ≤ (directionsDeterminedBy points).card := by
    exact Finset.card_le_card_of_injOn witness (by intro b _hb; exact hwitness b)
      (by intro a _ha b _hb h; exact hinj h)
  rw [hcard]
  norm_num at htwo ⊢
  exact htwo



theorem directions_lower_bound_of_even_direction_bound_all (points : Finset Point2)
    (hcard : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (heven_bound : ∀ S : Finset Point2, Even S.card → NoncollinearSet S →
      S.card ≤ (directionsDeterminedBy S).card) :
    points.card - 1 ≤ (directionsDeterminedBy points).card := by
  by_cases hthree : points.card = 3
  · exact directions_lower_bound_three points hthree hncoll
  · exact directions_lower_bound_of_even_direction_bound points (by omega) hncoll heven_bound

theorem directions_floor_lower_bound_of_even_direction_bound_all (points : Finset Point2)
    (hcard : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (heven_bound : ∀ S : Finset Point2, Even S.card → NoncollinearSet S →
      S.card ≤ (directionsDeterminedBy S).card) :
    2 * (points.card / 2) ≤ (directionsDeterminedBy points).card := by
  classical
  by_cases hEven : Even points.card
  · rcases hEven with ⟨m, hm⟩
    have hfloor : 2 * (points.card / 2) = points.card := by
      rw [hm]
      have hdiv : (m + m) / 2 = m := by
        rw [← two_mul m]
        exact Nat.mul_div_right m (by norm_num : 0 < 2)
      rw [hdiv]
      omega
    rw [hfloor]
    exact heven_bound points ⟨m, hm⟩ hncoll
  · have hprev :=
      directions_lower_bound_of_even_direction_bound_all points hcard hncoll heven_bound
    have hodd : points.card % 2 = 1 := Nat.not_even_iff.mp hEven
    rw [Nat.two_mul_odd_div_two hodd]
    exact hprev



theorem UngarCountingCertificate.length_lower_bound {n t : ℕ}
    (cert : UngarCountingCertificate n t) : n ≤ t :=
  le_trans cert.letters_cross cert.blocks_fit



























































/-! ### Finite allowable-sequence vocabulary -/





















namespace GeneralizedAllowableSequence





theorem crossingLabelsCard_eq_two_mul_of_refl_reverse {k r : ℕ}
    (A : GeneralizedAllowableSequence k r) (j : Fin r)
    (hsource : A.π (stepFrom j) = Equiv.refl (Fin (2 * k)))
    (htarget : A.π (stepTo j) = reverseFin (2 * k)) :
    A.crossingLabelsCard j = 2 * k := by
  classical
  unfold crossingLabelsCard
  rw [hsource, htarget]
  simp [crossesMiddle, middleLeft_reverseFin_symm_iff_not]









end GeneralizedAllowableSequence

/-! ### Sweep → GeneralizedAllowableSequence bridge -/









/-! ### Consecutive block moves -/



namespace PositionInterval

















theorem mirror_strictAnti {N : ℕ} (I : PositionInterval N)
    {p q : Fin N} (hp : I.Mem p) (hq : I.Mem q) (hpq : p < q) :
    I.mirror q hq < I.mirror p hp := by
  rcases hp with ⟨hplo, hphi⟩
  rcases hq with ⟨hqlo, hqhi⟩
  change (I.mirror q ⟨hqlo, hqhi⟩).val < (I.mirror p ⟨hplo, hphi⟩).val
  dsimp [mirror]
  omega







theorem toFinset_card {N : ℕ} (I : PositionInterval N) :
    I.toFinset.card = I.length := by
  classical
  let e : Fin N ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  have hmap : I.toFinset.map e = Finset.Icc I.lo I.hi := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
      rw [mem_toFinset] at hp
      simp [e] at hpval
      subst n
      exact Finset.mem_Icc.mpr hp
    · intro hn
      rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
      have hnlt : n < N := lt_of_le_of_lt hhi I.hi_lt
      refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
      · rw [mem_toFinset]
        exact ⟨hlo, hhi⟩
      · simp [e]
  have hcard_map : (I.toFinset.map e).card = I.toFinset.card :=
    Finset.card_map e
  rw [hmap] at hcard_map
  rw [← hcard_map]
  simp [length]



























theorem crossOrder_le_left {k : ℕ} (I : PositionInterval (2 * k)) :
    I.crossOrder k ≤ k - I.lo := by
  by_cases h : I.lo < k ∧ k ≤ I.hi
  · rw [crossOrder_eq_min_of_crossing h]
    exact Nat.min_le_left _ _
  · rw [crossOrder_eq_zero_of_not_crossing h]
    omega

theorem crossOrder_le_right {k : ℕ} (I : PositionInterval (2 * k)) :
    I.crossOrder k ≤ I.hi + 1 - k := by
  by_cases h : I.lo < k ∧ k ≤ I.hi
  · rw [crossOrder_eq_min_of_crossing h]
    exact Nat.min_le_right _ _
  · rw [crossOrder_eq_zero_of_not_crossing h]
    omega

theorem eq_full_of_crossOrder_eq_middle {k : ℕ} (I : PositionInterval (2 * k))
    (hk : 0 < k) (horder : I.crossOrder k = k) :
    I.lo = 0 ∧ I.hi = 2 * k - 1 := by
  have hleft := I.crossOrder_le_left
  have hright := I.crossOrder_le_right
  have hhi := I.hi_lt
  rw [horder] at hleft hright
  omega















theorem mem_leftBarrierPositions {k d : ℕ} {p : Fin (2 * k)} :
    p ∈ leftBarrierPositions k d ↔ k - d ≤ p.val ∧ p.val < k := by
  simp [leftBarrierPositions]

theorem mem_rightBarrierPositions {k d : ℕ} {p : Fin (2 * k)} :
    p ∈ rightBarrierPositions k d ↔ k ≤ p.val ∧ p.val < k + d := by
  simp [rightBarrierPositions]

theorem mem_centralBarrierPositions {k d : ℕ} {p : Fin (2 * k)} :
    p ∈ centralBarrierPositions k d ↔
      (k - d ≤ p.val ∧ p.val < k) ∨ (k ≤ p.val ∧ p.val < k + d) := by
  simp [centralBarrierPositions, mem_leftBarrierPositions, mem_rightBarrierPositions]

theorem left_rightBarrierPositions_disjoint {k d : ℕ} :
    Disjoint (leftBarrierPositions k d) (rightBarrierPositions k d) := by
  rw [Finset.disjoint_left]
  intro p hp_left hp_right
  rw [mem_leftBarrierPositions] at hp_left
  rw [mem_rightBarrierPositions] at hp_right
  omega

theorem leftBarrierPositions_card_eq {k d : ℕ} (hd : d ≤ k) :
    (leftBarrierPositions k d).card = d := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  have hmap :
      (leftBarrierPositions k d).map e = Finset.Ico (k - d) k := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
      rw [mem_leftBarrierPositions] at hp
      simp [e] at hpval
      subst n
      exact Finset.mem_Ico.mpr hp
    · intro hn
      rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
      have hnlt : n < 2 * k := lt_trans hhi (by omega : k < 2 * k)
      refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
      · rw [mem_leftBarrierPositions]
        exact ⟨hlo, hhi⟩
      · simp [e]
  have hcard_map : ((leftBarrierPositions k d).map e).card =
      (leftBarrierPositions k d).card := Finset.card_map e
  rw [hmap] at hcard_map
  rw [← hcard_map]
  simp
  omega

theorem rightBarrierPositions_card_eq {k d : ℕ} (hd : d ≤ k) :
    (rightBarrierPositions k d).card = d := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  have hmap :
      (rightBarrierPositions k d).map e = Finset.Ico k (k + d) := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
      rw [mem_rightBarrierPositions] at hp
      simp [e] at hpval
      subst n
      exact Finset.mem_Ico.mpr hp
    · intro hn
      rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
      have hnlt : n < 2 * k := by omega
      refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
      · rw [mem_rightBarrierPositions]
        exact ⟨hlo, hhi⟩
      · simp [e]
  have hcard_map : ((rightBarrierPositions k d).map e).card =
      (rightBarrierPositions k d).card := Finset.card_map e
  rw [hmap] at hcard_map
  rw [← hcard_map]
  simp

theorem centralBarrierPositions_card_eq {k d : ℕ} (hd : d ≤ k) :
    (centralBarrierPositions k d).card = 2 * d := by
  rw [centralBarrierPositions, Finset.card_union_of_disjoint left_rightBarrierPositions_disjoint]
  rw [leftBarrierPositions_card_eq hd, rightBarrierPositions_card_eq hd]
  omega





theorem centralBarrierPositions_mono {k d e : ℕ} (hde : d ≤ e) :
    centralBarrierPositions k d ⊆ centralBarrierPositions k e := by
  intro p hp
  rw [mem_centralBarrierPositions] at hp ⊢
  rcases hp with hp | hp
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem pred_mem_centralBarrierPositions_of_mem_pred {k d : ℕ}
    {p : Fin (2 * k)} (hp : p ∈ centralBarrierPositions k (d - 1))
    (hp_pos : 0 < p.val) :
    (⟨p.val - 1, by omega⟩ : Fin (2 * k)) ∈ centralBarrierPositions k d := by
  rw [mem_centralBarrierPositions] at hp ⊢
  rcases hp with hp | hp
  · refine Or.inl ?_
    change k - d ≤ p.val - 1 ∧ p.val - 1 < k
    omega
  · by_cases hpk : p.val = k
    · refine Or.inl ?_
      change k - d ≤ p.val - 1 ∧ p.val - 1 < k
      omega
    · refine Or.inr ?_
      change k ≤ p.val - 1 ∧ p.val - 1 < k + d
      omega

theorem succ_mem_centralBarrierPositions_of_mem_pred {k d : ℕ}
    {p : Fin (2 * k)} (hp : p ∈ centralBarrierPositions k (d - 1))
    (hp_succ : p.val + 1 < 2 * k) :
    (⟨p.val + 1, hp_succ⟩ : Fin (2 * k)) ∈ centralBarrierPositions k d := by
  rw [mem_centralBarrierPositions] at hp ⊢
  rcases hp with hp | hp
  · by_cases hpk : p.val + 1 = k
    · refine Or.inr ?_
      change k ≤ p.val + 1 ∧ p.val + 1 < k + d
      omega
    · refine Or.inl ?_
      change k - d ≤ p.val + 1 ∧ p.val + 1 < k
      omega
  · refine Or.inr ?_
    change k ≤ p.val + 1 ∧ p.val + 1 < k + d
    omega











theorem two_mul_crossOrder_le_length {k : ℕ} (I : PositionInterval (2 * k)) :
    2 * I.crossOrder k ≤ I.length := by
  by_cases h : I.lo < k ∧ k ≤ I.hi
  · rw [crossOrder_eq_min_of_crossing h]
    have hleft : Nat.min (k - I.lo) (I.hi + 1 - k) ≤ k - I.lo :=
      Nat.min_le_left _ _
    have hright : Nat.min (k - I.lo) (I.hi + 1 - k) ≤ I.hi + 1 - k :=
      Nat.min_le_right _ _
    have hlen : I.length = (k - I.lo) + (I.hi + 1 - k) := by
      dsimp [length]
      omega
    rw [hlen]
    omega
  · rw [crossOrder_eq_zero_of_not_crossing h]
    omega



end PositionInterval



namespace BlockMove













theorem pairwise_disjoint_toFinset {N : ℕ} (M : BlockMove N) :
    ((Finset.univ : Finset (Fin M.blockCount)) : Set (Fin M.blockCount)).PairwiseDisjoint
      (fun i => (M.block i).toFinset) := by
  classical
  intro i _hi j _hj hij
  change Disjoint (M.block i).toFinset (M.block j).toFinset
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hset_dis : Disjoint ((M.block i).toSet) ((M.block j).toSet) :=
    M.pairwise_disjoint (by simp) (by simp) hij
  have hpi_set : p ∈ (M.block i).toSet := by
    simpa [PositionInterval.toSet, PositionInterval.mem_toFinset] using hpi
  have hpj_set : p ∈ (M.block j).toSet := by
    simpa [PositionInterval.toSet, PositionInterval.mem_toFinset] using hpj
  exact hset_dis.le_bot ⟨hpi_set, hpj_set⟩

/-- Pairwise-disjoint blocks in `Fin N` have total length at most `N`. -/
theorem sum_block_lengths_le {N : ℕ} (M : BlockMove N) :
    (∑ i : Fin M.blockCount, (M.block i).length) ≤ N := by
  classical
  have hcard :
      ((Finset.univ : Finset (Fin M.blockCount)).biUnion
        (fun i => (M.block i).toFinset)).card =
        ∑ i : Fin M.blockCount, ((M.block i).toFinset).card := by
    simpa using
      (Finset.card_biUnion (s := (Finset.univ : Finset (Fin M.blockCount)))
        (t := fun i => (M.block i).toFinset) M.pairwise_disjoint_toFinset)
  have hle :
      ((Finset.univ : Finset (Fin M.blockCount)).biUnion
        (fun i => (M.block i).toFinset)).card ≤ N := by
    simpa [Fintype.card_fin] using
      (((Finset.univ : Finset (Fin M.blockCount)).biUnion
        (fun i => (M.block i).toFinset)).card_le_univ)
  rw [hcard] at hle
  simpa [PositionInterval.toFinset_card] using hle



end BlockMove

/-! ### BlockMove from level function -/









namespace ReversalStep





theorem label_decreases_after_block_of_reversesBlocks {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (i : Fin M.move.blockCount)
    {p q : Fin (2 * k)} (hp : (M.move.block i).Mem p) (hq : (M.move.block i).Mem q)
    (hpq : p < q) :
    (ρ q).val < (ρ p).val := by
  have hmirror_lt :
      (M.move.block i).mirror q hq < (M.move.block i).mirror p hp :=
    (M.move.block i).mirror_strictAnti hp hq hpq
  have hmono :=
    M.increasing_before i ((M.move.block i).mirror_mem q hq)
      ((M.move.block i).mirror_mem p hp) hmirror_lt
  rw [M.step_apply q, M.step_apply p]
  rw [hrev.1 i q hq, hrev.1 i p hp]
  exact hmono





theorem DecreasingOnPositions.mono {N : ℕ} {π : State N} {s t : Finset (Fin N)}
    (hdec : DecreasingOnPositions π t) (hst : s ⊆ t) :
    DecreasingOnPositions π s := by
  intro p hp q hq hpq
  exact hdec (hst hp) (hst hq) hpq

theorem IncreasingOnPositions.mono {N : ℕ} {π : State N} {s t : Finset (Fin N)}
    (hinc : IncreasingOnPositions π t) (hst : s ⊆ t) :
    IncreasingOnPositions π s := by
  intro p hp q hq hpq
  exact hinc (hst hp) (hst hq) hpq

theorem state_eq_refl_of_increasingOn_univ {N : ℕ} {π : State N}
    (hinc : IncreasingOnPositions π Finset.univ) :
    π = Equiv.refl (Fin N) := by
  apply Equiv.ext
  intro p
  have hmono : StrictMono (fun x : Fin N => π x) := by
    intro a b hab
    change (π a).val < (π b).val
    exact hinc (by simp) (by simp) hab
  have hπ :
      (fun x : Fin N => π x) =
        (Finset.univ : Finset (Fin N)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin N)))
      (k := N) (by simp) (fun _ => by simp) hmono
  have hid :
      (fun x : Fin N => x) =
        (Finset.univ : Finset (Fin N)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin N)))
      (k := N) (by simp) (fun _ => by simp) (by intro a b hab; exact hab)
  have hfun : (fun x : Fin N => π x) = fun x : Fin N => x := hπ.trans hid.symm
  exact congrFun hfun p

theorem state_eq_reverseFin_of_decreasingOn_univ {N : ℕ} {π : State N}
    (hdec : DecreasingOnPositions π Finset.univ) :
    π = reverseFin N := by
  apply Equiv.ext
  intro p
  have hmono : StrictMono (fun x : Fin N => π (Fin.rev x)) := by
    intro a b hab
    have hrev : Fin.rev b < Fin.rev a := by
      rw [← Fin.rev_lt_rev]
      simpa using hab
    change (π (Fin.rev a)).val < (π (Fin.rev b)).val
    exact hdec (by simp) (by simp) hrev
  have hπ :
      (fun x : Fin N => π (Fin.rev x)) =
        (Finset.univ : Finset (Fin N)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin N)))
      (k := N) (by simp) (fun _ => by simp) hmono
  have hid :
      (fun x : Fin N => x) =
        (Finset.univ : Finset (Fin N)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin N)))
      (k := N) (by simp) (fun _ => by simp) (by intro a b hab; exact hab)
  have hfun : (fun x : Fin N => π (Fin.rev x)) = fun x : Fin N => x :=
    hπ.trans hid.symm
  have hp := congrFun hfun (Fin.rev p)
  simpa [reverseFin] using hp





























theorem not_increasing_and_decreasing_on_two_positions {N : ℕ}
    {π : State N} {s : Finset (Fin N)}
    (hinc : IncreasingOnPositions π s) (hdec : DecreasingOnPositions π s)
    (hcard : 2 ≤ s.card) :
    False := by
  have hcard' : 1 < s.card := by omega
  rcases Finset.one_lt_card.mp hcard' with ⟨p, hp, q, hq, hpq⟩
  rcases lt_or_gt_of_ne hpq with hpq_lt | hqp_lt
  · have hlt1 := hinc hp hq hpq_lt
    have hlt2 := hdec hp hq hpq_lt
    omega
  · have hlt1 := hinc hq hp hqp_lt
    have hlt2 := hdec hq hp hqp_lt
    omega

theorem card_inter_le_one_of_increasing_decreasing {N : ℕ}
    {π : State N} {s t : Finset (Fin N)}
    (hinc : IncreasingOnPositions π t) (hdec : DecreasingOnPositions π s) :
    (s ∩ t).card ≤ 1 := by
  by_contra hnot
  have htwo : 2 ≤ (s ∩ t).card := by omega
  have hinc_inter : IncreasingOnPositions π (s ∩ t) :=
    hinc.mono (by intro p hp; exact (Finset.mem_inter.mp hp).2)
  have hdec_inter : DecreasingOnPositions π (s ∩ t) :=
    hdec.mono (by intro p hp; exact (Finset.mem_inter.mp hp).1)
  exact not_increasing_and_decreasing_on_two_positions hinc_inter hdec_inter htwo

theorem increasing_before_block {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (i : Fin M.move.blockCount) :
    IncreasingOnPositions π (M.move.block i).toFinset := by
  intro p hp q hq hpq
  rw [PositionInterval.mem_toFinset] at hp hq
  exact M.increasing_before i hp hq hpq

theorem block_inter_central_le_one_of_decreasing_before {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (i : Fin M.move.blockCount)
    (hdec : DecreasingOnPositions π (PositionInterval.centralBarrierPositions k d)) :
    (PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset).card ≤ 1 :=
  card_inter_le_one_of_increasing_decreasing (M.increasing_before_block i) hdec

theorem ne_of_mem_block_and_central_contradicts_decreasing_before {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (i : Fin M.move.blockCount)
    (hdec : DecreasingOnPositions π (PositionInterval.centralBarrierPositions k d))
    {p q : Fin (2 * k)}
    (hpC : p ∈ PositionInterval.centralBarrierPositions k d)
    (hqC : q ∈ PositionInterval.centralBarrierPositions k d)
    (hpB : (M.move.block i).Mem p) (hqB : (M.move.block i).Mem q)
    (hpq : p ≠ q) :
    False := by
  have hle := M.block_inter_central_le_one_of_decreasing_before i hdec
  have hp_inter :
      p ∈ PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset := by
    rw [Finset.mem_inter, PositionInterval.mem_toFinset]
    exact ⟨hpC, hpB⟩
  have hq_inter :
      q ∈ PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset := by
    rw [Finset.mem_inter, PositionInterval.mem_toFinset]
    exact ⟨hqC, hqB⟩
  have htwo :
      1 < (PositionInterval.centralBarrierPositions k d ∩
        (M.move.block i).toFinset).card :=
    Finset.one_lt_card.mpr ⟨p, hp_inter, q, hq_inter, hpq⟩
  omega

theorem fixed_on_smaller_central_of_decreasing_before_nonCrossing {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing)
    (hdec : DecreasingOnPositions π (PositionInterval.centralBarrierPositions k d))
    {p : Fin (2 * k)} (hp : p ∈ PositionInterval.centralBarrierPositions k (d - 1)) :
    M.move.map p = p := by
  classical
  have hp_big : p ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hp
  by_cases hmem : ∃ i : Fin M.move.blockCount, (M.move.block i).Mem p
  · rcases hmem with ⟨i, hpi⟩
    have hnot_cross_i :
        ¬ ((M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi) := by
      intro hi
      apply hM
      unfold IsCrossing order
      rw [Finset.sum_pos_iff]
      exact ⟨i, by simp, (M.move.block i).crossOrder_pos_iff.mpr hi⟩
    have hmap : M.move.map p = (M.move.block i).mirror p hpi := hrev.1 i p hpi
    by_contra hneq
    have hval_ne : (M.move.map p).val ≠ p.val := by
      intro hval
      exact hneq (Fin.ext hval)
    rcases lt_or_gt_of_ne hval_ne with hlt | hgt
    · have hp_pos : 0 < p.val := by
        rw [hmap] at hlt
        change (M.move.block i).lo + (M.move.block i).hi - p.val < p.val at hlt
        omega
      let q : Fin (2 * k) := ⟨p.val - 1, by omega⟩
      have hq_block : (M.move.block i).Mem q := by
        rw [hmap] at hlt
        change (M.move.block i).lo + (M.move.block i).hi - p.val < p.val at hlt
        rcases hpi with ⟨hlo, hhi⟩
        dsimp [q]
        change (M.move.block i).lo ≤ p.val - 1 ∧
          p.val - 1 ≤ (M.move.block i).hi
        constructor <;> omega
      have hq_big : q ∈ PositionInterval.centralBarrierPositions k d := by
        dsimp [q]
        exact PositionInterval.pred_mem_centralBarrierPositions_of_mem_pred hp hp_pos
      have hpq : p ≠ q := by
        intro hpq
        have hval := congrArg Fin.val hpq
        dsimp [q] at hval
        omega
      exact M.ne_of_mem_block_and_central_contradicts_decreasing_before i hdec
        hp_big hq_big hpi hq_block hpq
    · have hp_succ : p.val + 1 < 2 * k := by
        rw [hmap] at hgt
        have hmirror_lt : ((M.move.block i).mirror p hpi).val < 2 * k :=
          (M.move.block i).mirror p hpi |>.isLt
        change p.val < (M.move.block i).lo + (M.move.block i).hi - p.val at hgt
        rcases hpi with ⟨hlo, hhi⟩
        have hhi_lt := (M.move.block i).hi_lt
        omega
      let q : Fin (2 * k) := ⟨p.val + 1, hp_succ⟩
      have hq_block : (M.move.block i).Mem q := by
        rw [hmap] at hgt
        change p.val < (M.move.block i).lo + (M.move.block i).hi - p.val at hgt
        rcases hpi with ⟨hlo, hhi⟩
        dsimp [q]
        change (M.move.block i).lo ≤ p.val + 1 ∧
          p.val + 1 ≤ (M.move.block i).hi
        constructor <;> omega
      have hq_big : q ∈ PositionInterval.centralBarrierPositions k d := by
        dsimp [q]
        exact PositionInterval.succ_mem_centralBarrierPositions_of_mem_pred hp hp_succ
      have hpq : p ≠ q := by
        intro hpq
        have hval := congrArg Fin.val hpq
        dsimp [q] at hval
        omega
      exact M.ne_of_mem_block_and_central_contradicts_decreasing_before i hdec
        hp_big hq_big hpi hq_block hpq
  · exact hrev.2 p (by
      intro i hi
      exact hmem ⟨i, hi⟩)

theorem decreasing_after_smaller_central_of_decreasing_before_nonCrossing {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing)
    (hdec : DecreasingOnPositions π (PositionInterval.centralBarrierPositions k d)) :
    DecreasingOnPositions ρ (PositionInterval.centralBarrierPositions k (d - 1)) := by
  intro p hp q hq hpq
  have hp_big : p ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hp
  have hq_big : q ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hq
  have hfixp := M.fixed_on_smaller_central_of_decreasing_before_nonCrossing
    hrev hM hdec hp
  have hfixq := M.fixed_on_smaller_central_of_decreasing_before_nonCrossing
    hrev hM hdec hq
  rw [M.step_apply q, M.step_apply p, hfixq, hfixp]
  exact hdec hp_big hq_big hpq

theorem decreasing_after_block_of_reversesBlocks {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (i : Fin M.move.blockCount) :
    DecreasingOnPositions ρ (M.move.block i).toFinset := by
  intro p hp q hq hpq
  rw [PositionInterval.mem_toFinset] at hp hq
  exact M.label_decreases_after_block_of_reversesBlocks hrev i hp hq hpq

theorem block_inter_central_le_one_of_increasing_after {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (i : Fin M.move.blockCount)
    (hinc : IncreasingOnPositions ρ (PositionInterval.centralBarrierPositions k d)) :
    (PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset).card ≤ 1 :=
  by
    have hle := card_inter_le_one_of_increasing_decreasing hinc
      (M.decreasing_after_block_of_reversesBlocks hrev i)
    simpa [Finset.inter_comm] using hle

theorem ne_of_mem_block_and_central_contradicts_increasing_after {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (i : Fin M.move.blockCount)
    (hinc : IncreasingOnPositions ρ (PositionInterval.centralBarrierPositions k d))
    {p q : Fin (2 * k)}
    (hpC : p ∈ PositionInterval.centralBarrierPositions k d)
    (hqC : q ∈ PositionInterval.centralBarrierPositions k d)
    (hpB : (M.move.block i).Mem p) (hqB : (M.move.block i).Mem q)
    (hpq : p ≠ q) :
    False := by
  have hle := M.block_inter_central_le_one_of_increasing_after hrev i hinc
  have hp_inter :
      p ∈ PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset := by
    rw [Finset.mem_inter, PositionInterval.mem_toFinset]
    exact ⟨hpC, hpB⟩
  have hq_inter :
      q ∈ PositionInterval.centralBarrierPositions k d ∩ (M.move.block i).toFinset := by
    rw [Finset.mem_inter, PositionInterval.mem_toFinset]
    exact ⟨hqC, hqB⟩
  have htwo :
      1 < (PositionInterval.centralBarrierPositions k d ∩
        (M.move.block i).toFinset).card :=
    Finset.one_lt_card.mpr ⟨p, hp_inter, q, hq_inter, hpq⟩
  omega

theorem fixed_on_smaller_central_of_increasing_after_nonCrossing {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing)
    (hinc : IncreasingOnPositions ρ (PositionInterval.centralBarrierPositions k d))
    {p : Fin (2 * k)} (hp : p ∈ PositionInterval.centralBarrierPositions k (d - 1)) :
    M.move.map p = p := by
  classical
  have hp_big : p ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hp
  by_cases hmem : ∃ i : Fin M.move.blockCount, (M.move.block i).Mem p
  · rcases hmem with ⟨i, hpi⟩
    have hnot_cross_i :
        ¬ ((M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi) := by
      intro hi
      apply hM
      unfold IsCrossing order
      rw [Finset.sum_pos_iff]
      exact ⟨i, by simp, (M.move.block i).crossOrder_pos_iff.mpr hi⟩
    have hmap : M.move.map p = (M.move.block i).mirror p hpi := hrev.1 i p hpi
    by_contra hneq
    have hval_ne : (M.move.map p).val ≠ p.val := by
      intro hval
      exact hneq (Fin.ext hval)
    rcases lt_or_gt_of_ne hval_ne with hlt | hgt
    · have hp_pos : 0 < p.val := by
        rw [hmap] at hlt
        change (M.move.block i).lo + (M.move.block i).hi - p.val < p.val at hlt
        omega
      let q : Fin (2 * k) := ⟨p.val - 1, by omega⟩
      have hq_block : (M.move.block i).Mem q := by
        rw [hmap] at hlt
        change (M.move.block i).lo + (M.move.block i).hi - p.val < p.val at hlt
        rcases hpi with ⟨hlo, hhi⟩
        dsimp [q]
        change (M.move.block i).lo ≤ p.val - 1 ∧
          p.val - 1 ≤ (M.move.block i).hi
        constructor <;> omega
      have hq_big : q ∈ PositionInterval.centralBarrierPositions k d := by
        dsimp [q]
        exact PositionInterval.pred_mem_centralBarrierPositions_of_mem_pred hp hp_pos
      have hpq : p ≠ q := by
        intro hpq
        have hval := congrArg Fin.val hpq
        dsimp [q] at hval
        omega
      exact M.ne_of_mem_block_and_central_contradicts_increasing_after hrev i hinc
        hp_big hq_big hpi hq_block hpq
    · have hp_succ : p.val + 1 < 2 * k := by
        rw [hmap] at hgt
        change p.val < (M.move.block i).lo + (M.move.block i).hi - p.val at hgt
        rcases hpi with ⟨hlo, hhi⟩
        have hhi_lt := (M.move.block i).hi_lt
        omega
      let q : Fin (2 * k) := ⟨p.val + 1, hp_succ⟩
      have hq_block : (M.move.block i).Mem q := by
        rw [hmap] at hgt
        change p.val < (M.move.block i).lo + (M.move.block i).hi - p.val at hgt
        rcases hpi with ⟨hlo, hhi⟩
        dsimp [q]
        change (M.move.block i).lo ≤ p.val + 1 ∧
          p.val + 1 ≤ (M.move.block i).hi
        constructor <;> omega
      have hq_big : q ∈ PositionInterval.centralBarrierPositions k d := by
        dsimp [q]
        exact PositionInterval.succ_mem_centralBarrierPositions_of_mem_pred hp hp_succ
      have hpq : p ≠ q := by
        intro hpq
        have hval := congrArg Fin.val hpq
        dsimp [q] at hval
        omega
      exact M.ne_of_mem_block_and_central_contradicts_increasing_after hrev i hinc
        hp_big hq_big hpi hq_block hpq
  · exact hrev.2 p (by
      intro i hi
      exact hmem ⟨i, hi⟩)

theorem increasing_before_smaller_central_of_increasing_after_nonCrossing {k d : ℕ}
    {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks)
    (hM : ¬ M.IsCrossing)
    (hinc : IncreasingOnPositions ρ (PositionInterval.centralBarrierPositions k d)) :
    IncreasingOnPositions π (PositionInterval.centralBarrierPositions k (d - 1)) := by
  intro p hp q hq hpq
  have hp_big : p ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hp
  have hq_big : q ∈ PositionInterval.centralBarrierPositions k d :=
    PositionInterval.centralBarrierPositions_mono (Nat.sub_le d 1) hq
  have hfixp := M.fixed_on_smaller_central_of_increasing_after_nonCrossing
    hrev hM hinc hp
  have hfixq := M.fixed_on_smaller_central_of_increasing_after_nonCrossing
    hrev hM hinc hq
  have hp_step := M.step_apply p
  have hq_step := M.step_apply q
  rw [hfixp] at hp_step
  rw [hfixq] at hq_step
  have h := hinc hp_big hq_big hpq
  rwa [hp_step, hq_step] at h













theorem crossingBlock_eq_full_of_order_eq_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing)
    (hk : 0 < k) (horder : M.order = k) :
    (M.move.block (M.crossingBlockIndex hM)).lo = 0 ∧
      (M.move.block (M.crossingBlockIndex hM)).hi = 2 * k - 1 := by
  have hcrossOrder :
      (M.move.block (M.crossingBlockIndex hM)).crossOrder k = k := by
    rw [← M.order_eq_crossingBlockIndex_crossOrder hM, horder]
  exact PositionInterval.eq_full_of_crossOrder_eq_middle
    (M.move.block (M.crossingBlockIndex hM)) hk hcrossOrder

theorem increasing_before_univ_of_order_eq_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing)
    (hk : 0 < k) (horder : M.order = k) :
    IncreasingOnPositions π Finset.univ := by
  intro p _hp q _hq hpq
  have hfull := M.crossingBlock_eq_full_of_order_eq_middle hM hk horder
  let b := M.crossingBlockIndex hM
  have hb_lo : (M.move.block b).lo = 0 := by
    simpa [b] using hfull.1
  have hb_hi : (M.move.block b).hi = 2 * k - 1 := by
    simpa [b] using hfull.2
  have hp : (M.move.block b).Mem p := by
    dsimp [PositionInterval.Mem]
    omega
  have hq : (M.move.block b).Mem q := by
    dsimp [PositionInterval.Mem]
    omega
  exact M.increasing_before b hp hq hpq

theorem decreasing_after_univ_of_order_eq_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing)
    (hk : 0 < k) (horder : M.order = k) :
    DecreasingOnPositions ρ Finset.univ := by
  intro p _hp q _hq hpq
  have hfull := M.crossingBlock_eq_full_of_order_eq_middle hM hk horder
  let b := M.crossingBlockIndex hM
  have hb_lo : (M.move.block b).lo = 0 := by
    simpa [b] using hfull.1
  have hb_hi : (M.move.block b).hi = 2 * k - 1 := by
    simpa [b] using hfull.2
  have hp : (M.move.block b).Mem p := by
    dsimp [PositionInterval.Mem]
    omega
  have hq : (M.move.block b).Mem q := by
    dsimp [PositionInterval.Mem]
    omega
  exact M.label_decreases_after_block_of_reversesBlocks hrev b hp hq hpq

theorem source_eq_refl_of_order_eq_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing)
    (hk : 0 < k) (horder : M.order = k) :
    π = Equiv.refl (Fin (2 * k)) :=
  state_eq_refl_of_increasingOn_univ
    (M.increasing_before_univ_of_order_eq_middle hM hk horder)

theorem target_eq_reverseFin_of_order_eq_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing)
    (hk : 0 < k) (horder : M.order = k) :
    ρ = reverseFin (2 * k) :=
  state_eq_reverseFin_of_decreasingOn_univ
    (M.decreasing_after_univ_of_order_eq_middle hrev hM hk horder)

































theorem increasing_before_centralBarrierPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    IncreasingOnPositions π (PositionInterval.centralBarrierPositions k M.order) := by
  intro p hp q hq hpq
  let b := M.crossingBlockIndex hM
  have hcross : (M.move.block b).lo < k ∧ k ≤ (M.move.block b).hi := by
    simpa [b] using M.crossingBlockIndex_spec hM
  have horder : M.order = (M.move.block b).crossOrder k := by
    simpa [b] using M.order_eq_crossingBlockIndex_crossOrder hM
  have hleft : (M.move.block b).crossOrder k ≤ k - (M.move.block b).lo :=
    (M.move.block b).crossOrder_le_left
  have hright : (M.move.block b).crossOrder k ≤ (M.move.block b).hi + 1 - k :=
    (M.move.block b).crossOrder_le_right
  have hpB : (M.move.block b).Mem p := by
    rw [PositionInterval.mem_centralBarrierPositions] at hp
    rw [horder] at hp
    rcases hp with hp | hp
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have hqB : (M.move.block b).Mem q := by
    rw [PositionInterval.mem_centralBarrierPositions] at hq
    rw [horder] at hq
    rcases hq with hq | hq
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  exact M.increasing_before b hpB hqB hpq

theorem decreasing_after_centralBarrierPositions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    DecreasingOnPositions ρ (PositionInterval.centralBarrierPositions k M.order) := by
  intro p hp q hq hpq
  let b := M.crossingBlockIndex hM
  have hcross : (M.move.block b).lo < k ∧ k ≤ (M.move.block b).hi := by
    simpa [b] using M.crossingBlockIndex_spec hM
  have horder : M.order = (M.move.block b).crossOrder k := by
    simpa [b] using M.order_eq_crossingBlockIndex_crossOrder hM
  have hleft : (M.move.block b).crossOrder k ≤ k - (M.move.block b).lo :=
    (M.move.block b).crossOrder_le_left
  have hright : (M.move.block b).crossOrder k ≤ (M.move.block b).hi + 1 - k :=
    (M.move.block b).crossOrder_le_right
  have hpB : (M.move.block b).Mem p := by
    rw [PositionInterval.mem_centralBarrierPositions] at hp
    rw [horder] at hp
    rcases hp with hp | hp
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  have hqB : (M.move.block b).Mem q := by
    rw [PositionInterval.mem_centralBarrierPositions] at hq
    rw [horder] at hq
    rcases hq with hq | hq
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  exact M.label_decreases_after_block_of_reversesBlocks hrev b hpB hqB hpq









































/-- The labels crossing in one reversal step fit inside the full position set. -/
theorem two_mul_order_le_positions {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) :
    2 * M.order ≤ 2 * k := by
  calc
    2 * M.order =
        ∑ i : Fin M.move.blockCount, 2 * (M.move.block i).crossOrder k := by
          simp [order, Finset.mul_sum]
    _ ≤ ∑ i : Fin M.move.blockCount, (M.move.block i).length := by
          exact Finset.sum_le_sum
            (by intro i _hi; exact PositionInterval.two_mul_crossOrder_le_length (M.move.block i))
    _ ≤ 2 * k := M.move.sum_block_lengths_le

theorem order_le_middle {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) :
    M.order ≤ k := by
  have h := M.two_mul_order_le_positions
  omega









theorem not_increasing_and_decreasing_centralBarrierPositions {k d : ℕ}
    {π : State (2 * k)} (hd : 0 < d) (hdk : d ≤ k)
    (hinc : IncreasingOnPositions π (PositionInterval.centralBarrierPositions k d))
    (hdec : DecreasingOnPositions π (PositionInterval.centralBarrierPositions k d)) :
    False :=
  not_increasing_and_decreasing_on_two_positions hinc hdec (by
    rw [PositionInterval.centralBarrierPositions_card_eq hdk]
    omega)

end ReversalStep





















namespace CountedGeneralizedAllowableSequence

























theorem moveOrder_eq_middle_of_directFullMove {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) {j : Fin r}
    (hsource : A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k)))
    (htarget : A.seq.π (stepTo j) = reverseFin (2 * k)) :
    A.moveOrder j = k := by
  have hcount := A.crossingLabelsCard_eq_two_mul_moveOrder j
  have hfull := A.seq.crossingLabelsCard_eq_two_mul_of_refl_reverse j hsource htarget
  rw [hfull] at hcount
  omega

theorem isCrossing_of_directFullMove {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (hk : 0 < k) {j : Fin r}
    (hsource : A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k)))
    (htarget : A.seq.π (stepTo j) = reverseFin (2 * k)) :
    A.IsCrossing j := by
  unfold IsCrossing
  rw [A.moveOrder_eq_middle_of_directFullMove hsource htarget]
  exact hk

























theorem not_isCrossing_between_crossingIdx_succ {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (i : ℕ) (hi : i + 1 < A.crossingMoves.card) {j : Fin r}
    (hlo : (A.crossingIdx ⟨i, by omega⟩).val < j.val)
    (hhi : j.val < (A.crossingIdx ⟨i + 1, by omega⟩).val) :
    ¬ A.IsCrossing j := by
  classical
  intro hjCross
  have hjmem : j ∈ A.crossingMoves := A.mem_crossingMoves.mpr hjCross
  have hmap :
      Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ =
        A.crossingMoves :=
    Finset.map_orderEmbOfFin_univ A.crossingMoves rfl
  have hjmap : j ∈ Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ := by
    rwa [hmap]
  rcases Finset.mem_map.mp hjmap with ⟨l, _hlmem, hlj⟩
  have hlj' : A.crossingIdx l = j := by
    simpa [crossingIdx] using hlj
  have hcases : l.val ≤ i ∨ i + 1 ≤ l.val := by omega
  rcases hcases with hle | hle
  · have hfinle : l ≤ (⟨i, by omega⟩ : Fin A.crossingMoves.card) := by
      change l.val ≤ i
      exact hle
    have hidxle : A.crossingIdx l ≤ A.crossingIdx ⟨i, by omega⟩ := by
      change (A.crossingMoves.orderEmbOfFin rfl l) ≤
        A.crossingMoves.orderEmbOfFin rfl ⟨i, by omega⟩
      exact (A.crossingMoves.orderEmbOfFin rfl).monotone hfinle
    have hvalle : j.val ≤ (A.crossingIdx ⟨i, by omega⟩).val := by
      have hvaleq : (A.crossingIdx l).val = j.val := congrArg Fin.val hlj'
      have hidxle_val : (A.crossingIdx l).val ≤ (A.crossingIdx ⟨i, by omega⟩).val :=
        hidxle
      omega
    omega
  · have hfinle : (⟨i + 1, by omega⟩ : Fin A.crossingMoves.card) ≤ l := by
      change i + 1 ≤ l.val
      exact hle
    have hidxle : A.crossingIdx ⟨i + 1, by omega⟩ ≤ A.crossingIdx l := by
      change (A.crossingMoves.orderEmbOfFin rfl ⟨i + 1, by omega⟩) ≤
        A.crossingMoves.orderEmbOfFin rfl l
      exact (A.crossingMoves.orderEmbOfFin rfl).monotone hfinle
    have hvalle : (A.crossingIdx ⟨i + 1, by omega⟩).val ≤ j.val := by
      have hvaleq : (A.crossingIdx l).val = j.val := congrArg Fin.val hlj'
      have hidxle_val : (A.crossingIdx ⟨i + 1, by omega⟩).val ≤
          (A.crossingIdx l).val :=
        hidxle
      omega
    omega





theorem consecutive_crossingIdx_succ {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (i : ℕ) (hi : i + 1 < A.crossingMoves.card) :
    A.ConsecutiveCrossing (A.crossingIdx ⟨i, by omega⟩)
      (A.crossingIdx ⟨i + 1, by omega⟩) := by
  refine ⟨A.crossingIdx_isCrossing _, A.crossingIdx_isCrossing _, ?_, ?_⟩
  · have hfinlt :
        (⟨i, by omega⟩ : Fin A.crossingMoves.card) <
          (⟨i + 1, by omega⟩ : Fin A.crossingMoves.card) := by
        change i < i + 1
        omega
    exact A.crossingIdx_strict hfinlt
  · intro l hlo hhi
    exact A.not_isCrossing_between_crossingIdx_succ i hi hlo hhi















/--
The finite Ungar conclusion extracted from a counted sequence once the T/O/C
gap inequalities have been proved for the ordered crossing moves.
-/
theorem length_lower_bound_from_gaps {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (htwo : 2 ≤ A.crossingMoves.card)
    (hgap_between :
      ∀ (i : ℕ) (hi : i + 1 < A.crossingMoves.card),
        A.moveOrder (A.crossingIdx ⟨i, by omega⟩) +
            A.moveOrder (A.crossingIdx ⟨i + 1, by omega⟩) - 1 ≤
          (A.crossingIdx ⟨i + 1, by omega⟩).val -
            (A.crossingIdx ⟨i, by omega⟩).val - 1)
    (hgap_ends :
      A.moveOrder (A.crossingIdx ⟨0, by omega⟩) +
          A.moveOrder (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩) - 1 ≤
        (A.crossingIdx ⟨0, by omega⟩).val +
          (r - 1 - (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩).val)) :
    2 * k ≤ r :=
  (A.toMoveSchedule htwo hgap_between hgap_ends).toCountingCertificate.length_lower_bound





end CountedGeneralizedAllowableSequence



namespace ConcreteGeneralizedAllowableSequence



theorem stateAt_eq_of_proofs {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    {m : ℕ} (hm₁ hm₂ : m ≤ r) :
    A.stateAt m hm₁ = A.stateAt m hm₂ := by
  simp [stateAt]











theorem directFullMoveForcesCommonLevel_of_blocksHaveCommonLevel {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) (hk : 0 < k)
    {points : Finset Point2} (L : PointLabeling points k)
    (stepDir : Fin r → Direction)
    (hblocks : A.BlocksHaveCommonLevel L stepDir) :
    A.DirectFullMoveForcesCommonLevel L stepDir := by
  intro j hsource htarget
  have hj :
      (A.step j).toReversalStep.IsCrossing := by
    have hjA :=
      A.toCountedGeneralizedAllowableSequence.isCrossing_of_directFullMove
        hk hsource htarget
    simpa [CountedGeneralizedAllowableSequence.IsCrossing,
      CountedGeneralizedAllowableSequence.moveOrder, ReversalStep.IsCrossing] using hjA
  let b := (A.step j).toReversalStep.crossingBlockIndex hj
  rcases hblocks j b with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro a
  have hfull :=
    (A.step j).toReversalStep.crossingBlock_eq_full_of_order_eq_middle hj hk
      (A.toCountedGeneralizedAllowableSequence.moveOrder_eq_middle_of_directFullMove
        hsource htarget)
  have ha_mem :
      ((A.step j).toReversalStep.move.block b).Mem a := by
    dsimp [PositionInterval.Mem, b]
    constructor
    · rw [hfull.1]
      exact Nat.zero_le _
    · rw [hfull.2]
      exact Nat.le_sub_one_of_lt a.isLt
  have hstate : A.seq.π (stepFrom j) a = a := by
    rw [hsource]
    rfl
  simpa [hstate] using hc a ha_mem











theorem noDirectFullMove_of_directFullMoveForcesCommonLevel {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {points : Finset Point2}
    (L : PointLabeling points k) (stepDir : Fin r → Direction)
    (hncoll : NoncollinearSet points)
    (hlevel : A.DirectFullMoveForcesCommonLevel L stepDir) :
    A.NoDirectFullMove := by
  intro j
  by_cases hsource : A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k))
  · right
    intro htarget
    rcases hlevel j hsource htarget with ⟨c, hcommon⟩
    exact not_all_directionLevels_eq_of_noncollinearSet hncoll (stepDir j)
      ⟨c, by
        intro p hp
        rcases L.point_surjective_on p hp with ⟨a, ha⟩
        rw [← ha]
        exact hcommon a⟩
  · exact Or.inl hsource



theorem moveOrder_lt_middle_of_noDirectFullMove {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) (hk : 0 < k)
    (hnoFull : A.NoDirectFullMove) :
    ∀ j : Fin r, A.toCountedGeneralizedAllowableSequence.IsCrossing j →
      A.toCountedGeneralizedAllowableSequence.moveOrder j < k := by
  intro j hj
  by_contra hnot_lt
  have hle :
      A.toCountedGeneralizedAllowableSequence.moveOrder j ≤ k :=
    (A.step j).toReversalStep.order_le_middle
  have horder :
      A.toCountedGeneralizedAllowableSequence.moveOrder j = k := by
    omega
  have hsource :
      A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k)) :=
    (A.step j).toReversalStep.source_eq_refl_of_order_eq_middle hj hk horder
  have htarget :
      A.seq.π (stepTo j) = reverseFin (2 * k) :=
    (A.step j).toReversalStep.target_eq_reverseFin_of_order_eq_middle
      (A.reversesBlocks j) hj hk horder
  rcases hnoFull j with hbad | hbad
  · exact hbad hsource
  · exact hbad htarget









theorem decreasing_persists_over_noncrossing_steps {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (a n d : ℕ) (hend : a + n ≤ r)
    (hnc : ∀ l : Fin r, a ≤ l.val → l.val < a + n →
      ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l)
    (hdec :
      ReversalStep.DecreasingOnPositions (A.stateAt a (by omega))
        (PositionInterval.centralBarrierPositions k d)) :
    ReversalStep.DecreasingOnPositions (A.stateAt (a + n) hend)
      (PositionInterval.centralBarrierPositions k (d - n)) := by
  induction n generalizing a d with
  | zero =>
      simpa [stateAt]
  | succ n ih =>
      have hend_n : a + n ≤ r := by omega
      have hnc_n :
          ∀ l : Fin r, a ≤ l.val → l.val < a + n →
            ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l := by
        intro l hla hln
        exact hnc l hla (by omega)
      have hdec_n := ih a d hend_n hnc_n hdec
      have hnlt : a + n < r := by omega
      let j : Fin r := ⟨a + n, hnlt⟩
      have hnc_j : ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing j :=
        hnc j (by dsimp [j]; omega) (by dsimp [j]; omega)
      have hsource :
          A.stateAt (a + n) hend_n = A.seq.π (stepFrom j) := by
        apply congrArg A.seq.π
        apply Fin.ext
        simp [stepFrom, j]
      have htarget :
          A.stateAt (a + (n + 1)) hend = A.seq.π (stepTo j) := by
        apply congrArg A.seq.π
        apply Fin.ext
        simp [stepTo, j]
        omega
      rw [hsource] at hdec_n
      have hstep :=
        (A.step j).toReversalStep.decreasing_after_smaller_central_of_decreasing_before_nonCrossing
          (A.reversesBlocks j) hnc_j hdec_n
      rw [← htarget] at hstep
      have hrad : d - (n + 1) = d - n - 1 := by omega
      simpa [Nat.add_assoc, hrad] using hstep

theorem increasing_persists_back_over_noncrossing_steps {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (a n d : ℕ) (hend : a + n ≤ r)
    (hnc : ∀ l : Fin r, a ≤ l.val → l.val < a + n →
      ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l)
    (hinc :
      ReversalStep.IncreasingOnPositions (A.stateAt (a + n) hend)
        (PositionInterval.centralBarrierPositions k d)) :
    ReversalStep.IncreasingOnPositions (A.stateAt a (by omega))
      (PositionInterval.centralBarrierPositions k (d - n)) := by
  induction n generalizing a d with
  | zero =>
      simpa [stateAt] using hinc
  | succ n ih =>
      have hend_n : a + n ≤ r := by omega
      have hnlt : a + n < r := by omega
      let j : Fin r := ⟨a + n, hnlt⟩
      have hnc_j : ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing j :=
        hnc j (by dsimp [j]; omega) (by dsimp [j]; omega)
      have htarget :
          A.stateAt (a + (n + 1)) hend = A.seq.π (stepTo j) := by
        apply congrArg A.seq.π
        apply Fin.ext
        simp [stepTo, j]
        omega
      rw [htarget] at hinc
      have hprev_step :=
        (A.step j).toReversalStep.increasing_before_smaller_central_of_increasing_after_nonCrossing
          (A.reversesBlocks j) hnc_j hinc
      have hsource :
          A.stateAt (a + n) hend_n = A.seq.π (stepFrom j) := by
        apply congrArg A.seq.π
        apply Fin.ext
        simp [stepFrom, j]
      rw [← hsource] at hprev_step
      have hnc_n :
          ∀ l : Fin r, a ≤ l.val → l.val < a + n →
            ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l := by
        intro l hla hln
        exact hnc l hla (by omega)
      have hstart := ih a (d - 1) hend_n hnc_n hprev_step
      have hrad : d - (n + 1) = d - 1 - n := by omega
      simpa [Nat.add_assoc, hrad] using hstart









theorem crossing_step_decreases_central_barrier {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j) :
    ReversalStep.DecreasingOnPositions (A.seq.π (stepTo j))
      (PositionInterval.centralBarrierPositions k
        (A.toCountedGeneralizedAllowableSequence.moveOrder j)) := by
  exact (A.step j).toReversalStep.decreasing_after_centralBarrierPositions
    (A.reversesBlocks j) hj

theorem crossing_step_needs_central_barrier_increasing {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {j : Fin r}
    (hj : A.toCountedGeneralizedAllowableSequence.IsCrossing j) :
    ReversalStep.IncreasingOnPositions (A.seq.π (stepFrom j))
      (PositionInterval.centralBarrierPositions k
        (A.toCountedGeneralizedAllowableSequence.moveOrder j)) := by
  exact (A.step j).toReversalStep.increasing_before_centralBarrierPositions hj

































theorem gap_between_consecutive_crossings {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {i j : Fin r}
    (hij : A.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing i j) :
    A.toCountedGeneralizedAllowableSequence.moveOrder i +
        A.toCountedGeneralizedAllowableSequence.moveOrder j - 1 ≤
      j.val - i.val - 1 := by
  classical
  by_contra hnot
  let di := A.toCountedGeneralizedAllowableSequence.moveOrder i
  let dj := A.toCountedGeneralizedAllowableSequence.moveOrder j
  let g := j.val - i.val - 1
  have hijlt : i.val < j.val := hij.2.2.1
  have hgap_lt : g < di + dj - 1 := by
    dsimp [g, di, dj]
    omega
  have hdi_pos : 0 < di := by
    dsimp [di]
    exact hij.1
  have hdj_pos : 0 < dj := by
    dsimp [dj]
    exact hij.2.1
  let n₁ := Nat.min g (di - 1)
  have hn₁_le_g : n₁ ≤ g := Nat.min_le_left _ _
  have hn₁_lt_di : n₁ < di := by
    dsimp [n₁]
    have hmin_le : Nat.min g (di - 1) ≤ di - 1 := Nat.min_le_right _ _
    omega
  have hg_sub_lt_dj : g - n₁ < dj := by
    dsimp [n₁]
    by_cases hg_le : g ≤ di - 1
    · have hn : Nat.min g (di - 1) = g := Nat.min_eq_left hg_le
      rw [hn]
      omega
    · have hdi_le_g : di ≤ g := by omega
      have hn : Nat.min g (di - 1) = di - 1 := Nat.min_eq_right (by omega)
      rw [hn]
      omega
  let D := Nat.min (di - n₁) (dj - (g - n₁))
  have hD_pos : 0 < D := by
    dsimp [D]
    have hleft : 0 < di - n₁ := by omega
    have hright : 0 < dj - (g - n₁) := by omega
    exact Nat.lt_min.mpr ⟨hleft, hright⟩
  have hD_le_left : D ≤ di - n₁ := Nat.min_le_left _ _
  have hD_le_right : D ≤ dj - (g - n₁) := Nat.min_le_right _ _
  let a := i.val + 1
  have ha_eq_to : A.stateAt a (by
      dsimp [a]
      exact Nat.succ_le_of_lt i.isLt) = A.seq.π (stepTo i) := by
    apply congrArg A.seq.π
    apply Fin.ext
    simp [a, stepTo]
  have hb_eq_from : A.stateAt j.val (le_of_lt j.isLt) = A.seq.π (stepFrom j) := by
    apply congrArg A.seq.π
    apply Fin.ext
    simp [stepFrom]
  have ha_add_g : a + g = j.val := by
    dsimp [a, g]
    omega
  have hend_dec : a + n₁ ≤ r := by
    have hjle : j.val ≤ r := le_of_lt j.isLt
    omega
  have hnc_dec :
      ∀ l : Fin r, a ≤ l.val → l.val < a + n₁ →
        ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l := by
    intro l hla hln
    exact hij.2.2.2 l (by dsimp [a] at hla; omega) (by
      have hng : n₁ ≤ g := hn₁_le_g
      dsimp [a, g] at hln hng
      omega)
  have hdec_start :
      ReversalStep.DecreasingOnPositions (A.stateAt a (by
        dsimp [a]
        exact Nat.succ_le_of_lt i.isLt))
        (PositionInterval.centralBarrierPositions k di) := by
    have hdec := A.crossing_step_decreases_central_barrier hij.1
    rw [ha_eq_to]
    simpa [di] using hdec
  have hdec_mid :=
    A.decreasing_persists_over_noncrossing_steps a n₁ di hend_dec hnc_dec hdec_start
  have hend_inc : a + n₁ + (g - n₁) ≤ r := by
    have hjle : j.val ≤ r := le_of_lt j.isLt
    omega
  have hnc_inc :
      ∀ l : Fin r, a + n₁ ≤ l.val → l.val < a + n₁ + (g - n₁) →
        ¬ A.toCountedGeneralizedAllowableSequence.IsCrossing l := by
    intro l hla hln
    exact hij.2.2.2 l (by dsimp [a] at hla; omega) (by
      dsimp [a, g] at hln
      omega)
  have hinc_end :
      ReversalStep.IncreasingOnPositions
        (A.stateAt (a + n₁ + (g - n₁)) hend_inc)
        (PositionInterval.centralBarrierPositions k dj) := by
    have hsum : a + n₁ + (g - n₁) = j.val := by
      omega
    have hinc := A.crossing_step_needs_central_barrier_increasing hij.2.1
    have hstate :
        A.stateAt (a + n₁ + (g - n₁)) hend_inc = A.seq.π (stepFrom j) := by
      have hstateAt :
          A.stateAt (a + n₁ + (g - n₁)) hend_inc =
            A.stateAt j.val (le_of_lt j.isLt) := by
        apply congrArg A.seq.π
        apply Fin.ext
        exact hsum
      exact hstateAt.trans hb_eq_from
    rw [hstate]
    simpa [dj] using hinc
  have hinc_mid :=
    A.increasing_persists_back_over_noncrossing_steps
      (a + n₁) (g - n₁) dj hend_inc hnc_inc hinc_end
  have hmid_same :
      A.stateAt (a + n₁) (by omega) = A.stateAt (a + n₁) hend_dec := by
    apply A.stateAt_eq_of_proofs
  rw [hmid_same] at hinc_mid
  have hdec_D :
      ReversalStep.DecreasingOnPositions (A.stateAt (a + n₁) hend_dec)
        (PositionInterval.centralBarrierPositions k D) :=
    hdec_mid.mono (PositionInterval.centralBarrierPositions_mono hD_le_left)
  have hinc_D :
      ReversalStep.IncreasingOnPositions (A.stateAt (a + n₁) hend_dec)
        (PositionInterval.centralBarrierPositions k D) :=
    hinc_mid.mono (PositionInterval.centralBarrierPositions_mono hD_le_right)
  have hD_le_k : D ≤ k := by
    have hdi_le : di ≤ k := by
      dsimp [di]
      exact (A.step i).toReversalStep.order_le_middle
    omega
  exact ReversalStep.not_increasing_and_decreasing_centralBarrierPositions
    hD_pos hD_le_k hinc_D hdec_D





theorem gap_between_crossingIdx {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (i : ℕ) (hi : i + 1 <
      A.toCountedGeneralizedAllowableSequence.crossingMoves.card) :
    A.toCountedGeneralizedAllowableSequence.moveOrder
          (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i, by omega⟩) +
        A.toCountedGeneralizedAllowableSequence.moveOrder
          (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i + 1, by omega⟩) - 1 ≤
      (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i + 1, by omega⟩).val -
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨i, by omega⟩).val - 1 := by
  have hij :=
    A.toCountedGeneralizedAllowableSequence.consecutive_crossingIdx_succ i hi
  exact A.gap_between_consecutive_crossings hij





theorem cyclicEndGap_of_witness {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    {hpos : 0 < A.toCountedGeneralizedAllowableSequence.crossingMoves.card}
    (W : A.CyclicEndGapWitness hpos) :
    A.CyclicEndGap hpos := by
  have hgap := W.cyclic.gap_between_consecutive_crossings W.consecutive
  dsimp [CyclicEndGap]
  rw [← W.last_order, ← W.next_order, ← W.cyclic_gap_eq]
  simpa [add_comm] using hgap

theorem length_lower_bound_from_end_gap {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) (hk : 0 < k)
    (hnoFull :
      ∀ j : Fin r, A.toCountedGeneralizedAllowableSequence.IsCrossing j →
        A.toCountedGeneralizedAllowableSequence.moveOrder j < k)
    (hgap_ends :
      A.toCountedGeneralizedAllowableSequence.moveOrder
          (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, by
            exact A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk⟩) +
          A.toCountedGeneralizedAllowableSequence.moveOrder
            (A.toCountedGeneralizedAllowableSequence.crossingIdx
              ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by
                have htwo :=
                  A.toCountedGeneralizedAllowableSequence.two_le_crossingMoves_card_of_no_full_crossing
                    hk hnoFull
                omega⟩) - 1 ≤
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, by
          exact A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk⟩).val +
          (r - 1 -
            (A.toCountedGeneralizedAllowableSequence.crossingIdx
              ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by
                have htwo :=
                  A.toCountedGeneralizedAllowableSequence.two_le_crossingMoves_card_of_no_full_crossing
                    hk hnoFull
                omega⟩).val)) :
    2 * k ≤ r := by
  have htwo :=
    A.toCountedGeneralizedAllowableSequence.two_le_crossingMoves_card_of_no_full_crossing
      hk hnoFull
  exact A.toCountedGeneralizedAllowableSequence.length_lower_bound_from_gaps
    htwo
    (fun i hi => A.gap_between_crossingIdx i hi)
    (by
      simpa using hgap_ends)

theorem length_lower_bound_from_cyclic_end_gap {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) (hk : 0 < k)
    (hnoFull :
      ∀ j : Fin r, A.toCountedGeneralizedAllowableSequence.IsCrossing j →
        A.toCountedGeneralizedAllowableSequence.moveOrder j < k)
    (hend :
      A.CyclicEndGap
        (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)) :
    2 * k ≤ r := by
  exact A.length_lower_bound_from_end_gap hk hnoFull (by
    simpa [CyclicEndGap] using hend)





end ConcreteGeneralizedAllowableSequence



theorem even_direction_bound_of_concrete_end_gap_sequence (points : Finset Point2)
    {k : ℕ} (hk : 0 < k) (hcard : points.card = 2 * k)
    (A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy points).card)
    (hnoFull :
      ∀ j : Fin (directionsDeterminedBy points).card,
        A.toCountedGeneralizedAllowableSequence.IsCrossing j →
          A.toCountedGeneralizedAllowableSequence.moveOrder j < k)
    (hend :
      A.CyclicEndGap
        (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)) :
    points.card ≤ (directionsDeterminedBy points).card := by
  rw [hcard]
  exact A.length_lower_bound_from_cyclic_end_gap hk hnoFull hend

































namespace UngarLevelSweepCertificate



theorem noDirectFullMove {S : Finset Point2} {k : ℕ} {hk : 0 < k}
    (C : UngarLevelSweepCertificate S k hk) (hncoll : NoncollinearSet S) :
    C.sequence.NoDirectFullMove :=
  C.sequence.noDirectFullMove_of_directFullMoveForcesCommonLevel
    C.labeling C.stepDir hncoll
    (C.sequence.directFullMoveForcesCommonLevel_of_blocksHaveCommonLevel
      hk C.labeling C.stepDir C.blocks_level)

theorem noFullCrossing {S : Finset Point2} {k : ℕ} {hk : 0 < k}
    (C : UngarLevelSweepCertificate S k hk) (hncoll : NoncollinearSet S) :
    ∀ j : Fin (directionsDeterminedBy S).card,
      C.sequence.toCountedGeneralizedAllowableSequence.IsCrossing j →
        C.sequence.toCountedGeneralizedAllowableSequence.moveOrder j < k :=
  C.sequence.moveOrder_lt_middle_of_noDirectFullMove hk (C.noDirectFullMove hncoll)



theorem even_direction_bound {S : Finset Point2} {k : ℕ} {hk : 0 < k}
    (C : UngarLevelSweepCertificate S k hk)
    (hcard : S.card = 2 * k) (hncoll : NoncollinearSet S) :
    S.card ≤ (directionsDeterminedBy S).card :=
  even_direction_bound_of_concrete_end_gap_sequence S hk hcard C.sequence
    (C.noFullCrossing hncoll) C.cyclic_end_gap

end UngarLevelSweepCertificate

namespace UngarLevelSweepCore



theorem noDirectFullMove {S : Finset Point2} {k : ℕ}
    (C : UngarLevelSweepCore S k) (hk : 0 < k) (hncoll : NoncollinearSet S) :
    C.sequence.NoDirectFullMove :=
  C.sequence.noDirectFullMove_of_directFullMoveForcesCommonLevel
    C.labeling C.stepDir hncoll
    (C.sequence.directFullMoveForcesCommonLevel_of_blocksHaveCommonLevel
      hk C.labeling C.stepDir C.blocks_level)

theorem noFullCrossing {S : Finset Point2} {k : ℕ}
    (C : UngarLevelSweepCore S k) (hk : 0 < k) (hncoll : NoncollinearSet S) :
    ∀ j : Fin (directionsDeterminedBy S).card,
      C.sequence.toCountedGeneralizedAllowableSequence.IsCrossing j →
        C.sequence.toCountedGeneralizedAllowableSequence.moveOrder j < k :=
  C.sequence.moveOrder_lt_middle_of_noDirectFullMove hk
    (C.noDirectFullMove hk hncoll)



end UngarLevelSweepCore









































theorem ungar_directions_floor_lower_bound_from_level_sweep_certificate
    (points : Finset Point2)
    (hn : 3 ≤ points.card) (hncoll : NoncollinearSet points)
    (hcert : EvenUngarLevelSweepCertificatePremise) :
    2 * (points.card / 2) ≤ (directionsDeterminedBy points).card :=
  directions_floor_lower_bound_of_even_direction_bound_all points hn hncoll
    (fun S hEven hS => by
      rcases hEven with ⟨k, hk_even⟩
      have hcardS : S.card = 2 * k := by omega
      have hkpos : 0 < k := by
        rcases hS with ⟨p, hp, _q, _hq, _r, _hr, _hnon⟩
        have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨p, hp⟩
        omega
      rcases hcert S k hkpos hcardS hS with ⟨C⟩
      exact C.even_direction_bound hcardS hS)







theorem chapter11_from_level_sweep_certificate (points : Finset Point2)
    (hn : 3 ≤ points.card)
    (hncoll : NoncollinearSet points)
    (hcert : EvenUngarLevelSweepCertificatePremise) :
    2 * (points.card / 2) ≤ (directionsDeterminedBy points).card :=
  ungar_directions_floor_lower_bound_from_level_sweep_certificate points hn hncoll hcert

/-! ## Sweep certificate construction

The remaining geometric core: construct `UngarLevelSweepCertificate` from the
rotating projection sweep of every even non-collinear point set.
-/

/-! ### BlockMove from monotone level function -/



























/-! ### ReversalStep from sweep event -/





/-! ### Sorted direction angle infrastructure -/



























/-! ### Starting angle selection -/











/-! ### Inter-event angles -/







/-! ### No-tie conditions between inter-event angles -/









/-! ### Sweep labeling and GAS -/











/-! ### Inter-event angle ordering -/





/-! ### Span and bounds for inter-event angles -/







/-! ### Generalized non-tie and only-event condition -/









/-! ### No-tie from θ₀ to inter-event angle -/



/-! ### Injectivity at inter-event angles -/



/-! ### ConcreteGAS assembly -/



/-! ### Monotonicity and nontrivial blocks at events -/





/-! ### ConcreteGAS assembly -/





/-! ### Step directions -/









/-! ### BlocksHaveCommonLevel -/













theorem evenUngarLevelSweepCertificatePremise_of_sweep_cyclicEndGap
    (hend : EvenSweepCyclicEndGapPremise) :
    EvenUngarLevelSweepCertificatePremise := by
  intro S k hk hcard hncoll
  let C := ungarLevelSweepCore (points := S) (k := k) hcard hncoll
  exact ⟨C.toCertificate hk (hend S k hk hcard hncoll)⟩



/-!
### Certificate assembly status

The rotating-level sweep constructs `ungarLevelSweepCore`; the cyclic end gap is
then supplied by the shifted-sweep witness assembled below:

- `labeling` = `sweepLabeling`
- `sequence` = `sweepConcreteGAS`
- `stepDir` = `sweepStepDir`
- `blocks_level` = `sweepConcreteGAS_blocksHaveCommonLevel`
- `stepDir_injective` = `sweepStepDir_injective`
- `cyclic_end_gap` = `sweepConcreteGAS_cyclicEndGap_of_noFull`

The theorem `evenSweepCyclicEndGapPremise` discharges the last sweep premise,
and `chapter11` is now the unconditional projective-direction lower bound.
-/

/-! ### Parameterized sweep for CyclicEndGap -/




























































































































































































theorem sweepConcreteGAS_cyclicEndGap_of_noFull
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hk : 0 < k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (hnoFull :
      ∀ j : Fin (directionsDeterminedBy points).card,
        (sweepConcreteGAS hcard hne hr hncoll).IsCrossing j →
          (sweepConcreteGAS hcard hne hr hncoll).moveOrder j < k) :
    (sweepConcreteGAS hcard hne hr hncoll).CyclicEndGap
      ((sweepConcreteGAS hcard hne hr hncoll).toCountedGeneralizedAllowableSequence
        |>.crossingMoves_card_pos hk) := by
  exact (sweepConcreteGAS hcard hne hr hncoll).cyclicEndGap_of_witness
    (sweepConcreteGAS_cyclicEndGapWitness_of_noFull
      hcard hk hne hr hncoll hnoFull)

theorem evenSweepCyclicEndGapPremise :
    EvenSweepCyclicEndGapPremise := by
  intro S k hk hcard hncoll
  let hne := directionsDeterminedBy_nonempty_of_noncollinear hncoll
  let hr := directionsDeterminedBy_card_ge_two_of_noncollinear hncoll
  let C := ungarLevelSweepCore (points := S) (k := k) hcard hncoll
  have hnoFull :
      ∀ j : Fin (directionsDeterminedBy S).card,
        (sweepConcreteGAS hcard hne hr hncoll).IsCrossing j →
          (sweepConcreteGAS hcard hne hr hncoll).moveOrder j < k := by
    simpa [C, ungarLevelSweepCore, hne, hr] using C.noFullCrossing hk hncoll
  simpa [C, ungarLevelSweepCore, hne, hr] using
    sweepConcreteGAS_cyclicEndGap_of_noFull hcard hk hne hr hncoll hnoFull

theorem evenUngarLevelSweepCertificatePremise :
    EvenUngarLevelSweepCertificatePremise :=
  evenUngarLevelSweepCertificatePremise_of_sweep_cyclicEndGap
    evenSweepCyclicEndGapPremise





-- Starting angle θ₀ is between sortedAngleAt(s-1) and sortedAngleAt(s)
-- (or equivalently, in the gap before event s).
--
-- This records why the older non-cyclic start hypothesis `θ₀ < d.angle` for
-- every direction cannot support a shifted cyclic start: combined with the
-- gap-before-s hypothesis, it forces `s = 0`.


/-!
### Shifted cyclic sweep

The proof of `cyclic_end_gap` starts a second sweep in the gap between the last
and first crossing directions, turning the cyclic end gap into an interior
consecutive-crossing gap.  The local modulo-`π` start infrastructure is wired
into a concrete shifted sweep:

- `orientedLevel_injective_of_all_angles_mod_pi`
- `sweepLabelingAt_inj_mod_pi`
- `sweepGAS_at_mod_pi`
- the `_mod_pi` start/end bounds for `shiftedSortedAngleAt` and
  `interEventAngleAt`
- the no-wrap/wrap angle-identification lemmas, culminating in the
  rotation formulas `shiftedSortedAngleAt_rotate` and
  `interEventAngleAt_rotate`
- `interEventAngleAt_no_other_shiftedEventAngle`
- `only_event_between_interEventAnglesAt_mod_pi`
- `inj_at_interEventAngleAt_mod_pi`
- `mono_at_eventAt_mod_pi`
- `sweepConcreteGAS_at_mod_pi`
- `sweepConcreteGAS_atIndex_mod_pi`
- `sweepLabelingAt_interEventAngle_point_eq`
- `sweepSort_labelingAt_interEventAngle_no_wrap`
- `sweepSort_labelingAt_interEventAngle_wrap`
- `sweepSort_labelingAt_interEventAngle_wrap_rev`
- `sweepConcreteGAS_atIndex_mod_pi_seq_no_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_seq_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_seq_wrap_rev`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap_to_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap_last`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_index_before`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_index_at_or_after_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_index_at_or_after_shifted_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_shifted_nonfinal`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_no_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_no_wrap_to_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_wrap_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_wrap_last`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_before`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_at_or_after_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_at_or_after_shifted_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_shifted_nonfinal`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_no_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_no_wrap_to_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_wrap_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_wrap_last`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_before`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_at_or_after_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_at_or_after_shifted_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_shifted_nonfinal`

The transfer is split into the interior no-wrap case, the boundary where the
target state first wraps past `π`, and the nonfinal/final wrapped cases.  These
cases feed `sweepConcreteGAS_cyclicEndGapWitness_of_noFull`, where the ordinary
last crossing becomes the shifted crossing at index `0`, the ordinary first
crossing becomes the next shifted crossing, and the `crossingIdx` extremality
lemmas rule out shifted crossings between them.
-/

end ProofsInTheBook.Chapter11

open ProofsInTheBook.Chapter11

theorem solution (points : Finset Point2)
    (hn : 3 ≤ points.card)
    (hncoll : NoncollinearSet points) :
    2 * (points.card / 2) ≤ (directionsDeterminedBy points).card :=
  chapter11_from_level_sweep_certificate points hn hncoll
    evenUngarLevelSweepCertificatePremise
