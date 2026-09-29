-- Prove2me | solution 1 for mme_CW_q6_exact_address_balanced_xy_bipartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:42:26.705764+00:00
-- url     : https://prove2.me/submissions/b464c882-c63b-4617-9597-478759e6baaa

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_exact_address_joint_xy_counts

open MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Split the positions of an exact address into two equal source words.
The first word is balanced in target mode zero and the second word is
balanced in target mode one.  This is the position permutation required by
the paired 121/211 source. -/
theorem solution
    {n L G : ℕ} (hLG : L + G = 2 * n)
    (address : CWQ6ExactCoupledAddress (2 * n) L G) :
    ∃ e : (Fin (2 * n) ⊕ Fin (2 * n)) ≃ Fin (2 * (2 * n)),
      (∀ r : Fin 3,
        Fintype.card {j : Fin (2 * n) //
          address.1 0 (e (Sum.inl j)) = r} =
            if r = 0 then n else if r = 1 then n else 0) ∧
      (∀ r : Fin 3,
        Fintype.card {j : Fin (2 * n) //
          address.1 1 (e (Sum.inr j)) = r} =
            if r = 0 then n else if r = 1 then n else 0) := by
  classical
  let P := Fin (2 * (2 * n))
  let C00 : Finset P := Finset.univ.filter
    (fun j => address.1 0 j = 0 ∧ address.1 1 j = 0)
  let C11 : Finset P := Finset.univ.filter
    (fun j => address.1 0 j = 1 ∧ address.1 1 j = 1)
  let C01 : Finset P := Finset.univ.filter
    (fun j => address.1 0 j = 0 ∧ address.1 1 j = 1)
  let C10 : Finset P := Finset.univ.filter
    (fun j => address.1 0 j = 1 ∧ address.1 1 j = 0)
  have hcounts :=
    mme_CW_q6_exact_address_joint_xy_counts hLG address
  have hC00 : C00.card = L := by simpa [C00, P] using hcounts.1
  have hC11 : C11.card = L := by simpa [C11, P] using hcounts.2.1
  have hC01 : C01.card = G := by simpa [C01, P] using hcounts.2.2.1
  have hC10 : C10.card = G := by simpa [C10, P] using hcounts.2.2.2
  let k := min n L
  have hkL : k ≤ L := by exact Nat.min_le_right _ _
  have hkn : k ≤ n := by exact Nat.min_le_left _ _
  have hrest : n - k ≤ G := by
    by_cases hnL : n ≤ L
    · have hk : k = n := Nat.min_eq_left hnL
      simp [hk]
    · have hLn : L ≤ n := by omega
      have hk : k = L := Nat.min_eq_right hLn
      omega
  obtain ⟨S00, hS00sub, hS00card⟩ :=
    C00.exists_subset_card_eq (hC00 ▸ hkL)
  obtain ⟨S11, hS11sub, hS11card⟩ :=
    C11.exists_subset_card_eq (hC11 ▸ hkL)
  obtain ⟨S01, hS01sub, hS01card⟩ :=
    C01.exists_subset_card_eq (hC01 ▸ hrest)
  obtain ⟨S10, hS10sub, hS10card⟩ :=
    C10.exists_subset_card_eq (hC10 ▸ hrest)
  have hS00cell : ∀ j ∈ S00,
      address.1 0 j = 0 ∧ address.1 1 j = 0 := by
    intro j hj
    exact (Finset.mem_filter.mp (hS00sub hj)).2
  have hS11cell : ∀ j ∈ S11,
      address.1 0 j = 1 ∧ address.1 1 j = 1 := by
    intro j hj
    exact (Finset.mem_filter.mp (hS11sub hj)).2
  have hS01cell : ∀ j ∈ S01,
      address.1 0 j = 0 ∧ address.1 1 j = 1 := by
    intro j hj
    exact (Finset.mem_filter.mp (hS01sub hj)).2
  have hS10cell : ∀ j ∈ S10,
      address.1 0 j = 1 ∧ address.1 1 j = 0 := by
    intro j hj
    exact (Finset.mem_filter.mp (hS10sub hj)).2
  let S : Finset P := S00 ∪ S11 ∪ S01 ∪ S10
  have hSX0 : S.filter (fun j => address.1 0 j = 0) = S00 ∪ S01 := by
    ext j
    constructor
    · intro hj
      have hjmem := (Finset.mem_filter.mp hj).1
      have hjx := (Finset.mem_filter.mp hj).2
      simp only [S, Finset.mem_union] at hjmem
      rcases hjmem with ((hj00 | hj11) | hj01) | hj10
      · exact Finset.mem_union_left _ hj00
      · have := (hS11cell j hj11).1
        simp_all
      · exact Finset.mem_union_right _ hj01
      · have := (hS10cell j hj10).1
        simp_all
    · intro hj
      rcases Finset.mem_union.mp hj with hj00 | hj01
      · exact Finset.mem_filter.mpr ⟨by simp [S, hj00], (hS00cell j hj00).1⟩
      · exact Finset.mem_filter.mpr ⟨by simp [S, hj01], (hS01cell j hj01).1⟩
  have hSX1 : S.filter (fun j => address.1 0 j = 1) = S11 ∪ S10 := by
    ext j
    constructor
    · intro hj
      have hjmem := (Finset.mem_filter.mp hj).1
      have hjx := (Finset.mem_filter.mp hj).2
      simp only [S, Finset.mem_union] at hjmem
      rcases hjmem with ((hj00 | hj11) | hj01) | hj10
      · have := (hS00cell j hj00).1
        simp_all
      · exact Finset.mem_union_left _ hj11
      · have := (hS01cell j hj01).1
        simp_all
      · exact Finset.mem_union_right _ hj10
    · intro hj
      rcases Finset.mem_union.mp hj with hj11 | hj10
      · exact Finset.mem_filter.mpr ⟨by simp [S, hj11], (hS11cell j hj11).1⟩
      · exact Finset.mem_filter.mpr ⟨by simp [S, hj10], (hS10cell j hj10).1⟩
  have hSY0 : S.filter (fun j => address.1 1 j = 0) = S00 ∪ S10 := by
    ext j
    constructor
    · intro hj
      have hjmem := (Finset.mem_filter.mp hj).1
      have hjy := (Finset.mem_filter.mp hj).2
      simp only [S, Finset.mem_union] at hjmem
      rcases hjmem with ((hj00 | hj11) | hj01) | hj10
      · exact Finset.mem_union_left _ hj00
      · have := (hS11cell j hj11).2
        simp_all
      · have := (hS01cell j hj01).2
        simp_all
      · exact Finset.mem_union_right _ hj10
    · intro hj
      rcases Finset.mem_union.mp hj with hj00 | hj10
      · exact Finset.mem_filter.mpr ⟨by simp [S, hj00], (hS00cell j hj00).2⟩
      · exact Finset.mem_filter.mpr ⟨by simp [S, hj10], (hS10cell j hj10).2⟩
  have hSY1 : S.filter (fun j => address.1 1 j = 1) = S11 ∪ S01 := by
    ext j
    constructor
    · intro hj
      have hjmem := (Finset.mem_filter.mp hj).1
      have hjy := (Finset.mem_filter.mp hj).2
      simp only [S, Finset.mem_union] at hjmem
      rcases hjmem with ((hj00 | hj11) | hj01) | hj10
      · have := (hS00cell j hj00).2
        simp_all
      · exact Finset.mem_union_left _ hj11
      · exact Finset.mem_union_right _ hj01
      · have := (hS10cell j hj10).2
        simp_all
    · intro hj
      rcases Finset.mem_union.mp hj with hj11 | hj01
      · exact Finset.mem_filter.mpr ⟨by simp [S, hj11], (hS11cell j hj11).2⟩
      · exact Finset.mem_filter.mpr ⟨by simp [S, hj01], (hS01cell j hj01).2⟩
  have hdisj00_01 : Disjoint S00 S01 := by
    rw [Finset.disjoint_left]
    intro j hj00 hj01
    have h0 := (hS00cell j hj00).2
    have h1 := (hS01cell j hj01).2
    simp_all
  have hdisj11_10 : Disjoint S11 S10 := by
    rw [Finset.disjoint_left]
    intro j hj11 hj10
    have h1 := (hS11cell j hj11).2
    have h0 := (hS10cell j hj10).2
    simp_all
  have hdisj00_10 : Disjoint S00 S10 := by
    rw [Finset.disjoint_left]
    intro j hj00 hj10
    have h0 := (hS00cell j hj00).1
    have h1 := (hS10cell j hj10).1
    simp_all
  have hdisj11_01 : Disjoint S11 S01 := by
    rw [Finset.disjoint_left]
    intro j hj11 hj01
    have h1 := (hS11cell j hj11).1
    have h0 := (hS01cell j hj01).1
    simp_all
  have hSX0card : (S.filter (fun j => address.1 0 j = 0)).card = n := by
    rw [hSX0, Finset.card_union_of_disjoint hdisj00_01,
      hS00card, hS01card]
    omega
  have hSX1card : (S.filter (fun j => address.1 0 j = 1)).card = n := by
    rw [hSX1, Finset.card_union_of_disjoint hdisj11_10,
      hS11card, hS10card]
    omega
  have hSY0card : (S.filter (fun j => address.1 1 j = 0)).card = n := by
    rw [hSY0, Finset.card_union_of_disjoint hdisj00_10,
      hS00card, hS10card]
    omega
  have hSY1card : (S.filter (fun j => address.1 1 j = 1)).card = n := by
    rw [hSY1, Finset.card_union_of_disjoint hdisj11_01,
      hS11card, hS01card]
    omega
  have hSpartition :
      (S.filter (fun j => address.1 0 j = 0)) ∪
        (S.filter (fun j => address.1 0 j = 1)) = S := by
    rw [hSX0, hSX1]
    ext j
    simp only [S, Finset.mem_union]
    tauto
  have hSXdisj : Disjoint
      (S.filter (fun j => address.1 0 j = 0))
      (S.filter (fun j => address.1 0 j = 1)) := by
    rw [Finset.disjoint_left]
    intro j hj0 hj1
    have h0 := (Finset.mem_filter.mp hj0).2
    have h1 := (Finset.mem_filter.mp hj1).2
    simp_all
  have hScard : S.card = 2 * n := by
    rw [← hSpartition, Finset.card_union_of_disjoint hSXdisj,
      hSX0card, hSX1card]
    omega
  let T : Finset P := Finset.univ \ S
  have hTcard : T.card = 2 * n := by
    have hdiff : ((Finset.univ : Finset P) \ S).card =
        (Finset.univ : Finset P).card - S.card :=
      Finset.card_sdiff_of_subset (Finset.subset_univ S)
    change ((Finset.univ : Finset P) \ S).card = 2 * n
    rw [hdiff]
    simp only [Finset.card_univ, Fintype.card_fin, P, hScard]
    omega
  have hX2total :
      ((Finset.univ : Finset P).filter
        (fun j => address.1 0 j = 2)).card = 0 := by
    have h := address.2.2 (0 : Fin 3) (2 : Fin 3)
    change ((Finset.univ : Finset (Fin (2 * (2 * n)))).filter
      (fun j => address.1 0 j = 2)).card = 0 at h
    simpa [P] using h
  have hY0total :
      ((Finset.univ : Finset P).filter
        (fun j => address.1 1 j = 0)).card = 2 * n := by
    have h := address.2.2 (1 : Fin 3) (0 : Fin 3)
    change ((Finset.univ : Finset (Fin (2 * (2 * n)))).filter
      (fun j => address.1 1 j = 0)).card = 2 * n at h
    simpa [P] using h
  have hY1total :
      ((Finset.univ : Finset P).filter
        (fun j => address.1 1 j = 1)).card = 2 * n := by
    have h := address.2.2 (1 : Fin 3) (1 : Fin 3)
    change ((Finset.univ : Finset (Fin (2 * (2 * n)))).filter
      (fun j => address.1 1 j = 1)).card = 2 * n at h
    simpa [P] using h
  have hY2total :
      ((Finset.univ : Finset P).filter
        (fun j => address.1 1 j = 2)).card = 0 := by
    have h := address.2.2 (1 : Fin 3) (2 : Fin 3)
    change ((Finset.univ : Finset (Fin (2 * (2 * n)))).filter
      (fun j => address.1 1 j = 2)).card = 0 at h
    simpa [P] using h
  have hSX2card : (S.filter (fun j => address.1 0 j = 2)).card = 0 := by
    have hsub : S.filter (fun j => address.1 0 j = 2) ⊆
        (Finset.univ : Finset P).filter
          (fun j => address.1 0 j = 2) := by
      intro j hj
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    have hle := Finset.card_le_card hsub
    omega
  have hTY0set : T.filter (fun j => address.1 1 j = 0) =
      ((Finset.univ : Finset P).filter
        (fun j => address.1 1 j = 0)) \
      (S.filter (fun j => address.1 1 j = 0)) := by
    ext j
    simp only [T, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    tauto
  have hTY1set : T.filter (fun j => address.1 1 j = 1) =
      ((Finset.univ : Finset P).filter
        (fun j => address.1 1 j = 1)) \
      (S.filter (fun j => address.1 1 j = 1)) := by
    ext j
    simp only [T, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    tauto
  have hTY0card : (T.filter (fun j => address.1 1 j = 0)).card = n := by
    have hsub : S.filter (fun j => address.1 1 j = 0) ⊆
        (Finset.univ : Finset P).filter
          (fun j => address.1 1 j = 0) := by
      intro j hj
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    have hdiff := Finset.card_sdiff_add_card_eq_card hsub
    rw [hTY0set]
    omega
  have hTY1card : (T.filter (fun j => address.1 1 j = 1)).card = n := by
    have hsub : S.filter (fun j => address.1 1 j = 1) ⊆
        (Finset.univ : Finset P).filter
          (fun j => address.1 1 j = 1) := by
      intro j hj
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    have hdiff := Finset.card_sdiff_add_card_eq_card hsub
    rw [hTY1set]
    omega
  have hTY2card : (T.filter (fun j => address.1 1 j = 2)).card = 0 := by
    have hsub : T.filter (fun j => address.1 1 j = 2) ⊆
        (Finset.univ : Finset P).filter
          (fun j => address.1 1 j = 2) := by
      intro j hj
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
    have hle := Finset.card_le_card hsub
    omega
  let eS : Fin (2 * n) ≃ ↥S :=
    (Fintype.equivFinOfCardEq (by simpa using hScard)).symm
  let eT : Fin (2 * n) ≃ ↥T :=
    (Fintype.equivFinOfCardEq (by simpa using hTcard)).symm
  let f : (Fin (2 * n) ⊕ Fin (2 * n)) → P :=
    Sum.elim (fun j => (eS j).1) (fun j => (eT j).1)
  have hfinj : Function.Injective f := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · have he : eS x = eS y := by
        apply Subtype.ext
        exact hxy
      have hxy' : x = y := eS.injective he
      exact hxy' ▸ rfl
    · exfalso
      have hxS := (eS x).2
      have hyT := (eT y).2
      have hval : (eS x).1 = (eT y).1 := hxy
      apply (Finset.mem_sdiff.mp hyT).2
      rw [← hval]
      exact hxS
    · exfalso
      have hxT := (eT x).2
      have hyS := (eS y).2
      have hval : (eT x).1 = (eS y).1 := hxy
      apply (Finset.mem_sdiff.mp hxT).2
      rw [hval]
      exact hyS
    · have he : eT x = eT y := by
        apply Subtype.ext
        exact hxy
      have hxy' : x = y := eT.injective he
      exact hxy' ▸ rfl
  have hfsurj : Function.Surjective f := by
    intro p
    by_cases hp : p ∈ S
    · let sp : ↥S := ⟨p, hp⟩
      refine ⟨Sum.inl (eS.symm sp), ?_⟩
      simp [f, sp]
    · have hpT : p ∈ T := by simp [T, hp]
      let tp : ↥T := ⟨p, hpT⟩
      refine ⟨Sum.inr (eT.symm tp), ?_⟩
      simp [f, tp]
  let e : (Fin (2 * n) ⊕ Fin (2 * n)) ≃ P :=
    Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hleft (r : Fin 3) :
      Fintype.card {j : Fin (2 * n) //
        address.1 0 (e (Sum.inl j)) = r} =
        (S.filter (fun p => address.1 0 p = r)).card := by
    calc
      Fintype.card {j : Fin (2 * n) //
          address.1 0 (e (Sum.inl j)) = r} =
        Fintype.card {p : ↥S // address.1 0 p.1 = r} := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquiv eS (by
            intro j
            simp [e, f])
      _ = (S.filter (fun p => address.1 0 p = r)).card := by
        calc
          Fintype.card {p : ↥S // address.1 0 p.1 = r} =
              Fintype.card ↥(S.filter
                (fun p => address.1 0 p = r)) := by
            apply Fintype.card_congr
            exact
              { toFun := fun p => ⟨p.1.1,
                  Finset.mem_filter.mpr ⟨p.1.2, p.2⟩⟩
                invFun := fun p => ⟨⟨p.1,
                  (Finset.mem_filter.mp p.2).1⟩,
                  (Finset.mem_filter.mp p.2).2⟩
                left_inv := by intro p; rfl
                right_inv := by intro p; rfl }
          _ = (S.filter (fun p => address.1 0 p = r)).card :=
            Fintype.card_coe _
  have hright (r : Fin 3) :
      Fintype.card {j : Fin (2 * n) //
        address.1 1 (e (Sum.inr j)) = r} =
        (T.filter (fun p => address.1 1 p = r)).card := by
    calc
      Fintype.card {j : Fin (2 * n) //
          address.1 1 (e (Sum.inr j)) = r} =
        Fintype.card {p : ↥T // address.1 1 p.1 = r} := by
          apply Fintype.card_congr
          exact Equiv.subtypeEquiv eT (by
            intro j
            simp [e, f])
      _ = (T.filter (fun p => address.1 1 p = r)).card := by
        calc
          Fintype.card {p : ↥T // address.1 1 p.1 = r} =
              Fintype.card ↥(T.filter
                (fun p => address.1 1 p = r)) := by
            apply Fintype.card_congr
            exact
              { toFun := fun p => ⟨p.1.1,
                  Finset.mem_filter.mpr ⟨p.1.2, p.2⟩⟩
                invFun := fun p => ⟨⟨p.1,
                  (Finset.mem_filter.mp p.2).1⟩,
                  (Finset.mem_filter.mp p.2).2⟩
                left_inv := by intro p; rfl
                right_inv := by intro p; rfl }
          _ = (T.filter (fun p => address.1 1 p = r)).card :=
            Fintype.card_coe _
  refine ⟨e, ?_, ?_⟩
  · intro r
    rw [hleft]
    fin_cases r
    · change (S.filter (fun p => address.1 0 p = (0 : Fin 3))).card = n
      exact hSX0card
    · change (S.filter (fun p => address.1 0 p = (1 : Fin 3))).card = n
      exact hSX1card
    · change (S.filter (fun p => address.1 0 p = (2 : Fin 3))).card = 0
      exact hSX2card
  · intro r
    rw [hright]
    fin_cases r
    · change (T.filter (fun p => address.1 1 p = (0 : Fin 3))).card = n
      exact hTY0card
    · change (T.filter (fun p => address.1 1 p = (1 : Fin 3))).card = n
      exact hTY1card
    · change (T.filter (fun p => address.1 1 p = (2 : Fin 3))).card = 0
      exact hTY2card
