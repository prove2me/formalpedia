-- Prove2me | solution 1 for AGT.arrow_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T19:21:29.217154+00:00
-- url     : https://prove2.me/submissions/1b8b9359-6b6d-44ea-8cd5-b8df544c716f

import Definitions.Def_agt_social
import Mathlib.Tactic

/-!
# Arrow's impossibility theorem

Theorem 9.3 of *Algorithmic Game Theory*.  The proof is the pivotal-voter
argument: Pareto efficiency, the extremal lemma, a pivotal voter for a fixed
alternative `b`, dictatorship over all pairs avoiding `b`, and finally the
transfer to pairs involving `b`.

Every concrete ballot used in the argument is built from a rank function
`ρ : A → ℕ` via `ordOf ρ`, where `x` is preferred to `y` iff `ρ y < ρ x`.
-/

namespace AGT

variable {A : Type*}

/-- The strict total order induced by a rank function. -/
private def ordOf (ρ : A → ℕ) : A → A → Prop := fun x y => ρ y < ρ x

private theorem isSTO_ordOf {ρ : A → ℕ} (hρ : Function.Injective ρ) :
    IsStrictTotalOrder A (ordOf ρ) := by
  haveI : IsIrrefl A (ordOf ρ) := ⟨fun x h => absurd h (Nat.lt_irrefl (ρ x))⟩
  haveI : IsTrans A (ordOf ρ) := ⟨fun _ _ _ h₁ h₂ => Nat.lt_trans h₂ h₁⟩
  haveI : IsTrichotomous A (ordOf ρ) :=
    ⟨fun _ _ h₁ h₂ => hρ (Nat.le_antisymm (Nat.not_lt.1 h₁) (Nat.not_lt.1 h₂))⟩
  exact {}

private theorem ordOf_asymm {ρ : A → ℕ} {x y : A} (h : ordOf ρ x y) : ¬ ordOf ρ y x :=
  fun h2 => Nat.lt_irrefl _ (Nat.lt_trans h h2)

section Ballots

variable [Fintype A] [DecidableEq A]

/-- A fixed injective ranking of the alternatives. -/
private noncomputable def rk (x : A) : ℕ := (Fintype.equivFin A x : ℕ)

omit [DecidableEq A] in
private theorem rk_inj : Function.Injective (rk (A := A)) := by
  intro x y h
  have : Fintype.equivFin A x = Fintype.equivFin A y := Fin.ext h
  simpa using congrArg (Fintype.equivFin A).symm this

omit [DecidableEq A] in
private theorem rk_lt (x : A) : rk x < Fintype.card A := (Fintype.equivFin A x).isLt

/-- The ballot ranking `x₁` first, `x₂` second, `x₃` third, everything else below. -/
private noncomputable def topThree (x₁ x₂ x₃ : A) : A → A → Prop :=
  ordOf (fun z =>
    if z = x₁ then Fintype.card A + 3
    else if z = x₂ then Fintype.card A + 2
    else if z = x₃ then Fintype.card A + 1
    else rk z)

variable {x₁ x₂ x₃ : A}

private theorem isSTO_topThree : IsStrictTotalOrder A (topThree x₁ x₂ x₃) := by
  refine isSTO_ordOf ?_
  intro u v huv
  have hu := rk_lt u
  have hv := rk_lt v
  simp only at huv
  split_ifs at huv <;> subst_vars <;>
    first
      | rfl
      | (exfalso; omega)
      | exact rk_inj huv

private theorem topThree_12 (h : x₂ ≠ x₁) : topThree x₁ x₂ x₃ x₁ x₂ := by
  simp [topThree, ordOf, h]

private theorem topThree_13 (h : x₃ ≠ x₁) : topThree x₁ x₂ x₃ x₁ x₃ := by
  simp only [topThree, ordOf, if_neg h]
  split_ifs <;> omega

private theorem topThree_23 (h₁ : x₃ ≠ x₁) (h₂ : x₃ ≠ x₂) : topThree x₁ x₂ x₃ x₂ x₃ := by
  simp only [topThree, ordOf, if_neg h₁, if_neg h₂]
  split_ifs <;> omega

private theorem not_topThree_21 (h : x₂ ≠ x₁) : ¬ topThree x₁ x₂ x₃ x₂ x₁ :=
  ordOf_asymm (topThree_12 h)

private theorem not_topThree_31 (h : x₃ ≠ x₁) : ¬ topThree x₁ x₂ x₃ x₃ x₁ :=
  ordOf_asymm (topThree_13 h)

private theorem not_topThree_32 (h₁ : x₃ ≠ x₁) (h₂ : x₃ ≠ x₂) : ¬ topThree x₁ x₂ x₃ x₃ x₂ :=
  ordOf_asymm (topThree_23 h₁ h₂)

/-- The ballot putting `b` strictly on top. -/
private noncomputable def bTopOrd (b : A) : A → A → Prop :=
  ordOf (fun z => if z = b then Fintype.card A else rk z)

/-- The ballot putting `b` strictly at the bottom. -/
private noncomputable def bBotOrd (b : A) : A → A → Prop :=
  ordOf (fun z => if z = b then 0 else rk z + 1)

private theorem isSTO_bTopOrd (b : A) : IsStrictTotalOrder A (bTopOrd b) := by
  refine isSTO_ordOf ?_
  intro u v huv
  have hu := rk_lt u
  have hv := rk_lt v
  simp only at huv
  split_ifs at huv <;> subst_vars <;>
    first
      | rfl
      | (exfalso; omega)
      | exact rk_inj huv

private theorem isSTO_bBotOrd (b : A) : IsStrictTotalOrder A (bBotOrd b) := by
  refine isSTO_ordOf ?_
  intro u v huv
  simp only at huv
  split_ifs at huv <;> subst_vars <;>
    first
      | rfl
      | (exfalso; omega)
      | exact rk_inj (by omega)

private theorem bTopOrd_top {b x : A} (h : x ≠ b) : bTopOrd b b x := by
  simp only [bTopOrd, ordOf, if_neg h]
  split_ifs <;> first | exact rk_lt x | omega

private theorem bBotOrd_bot {b x : A} (h : x ≠ b) : bBotOrd b x b := by
  simp only [bBotOrd, ordOf, if_neg h]
  split_ifs <;> omega

private theorem not_bTopOrd {b x : A} (h : x ≠ b) : ¬ bTopOrd b x b :=
  ordOf_asymm (bTopOrd_top h)

private theorem not_bBotOrd {b x : A} (h : x ≠ b) : ¬ bBotOrd b b x :=
  ordOf_asymm (bBotOrd_bot h)

end Ballots

section Arrow

variable {ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]
  {F : (ι → A → A → Prop) → A → A → Prop}

/-- `b` is the top of the relation `r`. -/
private def IsTopOf (r : A → A → Prop) (b : A) : Prop := ∀ x, x ≠ b → r b x

/-- `b` is the bottom of the relation `r`. -/
private def IsBotOf (r : A → A → Prop) (b : A) : Prop := ∀ x, x ≠ b → r x b

/-- Pareto efficiency: unanimity on a pair transfers to the social preference. -/
private theorem arrow_pareto (huna : SWFUnanimity F) (hiia : SWFIIA F)
    {P : ι → A → A → Prop} (hP : IsPrefProfile P) {a b : A} (hab : a ≠ b)
    (h : ∀ i, P i a b) : F P a b := by
  have hSTO : IsStrictTotalOrder A (topThree a b b) := isSTO_topThree
  have hr : topThree a b b a b := topThree_12 (Ne.symm hab)
  have hQ : IsPrefProfile (fun _ : ι => topThree a b b) := fun _ => hSTO
  have h1 : F (fun _ => topThree a b b) a b := (huna _ hSTO a b).2 hr
  exact (hiia P _ hP hQ a b (fun i => iff_of_true (h i) hr)).2 h1

/-- The extremal lemma: if every voter puts `b` at an extreme of their ballot,
society puts `b` at an extreme too. -/
private theorem arrow_extremal (hF : IsSWF F) (huna : SWFUnanimity F) (hiia : SWFIIA F)
    {P : ι → A → A → Prop} (hP : IsPrefProfile P) (b : A)
    (hext : ∀ i, IsTopOf (P i) b ∨ IsBotOf (P i) b) :
    IsTopOf (F P) b ∨ IsBotOf (F P) b := by
  classical
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.1 hcon
  haveI := hF P hP
  obtain ⟨a, hab, hna⟩ : ∃ a, a ≠ b ∧ ¬ F P b a := by
    by_contra h
    exact h1 fun x hx => by
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
  obtain ⟨c, hcb, hnc⟩ : ∃ c, c ≠ b ∧ ¬ F P c b := by
    by_contra h
    exact h2 fun x hx => by
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
  have hFab : F P a b := by
    rcases trichotomous_of (F P) a b with h | h | h
    · exact h
    · exact absurd h hab
    · exact absurd h hna
  have hFbc : F P b c := by
    rcases trichotomous_of (F P) b c with h | h | h
    · exact h
    · exact absurd h.symm hcb
    · exact absurd h hnc
  have hac : a ≠ c := by
    rintro rfl
    exact absurd (trans_of (F P) hFab hFbc) (irrefl_of (F P) a)
  -- every voter moves `c` above `a`, keeping `b` extremal
  set P' : ι → A → A → Prop :=
    fun i => if IsTopOf (P i) b then topThree b c a else topThree c a b with hP'
  have hP'pref : IsPrefProfile P' := by
    intro i
    simp only [hP']
    split_ifs <;> exact isSTO_topThree
  have hab' : ∀ i, P' i a b ↔ P i a b := by
    intro i
    haveI := hP i
    simp only [hP']
    split_ifs with h
    · exact iff_of_false (not_topThree_31 hab) (asymm_of (P i) (h a hab))
    · rcases hext i with h' | h'
      · exact absurd h' h
      · exact iff_of_true (topThree_23 (Ne.symm hcb) (Ne.symm hab)) (h' a hab)
  have hbc' : ∀ i, P' i b c ↔ P i b c := by
    intro i
    haveI := hP i
    simp only [hP']
    split_ifs with h
    · exact iff_of_true (topThree_12 hcb) (h c hcb)
    · rcases hext i with h' | h'
      · exact absurd h' h
      · exact iff_of_false (not_topThree_31 (Ne.symm hcb)) (asymm_of (P i) (h' c hcb))
  have hca' : ∀ i, P' i c a := by
    intro i
    simp only [hP']
    split_ifs with h
    · exact topThree_23 hab hac
    · exact topThree_12 hac
  haveI := hF P' hP'pref
  have e1 : F P' a b := (hiia P' P hP'pref hP a b hab').2 hFab
  have e2 : F P' b c := (hiia P' P hP'pref hP b c hbc').2 hFbc
  have e3 : F P' a c := trans_of (F P') e1 e2
  have e4 : F P' c a := arrow_pareto huna hiia hP'pref (Ne.symm hac) hca'
  exact absurd e4 (asymm_of (F P') e3)

/-- The profile in which the voters of `S` put `b` on top and all others put
`b` at the bottom. -/
private noncomputable def pivProfile (b : A) (S : Finset ι) : ι → A → A → Prop :=
  fun i => if i ∈ S then bTopOrd b else bBotOrd b

private theorem pivProfile_mem {b : A} {S : Finset ι} {i : ι} (h : i ∈ S) :
    pivProfile b S i = bTopOrd b := by
  simp only [pivProfile, if_pos h]

private theorem pivProfile_not_mem {b : A} {S : Finset ι} {i : ι} (h : i ∉ S) :
    pivProfile b S i = bBotOrd b := by
  simp only [pivProfile, if_neg h]

private theorem pivProfile_pref (b : A) (S : Finset ι) : IsPrefProfile (pivProfile b S) := by
  intro i
  by_cases h : i ∈ S
  · rw [pivProfile_mem h]; exact isSTO_bTopOrd b
  · rw [pivProfile_not_mem h]; exact isSTO_bBotOrd b

private theorem pivProfile_ext (b : A) (S : Finset ι) (i : ι) :
    IsTopOf (pivProfile b S i) b ∨ IsBotOf (pivProfile b S i) b := by
  by_cases h : i ∈ S
  · rw [pivProfile_mem h]; exact Or.inl fun x hx => bTopOrd_top hx
  · rw [pivProfile_not_mem h]; exact Or.inr fun x hx => bBotOrd_bot hx

private theorem pivProfile_empty_bot (huna : SWFUnanimity F) (hiia : SWFIIA F) (b : A) :
    IsBotOf (F (pivProfile b (∅ : Finset ι))) b := by
  intro x hx
  refine arrow_pareto huna hiia (pivProfile_pref b ∅) hx fun i => ?_
  rw [pivProfile_not_mem (by simp : i ∉ (∅ : Finset ι))]
  exact bBotOrd_bot hx

private theorem pivProfile_univ_top (huna : SWFUnanimity F) (hiia : SWFIIA F) (b : A) :
    IsTopOf (F (pivProfile b (Finset.univ : Finset ι))) b := by
  intro x hx
  refine arrow_pareto huna hiia (pivProfile_pref b _) (Ne.symm hx) fun i => ?_
  rw [pivProfile_mem (Finset.mem_univ i)]
  exact bTopOrd_top hx

/-- There is a voter whose switch from "`b` last" to "`b` first" flips the social
placement of `b` from bottom to top. -/
private theorem exists_pivotal (hF : IsSWF F) (huna : SWFUnanimity F) (hiia : SWFIIA F)
    (b : A) (hne : ∃ z : A, z ≠ b) :
    ∃ (S : Finset ι) (i : ι), i ∉ S ∧ IsBotOf (F (pivProfile b S)) b ∧
      IsTopOf (F (pivProfile b (insert i S))) b := by
  classical
  obtain ⟨z, hz⟩ := hne
  suffices H : ∀ n : ℕ, ∀ S : Finset ι, (Finset.univ \ S).card = n →
      IsBotOf (F (pivProfile b S)) b →
      ∃ (S' : Finset ι) (i : ι), i ∉ S' ∧ IsBotOf (F (pivProfile b S')) b ∧
        IsTopOf (F (pivProfile b (insert i S'))) b by
    exact H _ ∅ rfl (pivProfile_empty_bot huna hiia b)
  intro n
  induction n with
  | zero =>
      intro S hcard hbot
      exfalso
      have hsub : (Finset.univ : Finset ι) ⊆ S := by
        have : Finset.univ \ S = (∅ : Finset ι) := Finset.card_eq_zero.1 hcard
        intro w _
        by_contra hw
        have : w ∈ Finset.univ \ S := Finset.mem_sdiff.2 ⟨Finset.mem_univ w, hw⟩
        simp_all
      have hSu : S = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ S) hsub
      subst hSu
      haveI := hF (pivProfile b (Finset.univ : Finset ι)) (pivProfile_pref b _)
      exact absurd (hbot z hz)
        (asymm_of (F (pivProfile b (Finset.univ : Finset ι)))
          (pivProfile_univ_top huna hiia b z hz))
  | succ n ih =>
      intro S hcard hbot
      have hpos : 0 < (Finset.univ \ S).card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
      have hiS : i ∉ S := (Finset.mem_sdiff.1 hi).2
      by_cases htop : IsTopOf (F (pivProfile b (insert i S))) b
      · exact ⟨S, i, hiS, hbot, htop⟩
      · have hbot' : IsBotOf (F (pivProfile b (insert i S))) b := by
          rcases arrow_extremal hF huna hiia (pivProfile_pref b (insert i S)) b
            (pivProfile_ext b (insert i S)) with h | h
          · exact absurd h htop
          · exact h
        refine ih (insert i S) ?_ hbot'
        have : Finset.univ \ insert i S = (Finset.univ \ S).erase i := by
          ext w
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_univ,
            true_and]
          tauto
        rw [this, Finset.card_erase_of_mem hi, hcard]
        omega


/-- The pivotal voter dictates every pair of alternatives avoiding `b`. -/
private theorem pivotal_dictates (hF : IsSWF F) (hiia : SWFIIA F)
    {b : A} {S : Finset ι} {i : ι} (hiS : i ∉ S)
    (hbot : IsBotOf (F (pivProfile b S)) b)
    (htop : IsTopOf (F (pivProfile b (insert i S))) b)
    {P : ι → A → A → Prop} (hP : IsPrefProfile P) {x y : A}
    (hxb : x ≠ b) (hyb : y ≠ b) (hxy : x ≠ y) (hxyP : P i x y) : F P x y := by
  classical
  set Q : ι → A → A → Prop := fun j =>
    if j = i then topThree x b y
    else if j ∈ S then (if P j x y then topThree b x y else topThree b y x)
    else (if P j x y then topThree x y b else topThree y x b) with hQ
  have hQpref : IsPrefProfile Q := by
    intro j
    simp only [hQ]
    split_ifs <;> exact isSTO_topThree
  have hQxb : ∀ j, Q j x b ↔ pivProfile b S j x b := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [pivProfile_not_mem hiS]
      simp only [hQ, if_pos rfl]
      exact iff_of_true (topThree_12 (Ne.symm hxb)) (bBotOrd_bot hxb)
    · by_cases hjS : j ∈ S
      · rw [pivProfile_mem hjS]
        simp only [hQ, if_neg hj, if_pos hjS]
        split_ifs
        · exact iff_of_false (not_topThree_21 hxb) (not_bTopOrd hxb)
        · exact iff_of_false (not_topThree_31 hxb) (not_bTopOrd hxb)
      · rw [pivProfile_not_mem hjS]
        simp only [hQ, if_neg hj, if_neg hjS]
        split_ifs
        · exact iff_of_true (topThree_13 (Ne.symm hxb)) (bBotOrd_bot hxb)
        · exact iff_of_true (topThree_23 (Ne.symm hyb) (Ne.symm hxb)) (bBotOrd_bot hxb)
  have hQby : ∀ j, Q j b y ↔ pivProfile b (insert i S) j b y := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [pivProfile_mem (Finset.mem_insert_self _ _)]
      simp only [hQ, if_pos rfl]
      exact iff_of_true (topThree_23 (Ne.symm hxy) hyb) (bTopOrd_top hyb)
    · by_cases hjS : j ∈ S
      · rw [pivProfile_mem (Finset.mem_insert_of_mem hjS)]
        simp only [hQ, if_neg hj, if_pos hjS]
        split_ifs
        · exact iff_of_true (topThree_13 hyb) (bTopOrd_top hyb)
        · exact iff_of_true (topThree_12 hyb) (bTopOrd_top hyb)
      · have hjins : j ∉ insert i S := by
          simp only [Finset.mem_insert]
          tauto
        rw [pivProfile_not_mem hjins]
        simp only [hQ, if_neg hj, if_neg hjS]
        split_ifs
        · exact iff_of_false (not_topThree_32 (Ne.symm hxb) (Ne.symm hyb)) (not_bBotOrd hyb)
        · exact iff_of_false (not_topThree_31 (Ne.symm hyb)) (not_bBotOrd hyb)
  have hQxy : ∀ j, Q j x y ↔ P j x y := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [hQ, if_pos rfl]
      exact iff_of_true (topThree_13 (Ne.symm hxy)) hxyP
    · by_cases hjS : j ∈ S
      · simp only [hQ, if_neg hj, if_pos hjS]
        split_ifs with hc
        · exact iff_of_true (topThree_23 hyb (Ne.symm hxy)) hc
        · exact iff_of_false (not_topThree_32 hxb hxy) hc
      · simp only [hQ, if_neg hj, if_neg hjS]
        split_ifs with hc
        · exact iff_of_true (topThree_12 (Ne.symm hxy)) hc
        · exact iff_of_false (not_topThree_21 hxy) hc
  haveI := hF Q hQpref
  have h1 : F Q x b :=
    (hiia Q (pivProfile b S) hQpref (pivProfile_pref b S) x b hQxb).2 (hbot x hxb)
  have h2 : F Q b y :=
    (hiia Q (pivProfile b (insert i S)) hQpref (pivProfile_pref b _) b y hQby).2 (htop y hyb)
  exact (hiia Q P hQpref hP x y hQxy).1 (trans_of (F Q) h1 h2)

/-- For every alternative `b` there is a voter dictating all pairs avoiding `b`,
together with the two profiles witnessing that this voter is pivotal for `b`. -/
private theorem exists_dictator_off (hF : IsSWF F) (huna : SWFUnanimity F) (hiia : SWFIIA F)
    (b : A) (hne : ∃ z : A, z ≠ b) :
    ∃ (i : ι) (S : Finset ι), i ∉ S ∧ IsBotOf (F (pivProfile b S)) b ∧
      IsTopOf (F (pivProfile b (insert i S))) b ∧
      ∀ P : ι → A → A → Prop, IsPrefProfile P → ∀ x y : A, x ≠ b → y ≠ b →
        (F P x y ↔ P i x y) := by
  obtain ⟨S, i, hiS, hbot, htop⟩ := exists_pivotal hF huna hiia b hne
  refine ⟨i, S, hiS, hbot, htop, fun P hP x y hxb hyb => ?_⟩
  haveI := hF P hP
  haveI := hP i
  by_cases hxy : x = y
  · subst hxy
    exact iff_of_false (irrefl_of (F P) x) (irrefl_of (P i) x)
  · constructor
    · intro h
      by_contra hc
      have : P i y x := by
        rcases trichotomous_of (P i) x y with h' | h' | h'
        · exact absurd h' hc
        · exact absurd h' hxy
        · exact h'
      exact absurd (pivotal_dictates hF hiia hiS hbot htop hP hyb hxb (Ne.symm hxy) this)
        (asymm_of (F P) h)
    · intro h
      exact pivotal_dictates hF hiia hiS hbot htop hP hxb hyb hxy h

/-- **Theorem 9.3 of *Algorithmic Game Theory* (Arrow)**. -/
theorem arrow_theorem' [Nonempty ι] (hA : 2 < Fintype.card A)
    (hF : IsSWF F) (huna : SWFUnanimity F) (hiia : SWFIIA F) :
    ∃ i : ι, SWFDictator F i := by
  classical
  have hcardA : 0 < Fintype.card A := by omega
  have : Nonempty A := Fintype.card_pos_iff.1 hcardA
  have hne : ∀ b : A, ∃ z : A, z ≠ b := fun b =>
    Fintype.exists_ne_of_one_lt_card (by omega) b
  obtain ⟨b₀⟩ := ‹Nonempty A›
  obtain ⟨i₀, S₀, hiS₀, hbot₀, htop₀, hdict₀⟩ :=
    exists_dictator_off hF huna hiia b₀ (hne b₀)
  refine ⟨i₀, fun P hP x y => ?_⟩
  haveI := hF P hP
  haveI := hP i₀
  by_cases hxy : x = y
  · subst hxy
    exact iff_of_false (irrefl_of (F P) x) (irrefl_of (P i₀) x)
  by_cases hxb : x = b₀
  · -- the pair involves `b₀`; use a dictator for a third alternative
    have hyb : y ≠ b₀ := by rw [← hxb]; exact fun h => hxy h.symm
    obtain ⟨c, hcx, hcy⟩ : ∃ c : A, c ≠ x ∧ c ≠ y := by
      by_contra hcon
      have hsub : (Finset.univ : Finset A) ⊆ {x, y} := by
        intro z _
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hz : z = x
        · exact Or.inl hz
        · by_cases hz' : z = y
          · exact Or.inr hz'
          · exact absurd ⟨z, hz, hz'⟩ hcon
      have h1 : Fintype.card A ≤ ({x, y} : Finset A).card := by
        simpa using Finset.card_le_card hsub
      have h2 : ({x, y} : Finset A).card ≤ 2 := by
        apply le_trans (Finset.card_insert_le _ _)
        simp
      omega
    obtain ⟨ic, Sc, _, _, _, hdictc⟩ := exists_dictator_off hF huna hiia c (hne c)
    have hic : ic = i₀ := by
      by_contra hne'
      have hagree : pivProfile b₀ S₀ ic = pivProfile b₀ (insert i₀ S₀) ic := by
        by_cases hm : ic ∈ S₀
        · rw [pivProfile_mem hm, pivProfile_mem (Finset.mem_insert_of_mem hm)]
        · have : ic ∉ insert i₀ S₀ := by
            simp only [Finset.mem_insert]
            tauto
          rw [pivProfile_not_mem hm, pivProfile_not_mem this]
      have e1 := hdictc (pivProfile b₀ S₀) (pivProfile_pref b₀ S₀) x y (Ne.symm hcx) (Ne.symm hcy)
      have e2 := hdictc (pivProfile b₀ (insert i₀ S₀)) (pivProfile_pref b₀ _) x y
        (Ne.symm hcx) (Ne.symm hcy)
      rw [hagree] at e1
      have hsame : F (pivProfile b₀ S₀) x y ↔ F (pivProfile b₀ (insert i₀ S₀)) x y :=
        e1.trans e2.symm
      subst hxb
      haveI := hF (pivProfile x S₀) (pivProfile_pref x S₀)
      exact absurd (hsame.2 (htop₀ y hyb)) (asymm_of (F (pivProfile x S₀)) (hbot₀ y hyb))
    subst hic
    exact hdictc P hP x y (Ne.symm hcx) (Ne.symm hcy)
  by_cases hyb : y = b₀
  · obtain ⟨c, hcx, hcy⟩ : ∃ c : A, c ≠ x ∧ c ≠ y := by
      by_contra hcon
      have hsub : (Finset.univ : Finset A) ⊆ {x, y} := by
        intro z _
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hz : z = x
        · exact Or.inl hz
        · by_cases hz' : z = y
          · exact Or.inr hz'
          · exact absurd ⟨z, hz, hz'⟩ hcon
      have h1 : Fintype.card A ≤ ({x, y} : Finset A).card := by
        simpa using Finset.card_le_card hsub
      have h2 : ({x, y} : Finset A).card ≤ 2 := by
        apply le_trans (Finset.card_insert_le _ _)
        simp
      omega
    obtain ⟨ic, Sc, _, _, _, hdictc⟩ := exists_dictator_off hF huna hiia c (hne c)
    have hic : ic = i₀ := by
      by_contra hne'
      have hagree : pivProfile b₀ S₀ ic = pivProfile b₀ (insert i₀ S₀) ic := by
        by_cases hm : ic ∈ S₀
        · rw [pivProfile_mem hm, pivProfile_mem (Finset.mem_insert_of_mem hm)]
        · have : ic ∉ insert i₀ S₀ := by
            simp only [Finset.mem_insert]
            tauto
          rw [pivProfile_not_mem hm, pivProfile_not_mem this]
      have e1 := hdictc (pivProfile b₀ S₀) (pivProfile_pref b₀ S₀) x y (Ne.symm hcx) (Ne.symm hcy)
      have e2 := hdictc (pivProfile b₀ (insert i₀ S₀)) (pivProfile_pref b₀ _) x y
        (Ne.symm hcx) (Ne.symm hcy)
      rw [hagree] at e1
      have hsame : F (pivProfile b₀ S₀) x y ↔ F (pivProfile b₀ (insert i₀ S₀)) x y :=
        e1.trans e2.symm
      subst hyb
      haveI := hF (pivProfile y (insert i₀ S₀)) (pivProfile_pref y _)
      exact absurd (hsame.1 (hbot₀ x hxb))
        (asymm_of (F (pivProfile y (insert i₀ S₀))) (htop₀ x hxb))
    subst hic
    exact hdictc P hP x y (Ne.symm hcx) (Ne.symm hcy)
  · exact hdict₀ P hP x y hxb hyb

end Arrow

end AGT

open AGT in
/-- **Theorem 9.3 of *Algorithmic Game Theory* (Arrow)**: every social
welfare function over more than two alternatives that satisfies unanimity
and independence of irrelevant alternatives is a dictatorship. -/
theorem solution {A ι : Type*} [Fintype A] [Fintype ι] [Nonempty ι]
    (hA : 2 < Fintype.card A) (F : (ι → A → A → Prop) → A → A → Prop)
    (hF : IsSWF F) (huna : SWFUnanimity F) (hiia : SWFIIA F) :
    ∃ i : ι, SWFDictator F i := by
  classical
  exact arrow_theorem' hA hF huna hiia
