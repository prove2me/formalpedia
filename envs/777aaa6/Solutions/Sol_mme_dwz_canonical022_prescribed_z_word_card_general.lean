-- Prove2me | solution 1 for mme_dwz_canonical022_prescribed_z_word_card_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T07:13:03.372751+00:00
-- url     : https://prove2.me/submissions/562fe9f4-7595-4c3b-86bc-606ef01274ea

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_kron_pow_word_reindex
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

open MME MME.DWZFineChannel MME.DWZComponentRestriction
open scoped Classical BigOperators
open MME.DWZRestrictedValue

set_option autoImplicit false
set_option warningAsError true

private theorem fine022Pair_injective (q : ℕ) :
    Function.Injective (fun c : Fine022Channel q ↦ fine022SourcePair q c 2) := by
  intro c d h
  have hx := congrArg (fun p : Fin (q + 2) × Fin (q + 2) ↦ p.1.val) h
  have hy := congrArg (fun p : Fin (q + 2) × Fin (q + 2) ↦ p.2.val) h
  rcases c with c | (⟨i, j⟩ | c)
  <;> rcases d with d | (⟨k, l⟩ | d)
  · exact congrArg Sum.inl (Subsingleton.elim _ _)
  · simp only [fine022SourcePair, cwT, cwM] at hx
    omega
  · simp only [fine022SourcePair, cwT, cwO] at hx
    omega
  · simp only [fine022SourcePair, cwT, cwM] at hx
    omega
  · have hi : i = k := Fin.ext (by simpa only [fine022SourcePair, cwM, Nat.add_right_cancel_iff] using hx)
    have hj : j = l := Fin.ext (by simpa only [fine022SourcePair, cwM, Nat.add_right_cancel_iff] using hy)
    subst k
    subst l
    rfl
  · simp only [fine022SourcePair, cwM, cwO] at hx
    omega
  · simp only [fine022SourcePair, cwO, cwT] at hx
    omega
  · simp only [fine022SourcePair, cwO, cwM] at hx
    omega
  · exact congrArg Sum.inr (congrArg Sum.inr (Subsingleton.elim _ _))

private theorem fine022Pair_grade (q : ℕ) (c : Fine022Channel q) :
    cwSquarePairGrade q (fine022SourcePair q c 2) = 2 := by
  rcases c with c | (⟨i, j⟩ | c)
  · apply Fin.ext
    simp [fine022SourcePair, cwSquarePairGrade, cwSquareCoordGrade, cwT, cwO]
  · have hi : i.val ≠ q := by omega
    have hj : j.val ≠ q := by omega
    apply Fin.ext
    simp [fine022SourcePair, cwSquarePairGrade, cwSquareCoordGrade, cwM, hi, hj]
  · apply Fin.ext
    simp [fine022SourcePair, cwSquarePairGrade, cwSquareCoordGrade, cwT, cwO]

private def channelGrade {q : ℕ} : Fine022Channel q → Fin 3
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 0

private theorem fine022Pair_left_grade (q : ℕ) (c : Fine022Channel q) :
    cwSquareCoordGrade q (fine022SourcePair q c 2).1 = channelGrade c := by
  rcases c with c | (⟨i, j⟩ | c)
  · simp [fine022SourcePair, cwSquareCoordGrade, cwT, channelGrade]
  · have hi : i.val ≠ q := by omega
    simp [fine022SourcePair, cwSquareCoordGrade, cwM, channelGrade, hi]
  · simp [fine022SourcePair, cwSquareCoordGrade, cwO, channelGrade]

private theorem fine022SourcePair_covers (q : ℕ) (p : CoarsePair q 2) :
    ∃ c : Fine022Channel q, fine022SourcePair q c 2 = p.1 := by
  rcases p with ⟨⟨a, b⟩, hp⟩
  have hgrade : (cwSquareCoordGrade q a).val + (cwSquareCoordGrade q b).val = 2 :=
    congrArg Fin.val hp
  by_cases ha0 : a.val = 0
  · have hbT : b.val = q + 1 := by
      simp only [cwSquareCoordGrade, ha0, ↓reduceIte] at hgrade
      split_ifs at hgrade <;> simp_all
    refine ⟨Sum.inr (Sum.inr 0), ?_⟩
    apply Prod.ext <;> apply Fin.ext
    · exact ha0.symm
    · exact hbT.symm
  by_cases haT : a.val = q + 1
  · have hb0 : b.val = 0 := by
      simp only [cwSquareCoordGrade, haT, ↓reduceIte] at hgrade
      split_ifs at hgrade <;> simp_all
    refine ⟨Sum.inl 0, ?_⟩
    apply Prod.ext <;> apply Fin.ext
    · exact haT.symm
    · exact hb0.symm
  have hb0 : b.val ≠ 0 := by
    intro hb
    simp [cwSquareCoordGrade, ha0, haT, hb] at hgrade
  have hbT : b.val ≠ q + 1 := by
    intro hb
    simp [cwSquareCoordGrade, ha0, haT, hb] at hgrade
  have ha : a.val - 1 < q := by omega
  have hb : b.val - 1 < q := by omega
  refine ⟨Sum.inr (Sum.inl (⟨a.val - 1, ha⟩, ⟨b.val - 1, hb⟩)), ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · change a.val - 1 + 1 = a.val
    omega
  · change b.val - 1 + 1 = b.val
    omega

universe u

private def channelClass {q : ℕ} : Fine022Channel q → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

private def swapChannel {q : ℕ} : Fine022Channel q → Fine022Channel q
  | Sum.inl c => Sum.inr (Sum.inr c)
  | Sum.inr (Sum.inl ij) => Sum.inr (Sum.inl ij)
  | Sum.inr (Sum.inr c) => Sum.inl c

private theorem swapChannel_involutive {q : ℕ} :
    Function.Involutive (@swapChannel q) := by
  intro c
  rcases c with c | (ij | c) <;> rfl

private noncomputable def gradeLetterEquiv (q : ℕ) :
    Fine022Channel q ≃ CoarsePair q 2 :=
  Equiv.ofBijective
    (fun c ↦ ⟨fine022SourcePair q (swapChannel c) 2,
      fine022Pair_grade q (swapChannel c)⟩) (by
      constructor
      · intro c d h
        apply swapChannel_involutive.injective
        exact fine022Pair_injective q (congrArg Subtype.val h)
      · intro p
        obtain ⟨c, hc⟩ := fine022SourcePair_covers q p
        refine ⟨swapChannel c, ?_⟩
        apply Subtype.ext
        simpa only [swapChannel_involutive c] using hc)

private theorem gradeLetterEquiv_grade (q : ℕ) (c : Fine022Channel q) :
    CoarsePair.leftGrade (gradeLetterEquiv q c) = channelClass c := by
  change cwSquareCoordGrade q (fine022SourcePair q (swapChannel c) 2).1 = _
  rw [fine022Pair_left_grade]
  rcases c with c | (ij | c) <;> rfl

private def middleLabel {q : ℕ} (c : Fine022Channel q)
    (h : channelClass c = 1) : Fin q × Fin q := by
  rcases c with c | (ij | c)
  · simp [channelClass] at h
  · exact ij
  · simp [channelClass] at h


private def profileMultiplicity (A B C : ℕ) : Fin 3 → ℕ := ![A, B, C]

private def ProfilePattern (N A B C : ℕ) :=
  {p : Fin N → Fin 3 // ∀ a,
    Fintype.card {r : Fin N // p r = a} = profileMultiplicity A B C a}

private def Profile022Word (q N A B C : ℕ) :=
  Σ p : ProfilePattern N A B C,
    ({r : Fin N // p.1 r = (1 : Fin 3)} → Fin q × Fin q)

private def encodeProfileWord {q N A B C : ℕ}
    (w : Profile022Word q N A B C) : Fin N → Fine022Channel q := fun r ↦
  if _h0 : w.1.1 r = (0 : Fin 3) then
    Sum.inl 0
  else if h1 : w.1.1 r = (1 : Fin 3) then
    Sum.inr (Sum.inl (w.2 ⟨r, h1⟩))
  else
    Sum.inr (Sum.inr 0)

private abbrev ProfileWord (q N A B C : ℕ) :=
  {w : PowIndex (LiftedCoarsePair.{u} q 2) N // ∀ a : Fin 3,
    Fintype.card {r : Fin N // (PowIndex.get N w r).leftGrade = a} =
      profileMultiplicity A B C a}

private noncomputable def decodedWord (q N : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} q 2) N) : Fin N → Fine022Channel q :=
  fun r ↦ (gradeLetterEquiv q).symm (PowIndex.get N w r).down

private theorem decodedWord_grade (q N : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} q 2) N) (r : Fin N) :
    channelClass (decodedWord q N w r) = (PowIndex.get N w r).leftGrade := by
  rw [← gradeLetterEquiv_grade]
  change CoarsePair.leftGrade
      (gradeLetterEquiv q ((gradeLetterEquiv q).symm _)) = _
  rw [Equiv.apply_symm_apply]
  rfl

private noncomputable def toProfile {q N A B C : ℕ}
    (w : ProfileWord.{u} q N A B C) : Profile022Word q N A B C := by
  refine ⟨⟨fun r ↦ channelClass (decodedWord q N w.1 r), ?_⟩, ?_⟩
  · intro a
    simpa only [decodedWord_grade] using w.2 a
  · exact fun r ↦ middleLabel (decodedWord q N w.1 r.1) r.2

private theorem encode_toProfile {q N A B C : ℕ}
    (w : ProfileWord.{u} q N A B C) :
    encodeProfileWord (toProfile w) = decodedWord q N w.1 := by
  funext r
  rcases h : decodedWord q N w.1 r with c | (ij | c)
  · have hc : c = 0 := Subsingleton.elim _ _
    subst c
    simp [toProfile, encodeProfileWord, h, channelClass]
  · simp [toProfile, encodeProfileWord, h, channelClass]
    rfl
  · have hc : c = 0 := Subsingleton.elim _ _
    subst c
    simp [toProfile, encodeProfileWord, h, channelClass]

private theorem class_encode {q N A B C : ℕ}
    (w : Profile022Word q N A B C) (r : Fin N) :
    channelClass (encodeProfileWord w r) = w.1.1 r := by
  by_cases h0 : w.1.1 r = 0
  · simp [encodeProfileWord, channelClass, h0]
  by_cases h1 : w.1.1 r = 1
  · simp [encodeProfileWord, channelClass, h1]
  have h2 : w.1.1 r = 2 := by
    apply Fin.ext
    omega
  simp [encodeProfileWord, channelClass, h2]


private theorem encodeProfileWord_at_middle
    {q N A B C : ℕ} (p : ProfilePattern N A B C)
    (label : {r : Fin N // p.1 r = (1 : Fin 3)} → Fin q × Fin q)
    (r : {r : Fin N // p.1 r = (1 : Fin 3)}) :
    encodeProfileWord ⟨p, label⟩ r.1 = Sum.inr (Sum.inl (label r)) := by
  simp [encodeProfileWord, r.2]

private theorem encodeProfileWord_injective {q N A B C : ℕ} :
    Function.Injective
      (encodeProfileWord : Profile022Word q N A B C → (Fin N → Fine022Channel q)) := by
  intro w v h
  have hp : w.1 = v.1 := by
    apply Subtype.ext
    funext r
    rw [← class_encode w r, ← class_encode v r, h]
  cases w with
  | mk wp wl =>
    cases v with
    | mk vp vl =>
      dsimp only at hp
      subst vp
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext r
        have hr := congrFun h r.1
        rw [encodeProfileWord_at_middle wp wl r,
          encodeProfileWord_at_middle wp vl r] at hr
        exact Sum.inl.inj (Sum.inr.inj hr)

private noncomputable def fromProfile {q N A B C : ℕ}
    (w : Profile022Word q N A B C) : ProfileWord.{u} q N A B C := by
  refine ⟨PowIndex.ofFun N
    (fun r ↦ ULift.up (gradeLetterEquiv q (encodeProfileWord w r))), ?_⟩
  intro a
  simpa only [PowIndex.get_ofFun, LiftedCoarsePair.leftGrade,
    gradeLetterEquiv_grade, class_encode] using w.1.2 a

private theorem decoded_fromProfile {q N A B C : ℕ}
    (w : Profile022Word q N A B C) :
    decodedWord q N (fromProfile.{u} w).1 = encodeProfileWord w := by
  funext r
  simp [decodedWord, fromProfile, PowIndex.get_ofFun]

private noncomputable def canonicalWordEquiv (q N A B C : ℕ) :
    ProfileWord.{u} q N A B C ≃ Profile022Word q N A B C where
  toFun := toProfile
  invFun := fromProfile
  left_inv w := by
    apply Subtype.ext
    apply (PowIndex.equivFun (LiftedCoarsePair.{u} q 2) N).injective
    funext r
    apply ULift.ext
    apply (gradeLetterEquiv q).symm.injective
    have h := congrFun (decoded_fromProfile (toProfile w)) r
    rw [encode_toProfile] at h
    exact h
  right_inv w := by
    apply encodeProfileWord_injective
    rw [encode_toProfile, decoded_fromProfile]


private def splitWordCount (N A C : ℕ) : ℕ := Nat.choose N A * Nat.choose (N - A) C

private theorem profileWord_card
    (q N A B C : ℕ) (hcount : A + B + C = N) :
    Nat.card (Profile022Word q N A B C) = splitWordCount N A C * q ^ (2 * B) := by
  have hsum : ∑ a : Fin 3, profileMultiplicity A B C a = N := by
    simpa [profileMultiplicity, Fin.sum_univ_succ, Nat.add_assoc] using hcount
  let patternPredicate : (Fin N → Fin 3) → Prop := fun g ↦
    ∀ i, Fintype.card {a : Fin N // g a = i} = profileMultiplicity A B C i
  letI patternDecidable : DecidablePred patternPredicate := fun _ ↦
    Fintype.decidableForallFintype
  letI patternFintype : Fintype {g : Fin N → Fin 3 // patternPredicate g} :=
    Subtype.fintype patternPredicate
  have hpattern0 :=
    mme_fintype_prescribed_fiber_function_card
      (α := Fin N) (ι := Fin 3) (profileMultiplicity A B C) (by simpa using hsum)
  have hpatternNat0 :
      Nat.card
          {g : Fin N → Fin 3 // ∀ i,
            Fintype.card {a : Fin N // g a = i} = profileMultiplicity A B C i} =
        N.factorial / ∏ i, (profileMultiplicity A B C i).factorial := by
    calc
      Nat.card
          {g : Fin N → Fin 3 // ∀ i,
            Fintype.card {a : Fin N // g a = i} = profileMultiplicity A B C i} =
          Fintype.card
            {g : Fin N → Fin 3 // ∀ i,
              Fintype.card {a : Fin N // g a = i} = profileMultiplicity A B C i} :=
        Nat.card_eq_fintype_card
      _ = N.factorial / ∏ i, (profileMultiplicity A B C i).factorial := by
        simpa using hpattern0
  have hpattern :
      Nat.card (ProfilePattern N A B C) =
        N.factorial / (A.factorial * B.factorial * C.factorial) := by
    simpa [ProfilePattern, profileMultiplicity, Fin.prod_univ_succ, Nat.mul_assoc]
      using hpatternNat0
  have hAN : A ≤ N := by omega
  have hCrem : C ≤ N - A := by omega
  have hfirst := Nat.choose_mul_factorial_mul_factorial hAN
  have hsecond := Nat.choose_mul_factorial_mul_factorial hCrem
  rw [show N - A - C = B by omega] at hsecond
  have hfactorial :
      (A.factorial * B.factorial * C.factorial) * splitWordCount N A C =
        N.factorial := by
    rw [splitWordCount]
    calc
      (A.factorial * B.factorial * C.factorial) *
            (Nat.choose N A * Nat.choose (N - A) C) =
          Nat.choose N A * A.factorial *
            (Nat.choose (N - A) C * C.factorial * B.factorial) := by ring
      _ = Nat.choose N A * A.factorial * (N - A).factorial := by rw [hsecond]
      _ = N.factorial := hfirst
  have hmultinomial :
      N.factorial / (A.factorial * B.factorial * C.factorial) =
        splitWordCount N A C := by
    symm
    exact Nat.eq_div_of_mul_eq_right (by positivity) hfactorial
  have hmiddle (p : ProfilePattern N A B C) :
      Nat.card ({r : Fin N // p.1 r = (1 : Fin 3)} → Fin q × Fin q) =
        q ^ (2 * B) := by
    have hp := p.2 (1 : Fin 3)
    simp [profileMultiplicity] at hp
    have hpNat : Nat.card {r : Fin N // p.1 r = (1 : Fin 3)} = B := by
      rw [Nat.card_eq_fintype_card]
      exact hp
    rw [Nat.card_fun, Nat.card_prod, hpNat]
    simp only [Nat.card_fin]
    rw [show q * q = q ^ 2 by ring]
    rw [← pow_mul]
  letI : Fintype (ProfilePattern N A B C) := patternFintype
  unfold Profile022Word
  rw [Nat.card_sigma]
  simp_rw [hmiddle]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hpattern, hmultinomial]
  rfl

theorem solution
    (q : ℕ) (p : IntegerZSplitProfile 3) (m : ℕ) :
    Nat.card {w : PowIndex (LiftedCoarsePair.{u} q 2) (p.length m) //
      prescribedZWord LiftedCoarsePair.leftGrade p m w} =
      Nat.choose (p.length m) (p.count 0 * m) *
        Nat.choose (p.length m - p.count 0 * m) (p.count 2 * m) *
          q ^ (2 * (p.count 1 * m)) := by
  have hcounts (a : Fin 3) :
      p.count a * m =
        profileMultiplicity (p.count 0 * m) (p.count 1 * m) (p.count 2 * m) a := by
    fin_cases a <;> simp [profileMultiplicity]
  have hcount :
      p.count 0 * m + p.count 1 * m + p.count 2 * m = p.length m := by
    have hp : p.count 0 + p.count 1 + p.count 2 = p.denominator := by
      simpa only [Fin.sum_univ_succ, Nat.add_zero, Nat.add_assoc] using p.count_sum
    unfold IntegerZSplitProfile.length
    rw [← hp]
    ring
  have heq (w : PowIndex (LiftedCoarsePair.{u} q 2) (p.length m)) :
      prescribedZWord LiftedCoarsePair.leftGrade p m w ↔
        ∀ a : Fin 3,
          Fintype.card {r : Fin (p.length m) //
            (PowIndex.get (p.length m) w r).leftGrade = a} =
              profileMultiplicity (p.count 0 * m) (p.count 1 * m) (p.count 2 * m) a := by
    simp only [prescribedZWord, leftGradeCount, Fintype.card_subtype]
    apply forall_congr'
    intro a
    rw [hcounts a]
  let e :=
    (Equiv.subtypeEquivRight heq).trans
      (canonicalWordEquiv.{u} q (p.length m)
        (p.count 0 * m) (p.count 1 * m) (p.count 2 * m))
  rw [Nat.card_congr e, profileWord_card q _ _ _ _ hcount]
  rfl
