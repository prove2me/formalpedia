-- Prove2me | solution 1 for mme_dwz_canonical022_prescribed_z_word_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T07:01:17.186089+00:00
-- url     : https://prove2.me/submissions/53db9f96-ca6e-447d-af91-18e0484caa9a

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
import Definitions.Def_mme_dwz_central_restricted_word_projectors
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

private abbrev SymmetricWord (q N L G : ℕ) :=
  {w : PowIndex (LiftedCoarsePair.{u} q 2) N // ∀ a : Fin 3,
    Fintype.card {r : Fin N // (PowIndex.get N w r).leftGrade = a} =
      centralSplitMultiplicity L G a}

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

private noncomputable def toCentral {q N L G : ℕ}
    (w : SymmetricWord.{u} q N L G) : CentralRestricted022Word q N L G := by
  refine ⟨⟨fun r ↦ channelClass (decodedWord q N w.1 r), ?_⟩, ?_⟩
  · intro a
    simpa only [decodedWord_grade] using w.2 a
  · exact fun r ↦ middleLabel (decodedWord q N w.1 r.1) r.2

private theorem encode_toCentral {q N L G : ℕ}
    (w : SymmetricWord.{u} q N L G) :
    encodeCentralRestricted022Word (toCentral w) = decodedWord q N w.1 := by
  funext r
  rcases h : decodedWord q N w.1 r with c | (ij | c)
  · have hc : c = 0 := Subsingleton.elim _ _
    subst c
    simp [toCentral, encodeCentralRestricted022Word, h, channelClass]
  · simp [toCentral, encodeCentralRestricted022Word, h, channelClass]
    rfl
  · have hc : c = 0 := Subsingleton.elim _ _
    subst c
    simp [toCentral, encodeCentralRestricted022Word, h, channelClass]

private theorem class_encode {q N L G : ℕ}
    (w : CentralRestricted022Word q N L G) (r : Fin N) :
    channelClass (encodeCentralRestricted022Word w r) = w.1.1 r := by
  by_cases h0 : w.1.1 r = 0
  · simp [encodeCentralRestricted022Word, channelClass, h0]
  by_cases h1 : w.1.1 r = 1
  · simp [encodeCentralRestricted022Word, channelClass, h1]
  have h2 : w.1.1 r = 2 := by
    apply Fin.ext
    omega
  simp [encodeCentralRestricted022Word, channelClass, h2]

private noncomputable def fromCentral {q N L G : ℕ}
    (w : CentralRestricted022Word q N L G) : SymmetricWord.{u} q N L G := by
  refine ⟨PowIndex.ofFun N
    (fun r ↦ ULift.up (gradeLetterEquiv q (encodeCentralRestricted022Word w r))), ?_⟩
  intro a
  simpa only [PowIndex.get_ofFun, LiftedCoarsePair.leftGrade,
    gradeLetterEquiv_grade, class_encode] using w.1.2 a

private theorem decoded_fromCentral {q N L G : ℕ}
    (w : CentralRestricted022Word q N L G) :
    decodedWord q N (fromCentral.{u} w).1 = encodeCentralRestricted022Word w := by
  funext r
  simp [decodedWord, fromCentral, PowIndex.get_ofFun]

private noncomputable def canonicalWordEquiv (q N L G : ℕ) :
    SymmetricWord.{u} q N L G ≃ CentralRestricted022Word q N L G where
  toFun := toCentral
  invFun := fromCentral
  left_inv w := by
    apply Subtype.ext
    apply (PowIndex.equivFun (LiftedCoarsePair.{u} q 2) N).injective
    funext r
    apply ULift.ext
    apply (gradeLetterEquiv q).symm.injective
    have h := congrFun (decoded_fromCentral (toCentral w)) r
    rw [encode_toCentral] at h
    exact h
  right_inv w := by
    apply encodeCentralRestricted022Word_injective
    rw [encode_toCentral, decoded_fromCentral]

private def splitWordCount (m L : ℕ) : ℕ := Nat.choose m L * Nat.choose (m - L) L

/-- Cardinality of the literal fine-Z word type.  This is exactly the source
multinomial times the `q^2` choices at every middle position. -/
private theorem centralWord_card
    (q m L G : ℕ) (hcount : 2 * L + G = m) :
    Nat.card (CentralRestricted022Word q m L G) = splitWordCount m L * q ^ (2 * G) := by
  have hsum : ∑ c : Fin 3, centralSplitMultiplicity L G c = m := by
    simp [centralSplitMultiplicity, Fin.sum_univ_succ]
    omega
  let patternPredicate : (Fin m → Fin 3) → Prop := fun g ↦
    ∀ i, Fintype.card {a : Fin m // g a = i} = centralSplitMultiplicity L G i
  letI patternDecidable : DecidablePred patternPredicate := fun _ ↦
    Fintype.decidableForallFintype
  letI patternFintype : Fintype {g : Fin m → Fin 3 // patternPredicate g} :=
    Subtype.fintype patternPredicate
  have hpattern0 :=
    mme_fintype_prescribed_fiber_function_card
      (α := Fin m) (ι := Fin 3) (centralSplitMultiplicity L G) (by simpa using hsum)
  have hpatternNat0 :
      Nat.card
          {g : Fin m → Fin 3 // ∀ i,
            Fintype.card {a : Fin m // g a = i} = centralSplitMultiplicity L G i} =
        m.factorial / ∏ i, (centralSplitMultiplicity L G i).factorial := by
    calc
      Nat.card
          {g : Fin m → Fin 3 // ∀ i,
            Fintype.card {a : Fin m // g a = i} = centralSplitMultiplicity L G i} =
          Fintype.card
            {g : Fin m → Fin 3 // ∀ i,
              Fintype.card {a : Fin m // g a = i} = centralSplitMultiplicity L G i} :=
        Nat.card_eq_fintype_card
      _ = m.factorial / ∏ i, (centralSplitMultiplicity L G i).factorial := by
        simpa using hpattern0
  have hpattern :
      Nat.card (CentralSplitPattern m L G) =
        m.factorial / (L.factorial * G.factorial * L.factorial) := by
    simpa [CentralSplitPattern, centralSplitMultiplicity, Fin.prod_univ_succ, Nat.mul_assoc]
      using hpatternNat0
  have hLm : L ≤ m := by omega
  have hLrem : L ≤ m - L := by omega
  have hfirst := Nat.choose_mul_factorial_mul_factorial hLm
  have hsecond := Nat.choose_mul_factorial_mul_factorial hLrem
  rw [show m - L - L = G by omega] at hsecond
  have hfactorial :
      (L.factorial * G.factorial * L.factorial) * splitWordCount m L =
        m.factorial := by
    rw [splitWordCount]
    calc
      (L.factorial * G.factorial * L.factorial) *
            (Nat.choose m L * Nat.choose (m - L) L) =
          Nat.choose m L * L.factorial *
            (Nat.choose (m - L) L * L.factorial * G.factorial) := by ring
      _ = Nat.choose m L * L.factorial * (m - L).factorial := by rw [hsecond]
      _ = m.factorial := hfirst
  have hmultinomial :
      m.factorial / (L.factorial * G.factorial * L.factorial) =
        splitWordCount m L := by
    symm
    exact Nat.eq_div_of_mul_eq_right (by positivity) hfactorial
  have hmiddle (p : CentralSplitPattern m L G) :
      Nat.card ({r : Fin m // p.1 r = (1 : Fin 3)} → Fin q × Fin q) =
        q ^ (2 * G) := by
    have hp := p.2 (1 : Fin 3)
    simp [centralSplitMultiplicity] at hp
    have hpNat : Nat.card {r : Fin m // p.1 r = (1 : Fin 3)} = G := by
      rw [Nat.card_eq_fintype_card]
      exact hp
    rw [Nat.card_fun, Nat.card_prod, hpNat]
    simp only [Nat.card_fin]
    rw [show q * q = q ^ 2 by ring]
    rw [← pow_mul]
  letI : Fintype (CentralSplitPattern m L G) := patternFintype
  unfold CentralRestricted022Word
  rw [Nat.card_sigma]
  simp_rw [hmiddle]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hpattern, hmultinomial]

  rfl


theorem solution
    (q : ℕ) (p : IntegerZSplitProfile 3)
    (houter : p.count 0 = p.count 2) (m : ℕ) :
    Nat.card {w : PowIndex (LiftedCoarsePair.{u} q 2) (p.length m) //
      prescribedZWord LiftedCoarsePair.leftGrade p m w} =
      Nat.choose (p.length m) (p.count 0 * m) *
        Nat.choose (p.length m - p.count 0 * m) (p.count 0 * m) *
          q ^ (2 * (p.count 1 * m)) := by
  have hcounts (a : Fin 3) :
      p.count a * m = centralSplitMultiplicity (p.count 0 * m) (p.count 1 * m) a := by
    fin_cases a <;> simp [centralSplitMultiplicity, houter]
  have hcount : 2 * (p.count 0 * m) + p.count 1 * m = p.length m := by
    have hp' : p.count 0 + p.count 1 + p.count 2 = p.denominator := by
      simpa only [Fin.sum_univ_succ, Nat.add_zero, Nat.add_assoc] using p.count_sum
    unfold IntegerZSplitProfile.length
    rw [← hp', ← houter]
    ring
  have heq (w : PowIndex (LiftedCoarsePair.{u} q 2) (p.length m)) :
      prescribedZWord LiftedCoarsePair.leftGrade p m w ↔
        ∀ a : Fin 3,
          Fintype.card {r : Fin (p.length m) //
            (PowIndex.get (p.length m) w r).leftGrade = a} =
              centralSplitMultiplicity (p.count 0 * m) (p.count 1 * m) a := by
    simp only [prescribedZWord, leftGradeCount, Fintype.card_subtype]
    apply forall_congr'
    intro a
    rw [hcounts a]
  let e :=
    (Equiv.subtypeEquivRight heq).trans
      (canonicalWordEquiv.{u} q (p.length m) (p.count 0 * m) (p.count 1 * m))
  rw [Nat.card_congr e, centralWord_card q _ _ _ hcount]
  rfl
