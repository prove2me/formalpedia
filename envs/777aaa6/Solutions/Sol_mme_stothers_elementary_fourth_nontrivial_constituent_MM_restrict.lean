-- Prove2me | solution 1 for mme_stothers_elementary_fourth_nontrivial_constituent_MM_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:34:15.470065+00:00
-- url     : https://prove2.me/submissions/b4f4c3b4-f32f-48a3-874f-8348872845ab

import Theorems.Thm_mme_CW_fourth_boundary_literal_code_restrict
import Definitions.Def_mme_CW_boundary_literal_codes
import Mathlib.Tactic

open MME MME.StothersFourth BigOperators

universe u

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

namespace MME.StothersFourth.ExplicitBoundaryCodes

private def liftEmbedding {A B : Type} (e : A ↪ B) : ULift.{u} A ↪ B :=
  ⟨fun x => e x.down, by
    intro x y hxy
    apply ULift.ext
    exact e.injective hxy⟩

private def boundaryKind {q : ℕ} : CWBoundaryLetter q → Fin 3
  | Sum.inl _ => 1
  | Sum.inr ⟨0, _⟩ => 0
  | Sum.inr ⟨1, _⟩ => 2

private def kindLetter {q : ℕ} (k : Fin 3) : CWBoundaryLetter q :=
  if k = 2 then Sum.inr 1 else Sum.inr 0

private theorem boundaryKind_kindLetter
    {q : ℕ} (k : Fin 3) (hk : k ≠ 1) :
    boundaryKind (kindLetter (q := q) k) = k := by
  fin_cases k <;> simp [kindLetter, boundaryKind] at hk ⊢

private theorem boundaryWeight_kindLetter
    {q : ℕ} (k : Fin 3) (hk : k ≠ 1) :
    cwBoundaryWeight (kindLetter (q := q) k) = k.val := by
  fin_cases k <;> simp [kindLetter, cwBoundaryWeight] at hk ⊢

private def patternWord (q n k : ℕ)
    (kind : Fin n → Fin 4 → Fin 3)
    (slot : Fin n → Fin 4 → Fin k)
    (x : Fin n × (Fin k → Fin q)) : Fin 4 → CWBoundaryLetter q :=
  fun r => if kind x.1 r = 1 then Sum.inl (x.2 (slot x.1 r))
    else kindLetter (kind x.1 r)

private theorem boundaryKind_patternWord
    (q n k : ℕ) (kind : Fin n → Fin 4 → Fin 3)
    (slot : Fin n → Fin 4 → Fin k)
    (x : Fin n × (Fin k → Fin q)) (r : Fin 4) :
    boundaryKind (patternWord q n k kind slot x r) = kind x.1 r := by
  simp only [patternWord]
  split_ifs with h
  · simpa [boundaryKind] using h.symm
  · exact boundaryKind_kindLetter (kind x.1 r) h

private theorem patternWord_injective
    (q n k : ℕ)
    (kind : Fin n → Fin 4 → Fin 3)
    (slot : Fin n → Fin 4 → Fin k)
    (pos : Fin n → Fin k → Fin 4)
    (hkind : Function.Injective kind)
    (hposKind : ∀ t s, kind t (pos t s) = 1)
    (hposSlot : ∀ t s, slot t (pos t s) = s) :
    Function.Injective (patternWord q n k kind slot) := by
  intro x y hxy
  have hkindxy : kind x.1 = kind y.1 := by
    funext r
    rw [← boundaryKind_patternWord q n k kind slot x r,
      ← boundaryKind_patternWord q n k kind slot y r, hxy]
  have htag : x.1 = y.1 := hkind hkindxy
  rcases x with ⟨tx, lx⟩
  rcases y with ⟨ty, ly⟩
  dsimp at htag
  subst ty
  congr 1
  funext s
  have hw := congrFun hxy (pos tx s)
  change (if kind tx (pos tx s) = 1 then
      Sum.inl (lx (slot tx (pos tx s))) else
      kindLetter (kind tx (pos tx s))) =
    (if kind tx (pos tx s) = 1 then
      Sum.inl (ly (slot tx (pos tx s))) else
      kindLetter (kind tx (pos tx s))) at hw
  rw [if_pos (hposKind tx s), if_pos (hposKind tx s),
    hposSlot tx s] at hw
  exact Sum.inl.inj hw

private def noSlotWord (q n : ℕ)
    (kind : Fin n → Fin 4 → Fin 3) (t : Fin n) :
    Fin 4 → CWBoundaryLetter q :=
  fun r => kindLetter (kind t r)

private theorem boundaryKind_noSlotWord
    (q n : ℕ) (kind : Fin n → Fin 4 → Fin 3)
    (t : Fin n) (r : Fin 4)
    (hnoOne : kind t r ≠ 1) :
    boundaryKind (noSlotWord q n kind t r) = kind t r := by
  exact boundaryKind_kindLetter (kind t r) hnoOne

private theorem noSlotWord_injective
    (q n : ℕ) (kind : Fin n → Fin 4 → Fin 3)
    (hkind : Function.Injective kind)
    (hnoOne : ∀ t r, kind t r ≠ 1) :
    Function.Injective (noSlotWord q n kind) := by
  intro t t' htt
  apply hkind
  funext r
  rw [← boundaryKind_noSlotWord q n kind t r (hnoOne t r),
    ← boundaryKind_noSlotWord q n kind t' r (hnoOne t' r), htt]

private theorem patternKind_eq_of_word_eq
    (q n k n' k' : ℕ)
    (kind : Fin n → Fin 4 → Fin 3)
    (slot : Fin n → Fin 4 → Fin k)
    (kind' : Fin n' → Fin 4 → Fin 3)
    (slot' : Fin n' → Fin 4 → Fin k')
    (x : Fin n × (Fin k → Fin q))
    (y : Fin n' × (Fin k' → Fin q))
    (hxy : patternWord q n k kind slot x =
      patternWord q n' k' kind' slot' y) :
    kind x.1 = kind' y.1 := by
  funext r
  calc
    kind x.1 r = boundaryKind (patternWord q n k kind slot x r) :=
      (boundaryKind_patternWord q n k kind slot x r).symm
    _ = boundaryKind (patternWord q n' k' kind' slot' y r) :=
      congrArg boundaryKind (congrFun hxy r)
    _ = kind' y.1 r :=
      boundaryKind_patternWord q n' k' kind' slot' y r

private theorem patternNoSlotKind_eq_of_word_eq
    (q n k n' : ℕ)
    (kind : Fin n → Fin 4 → Fin 3)
    (slot : Fin n → Fin 4 → Fin k)
    (kind' : Fin n' → Fin 4 → Fin 3)
    (hnoOne : ∀ t r, kind' t r ≠ 1)
    (x : Fin n × (Fin k → Fin q)) (y : Fin n')
    (hxy : patternWord q n k kind slot x = noSlotWord q n' kind' y) :
    kind x.1 = kind' y := by
  funext r
  calc
    kind x.1 r = boundaryKind (patternWord q n k kind slot x r) :=
      (boundaryKind_patternWord q n k kind slot x r).symm
    _ = boundaryKind (noSlotWord q n' kind' y r) :=
      congrArg boundaryKind (congrFun hxy r)
    _ = kind' y r := boundaryKind_noSlotWord q n' kind' y r (hnoOne y r)

/-! ## Constant pattern tables -/

private def oneKind : Fin 4 → Fin 4 → Fin 3 :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

private def oneSlot : Fin 4 → Fin 4 → Fin 1 := fun _ _ => 0
private def onePos : Fin 4 → Fin 1 → Fin 4 := fun t _ => t

private theorem oneKind_injective : Function.Injective oneKind := by decide
private theorem onePos_kind : ∀ t s, oneKind t (onePos t s) = 1 := by decide
private theorem onePos_slot : ∀ t s, oneSlot t (onePos t s) = s := by decide

private def pairKind : Fin 6 → Fin 4 → Fin 3 :=
  ![![1, 1, 0, 0], ![1, 0, 1, 0], ![1, 0, 0, 1],
    ![0, 1, 1, 0], ![0, 1, 0, 1], ![0, 0, 1, 1]]

private def pairSlot : Fin 6 → Fin 4 → Fin 2 :=
  ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1],
    ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 1]]

private def pairPos : Fin 6 → Fin 2 → Fin 4 :=
  ![![0, 1], ![0, 2], ![0, 3], ![1, 2], ![1, 3], ![2, 3]]

private theorem pairKind_injective : Function.Injective pairKind := by decide
private theorem pairPos_kind : ∀ t s, pairKind t (pairPos t s) = 1 := by decide
private theorem pairPos_slot : ∀ t s, pairSlot t (pairPos t s) = s := by decide

private def singleCKind : Fin 4 → Fin 4 → Fin 3 :=
  ![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]]

private theorem singleCKind_injective : Function.Injective singleCKind := by decide
private theorem singleCKind_noOne : ∀ t r, singleCKind t r ≠ 1 := by decide
private theorem pair_singleC_disjoint : ∀ p c, pairKind p ≠ singleCKind c := by decide

private def tripleKind : Fin 4 → Fin 4 → Fin 3 :=
  ![![0, 1, 1, 1], ![1, 0, 1, 1], ![1, 1, 0, 1], ![1, 1, 1, 0]]

private def tripleSlot : Fin 4 → Fin 4 → Fin 3 :=
  ![![0, 0, 1, 2], ![0, 0, 1, 2], ![0, 1, 0, 2], ![0, 1, 2, 0]]

private def triplePos : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

private theorem tripleKind_injective : Function.Injective tripleKind := by decide
private theorem triplePos_kind : ∀ t s, tripleKind t (triplePos t s) = 1 := by decide
private theorem triplePos_slot : ∀ t s, tripleSlot t (triplePos t s) = s := by decide

/-- Ordered patterns having one `C`, one middle letter, and two `B`s. -/
private def caKind : Fin 12 → Fin 4 → Fin 3 :=
  ![![2, 1, 0, 0], ![2, 0, 1, 0], ![2, 0, 0, 1],
    ![1, 2, 0, 0], ![0, 2, 1, 0], ![0, 2, 0, 1],
    ![1, 0, 2, 0], ![0, 1, 2, 0], ![0, 0, 2, 1],
    ![1, 0, 0, 2], ![0, 1, 0, 2], ![0, 0, 1, 2]]

private def caSlot : Fin 12 → Fin 4 → Fin 1 := fun _ _ => 0
private def caPos : Fin 12 → Fin 1 → Fin 4 :=
  ![![1], ![2], ![3], ![0], ![2], ![3], ![0], ![1], ![3], ![0], ![1], ![2]]

private theorem caKind_injective : Function.Injective caKind := by decide
private theorem caPos_kind : ∀ t s, caKind t (caPos t s) = 1 := by decide
private theorem caPos_slot : ∀ t s, caSlot t (caPos t s) = s := by decide
private theorem triple_ca_disjoint : ∀ t c, tripleKind t ≠ caKind c := by decide

private def allAKind : Fin 1 → Fin 4 → Fin 3 := fun _ _ => 1
private def allASlot : Fin 1 → Fin 4 → Fin 4 := fun _ r => r
private def allAPos : Fin 1 → Fin 4 → Fin 4 := fun _ r => r

private theorem allAKind_injective : Function.Injective allAKind := by
  intro a b _
  exact Subsingleton.elim a b
private theorem allAPos_kind : ∀ t s, allAKind t (allAPos t s) = 1 := by decide
private theorem allAPos_slot : ∀ t s, allASlot t (allAPos t s) = s := by decide

/-- Ordered patterns having one `C`, one `B`, and two middle letters. -/
private def caaKind : Fin 12 → Fin 4 → Fin 3 :=
  ![![2, 0, 1, 1], ![2, 1, 0, 1], ![2, 1, 1, 0],
    ![0, 2, 1, 1], ![1, 2, 0, 1], ![1, 2, 1, 0],
    ![0, 1, 2, 1], ![1, 0, 2, 1], ![1, 1, 2, 0],
    ![0, 1, 1, 2], ![1, 0, 1, 2], ![1, 1, 0, 2]]

private def caaSlot : Fin 12 → Fin 4 → Fin 2 :=
  ![![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 1, 0],
    ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 1, 0],
    ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 1, 0, 0],
    ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 1, 0, 0]]

private def caaPos : Fin 12 → Fin 2 → Fin 4 :=
  ![![2, 3], ![1, 3], ![1, 2], ![2, 3], ![0, 3], ![0, 2],
    ![1, 3], ![0, 3], ![0, 1], ![1, 2], ![0, 2], ![0, 1]]

private theorem caaKind_injective : Function.Injective caaKind := by decide
private theorem caaPos_kind : ∀ t s, caaKind t (caaPos t s) = 1 := by decide
private theorem caaPos_slot : ∀ t s, caaSlot t (caaPos t s) = s := by decide

private def doubleCKind : Fin 6 → Fin 4 → Fin 3 :=
  ![![2, 2, 0, 0], ![2, 0, 2, 0], ![2, 0, 0, 2],
    ![0, 2, 2, 0], ![0, 2, 0, 2], ![0, 0, 2, 2]]

private theorem doubleCKind_injective : Function.Injective doubleCKind := by decide
private theorem doubleCKind_noOne : ∀ t r, doubleCKind t r ≠ 1 := by decide
private theorem allA_caa_disjoint : ∀ t c, allAKind t ≠ caaKind c := by decide
private theorem allA_doubleC_disjoint : ∀ t c, allAKind t ≠ doubleCKind c := by decide
private theorem caa_doubleC_disjoint : ∀ t c, caaKind t ≠ doubleCKind c := by decide

/-! ## The four finite codes -/

private abbrev Code1 (q : ℕ) := Fin 4 × (Fin 1 → Fin q)
private abbrev Code2 (q : ℕ) :=
  (Fin 6 × (Fin 2 → Fin q)) ⊕ Fin 4
private abbrev Code3 (q : ℕ) :=
  (Fin 4 × (Fin 3 → Fin q)) ⊕ (Fin 12 × (Fin 1 → Fin q))
private abbrev Code4 (q : ℕ) :=
  ((Fin 1 × (Fin 4 → Fin q)) ⊕ (Fin 12 × (Fin 2 → Fin q))) ⊕ Fin 6

private def code1Enc (q : ℕ) : Code1 q ↪ (Fin 4 → CWBoundaryLetter q) :=
  ⟨patternWord q 4 1 oneKind oneSlot,
    patternWord_injective q 4 1 oneKind oneSlot onePos
      oneKind_injective onePos_kind onePos_slot⟩

private def code2Word (q : ℕ) : Code2 q → Fin 4 → CWBoundaryLetter q
  | Sum.inl x => patternWord q 6 2 pairKind pairSlot x
  | Sum.inr t => noSlotWord q 4 singleCKind t

private theorem code2Word_injective (q : ℕ) : Function.Injective (code2Word q) := by
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y
  · congr 1
    exact patternWord_injective q 6 2 pairKind pairSlot pairPos
      pairKind_injective pairPos_kind pairPos_slot hxy
  · exfalso
    apply pair_singleC_disjoint x.1 y
    change patternWord q 6 2 pairKind pairSlot x =
      noSlotWord q 4 singleCKind y at hxy
    exact patternNoSlotKind_eq_of_word_eq q 6 2 4 pairKind pairSlot
      singleCKind singleCKind_noOne x y hxy
  · exfalso
    apply pair_singleC_disjoint y.1 x
    change noSlotWord q 4 singleCKind x =
      patternWord q 6 2 pairKind pairSlot y at hxy
    exact patternNoSlotKind_eq_of_word_eq q 6 2 4 pairKind pairSlot
      singleCKind singleCKind_noOne y x hxy.symm
  · congr 1
    exact noSlotWord_injective q 4 singleCKind
      singleCKind_injective singleCKind_noOne hxy

private def code2Enc (q : ℕ) : Code2 q ↪ (Fin 4 → CWBoundaryLetter q) :=
  ⟨code2Word q, code2Word_injective q⟩

private def code3Word (q : ℕ) : Code3 q → Fin 4 → CWBoundaryLetter q
  | Sum.inl x => patternWord q 4 3 tripleKind tripleSlot x
  | Sum.inr x => patternWord q 12 1 caKind caSlot x

private theorem code3Word_injective (q : ℕ) : Function.Injective (code3Word q) := by
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y
  · congr 1
    exact patternWord_injective q 4 3 tripleKind tripleSlot triplePos
      tripleKind_injective triplePos_kind triplePos_slot hxy
  · exfalso
    apply triple_ca_disjoint x.1 y.1
    change patternWord q 4 3 tripleKind tripleSlot x =
      patternWord q 12 1 caKind caSlot y at hxy
    exact patternKind_eq_of_word_eq q 4 3 12 1 tripleKind tripleSlot
      caKind caSlot x y hxy
  · exfalso
    apply triple_ca_disjoint y.1 x.1
    change patternWord q 12 1 caKind caSlot x =
      patternWord q 4 3 tripleKind tripleSlot y at hxy
    exact patternKind_eq_of_word_eq q 4 3 12 1 tripleKind tripleSlot
      caKind caSlot y x hxy.symm
  · congr 1
    exact patternWord_injective q 12 1 caKind caSlot caPos
      caKind_injective caPos_kind caPos_slot hxy

private def code3Enc (q : ℕ) : Code3 q ↪ (Fin 4 → CWBoundaryLetter q) :=
  ⟨code3Word q, code3Word_injective q⟩

private def code4Word (q : ℕ) : Code4 q → Fin 4 → CWBoundaryLetter q
  | Sum.inl (Sum.inl x) => patternWord q 1 4 allAKind allASlot x
  | Sum.inl (Sum.inr x) => patternWord q 12 2 caaKind caaSlot x
  | Sum.inr t => noSlotWord q 6 doubleCKind t

private theorem code4Word_injective (q : ℕ) : Function.Injective (code4Word q) := by
  intro x y hxy
  rcases x with (x | x) | x <;> rcases y with (y | y) | y
  · congr 2
    exact patternWord_injective q 1 4 allAKind allASlot allAPos
      allAKind_injective allAPos_kind allAPos_slot hxy
  · exfalso
    apply allA_caa_disjoint x.1 y.1
    change patternWord q 1 4 allAKind allASlot x =
      patternWord q 12 2 caaKind caaSlot y at hxy
    exact patternKind_eq_of_word_eq q 1 4 12 2 allAKind allASlot
      caaKind caaSlot x y hxy
  · exfalso
    apply allA_doubleC_disjoint x.1 y
    change patternWord q 1 4 allAKind allASlot x =
      noSlotWord q 6 doubleCKind y at hxy
    exact patternNoSlotKind_eq_of_word_eq q 1 4 6 allAKind allASlot
      doubleCKind doubleCKind_noOne x y hxy
  · exfalso
    apply allA_caa_disjoint y.1 x.1
    change patternWord q 12 2 caaKind caaSlot x =
      patternWord q 1 4 allAKind allASlot y at hxy
    exact patternKind_eq_of_word_eq q 1 4 12 2 allAKind allASlot
      caaKind caaSlot y x hxy.symm
  · congr 2
    exact patternWord_injective q 12 2 caaKind caaSlot caaPos
      caaKind_injective caaPos_kind caaPos_slot hxy
  · exfalso
    apply caa_doubleC_disjoint x.1 y
    change patternWord q 12 2 caaKind caaSlot x =
      noSlotWord q 6 doubleCKind y at hxy
    exact patternNoSlotKind_eq_of_word_eq q 12 2 6 caaKind caaSlot
      doubleCKind doubleCKind_noOne x y hxy
  · exfalso
    apply allA_doubleC_disjoint y.1 x
    change noSlotWord q 6 doubleCKind x =
      patternWord q 1 4 allAKind allASlot y at hxy
    exact patternNoSlotKind_eq_of_word_eq q 1 4 6 allAKind allASlot
      doubleCKind doubleCKind_noOne y x hxy.symm
  · exfalso
    apply caa_doubleC_disjoint y.1 x
    change noSlotWord q 6 doubleCKind x =
      patternWord q 12 2 caaKind caaSlot y at hxy
    exact patternNoSlotKind_eq_of_word_eq q 12 2 6 caaKind caaSlot
      doubleCKind doubleCKind_noOne y x hxy.symm
  · congr 1
    exact noSlotWord_injective q 6 doubleCKind
      doubleCKind_injective doubleCKind_noOne hxy

private def code4Enc (q : ℕ) : Code4 q ↪ (Fin 4 → CWBoundaryLetter q) :=
  ⟨code4Word q, code4Word_injective q⟩

private theorem patternWord_weight
    (q n k w : ℕ)
    (kind : Fin n → Fin 4 → Fin 3)
    (slot : Fin n → Fin 4 → Fin k)
    (hweight : ∀ t, ∑ r, (kind t r).val = w)
    (x : Fin n × (Fin k → Fin q)) :
    cwBoundaryWordWeight (patternWord q n k kind slot x) = w := by
  rw [cwBoundaryWordWeight]
  have hpoint : ∀ r, cwBoundaryWeight (patternWord q n k kind slot x r) =
      (kind x.1 r).val := by
    intro r
    simp only [patternWord]
    split_ifs with h
    · simpa [cwBoundaryWeight] using congrArg Fin.val h.symm
    · exact boundaryWeight_kindLetter (kind x.1 r) h
  simp_rw [hpoint]
  exact hweight x.1

private theorem noSlotWord_weight
    (q n w : ℕ) (kind : Fin n → Fin 4 → Fin 3)
    (hnoOne : ∀ t r, kind t r ≠ 1)
    (hweight : ∀ t, ∑ r, (kind t r).val = w)
    (t : Fin n) : cwBoundaryWordWeight (noSlotWord q n kind t) = w := by
  rw [cwBoundaryWordWeight]
  have hpoint : ∀ r, cwBoundaryWeight (noSlotWord q n kind t r) =
      (kind t r).val := by
    intro r
    exact boundaryWeight_kindLetter (kind t r) (hnoOne t r)
  simp_rw [hpoint]
  exact hweight t

private theorem oneKind_weight : ∀ t, ∑ r, (oneKind t r).val = 1 := by decide
private theorem pairKind_weight : ∀ t, ∑ r, (pairKind t r).val = 2 := by decide
private theorem singleCKind_weight : ∀ t, ∑ r, (singleCKind t r).val = 2 := by decide
private theorem tripleKind_weight : ∀ t, ∑ r, (tripleKind t r).val = 3 := by decide
private theorem caKind_weight : ∀ t, ∑ r, (caKind t r).val = 3 := by decide
private theorem allAKind_weight : ∀ t, ∑ r, (allAKind t r).val = 4 := by decide
private theorem caaKind_weight : ∀ t, ∑ r, (caaKind t r).val = 4 := by decide
private theorem doubleCKind_weight : ∀ t, ∑ r, (doubleCKind t r).val = 4 := by decide

private theorem code1_weight (q : ℕ) (x : Code1 q) :
    cwBoundaryWordWeight (code1Enc q x) = 1 :=
  patternWord_weight q 4 1 1 oneKind oneSlot oneKind_weight x

private theorem code2_weight (q : ℕ) (x : Code2 q) :
    cwBoundaryWordWeight (code2Enc q x) = 2 := by
  rcases x with x | x
  · exact patternWord_weight q 6 2 2 pairKind pairSlot pairKind_weight x
  · exact noSlotWord_weight q 4 2 singleCKind singleCKind_noOne
      singleCKind_weight x

private theorem code3_weight (q : ℕ) (x : Code3 q) :
    cwBoundaryWordWeight (code3Enc q x) = 3 := by
  rcases x with x | x
  · exact patternWord_weight q 4 3 3 tripleKind tripleSlot tripleKind_weight x
  · exact patternWord_weight q 12 1 3 caKind caSlot caKind_weight x

private theorem code4_weight (q : ℕ) (x : Code4 q) :
    cwBoundaryWordWeight (code4Enc q x) = 4 := by
  rcases x with (x | x) | x
  · exact patternWord_weight q 1 4 4 allAKind allASlot allAKind_weight x
  · exact patternWord_weight q 12 2 4 caaKind caaSlot caaKind_weight x
  · exact noSlotWord_weight q 6 4 doubleCKind doubleCKind_noOne
      doubleCKind_weight x

private theorem code1_card (q : ℕ) : Fintype.card (Code1 q) = 4 * q := by
  simp

private theorem code2_card (q : ℕ) :
    Fintype.card (Code2 q) = 6 * q ^ 2 + 4 := by
  simp

private theorem code3_card (q : ℕ) :
    Fintype.card (Code3 q) = 4 * q * (q ^ 2 + 3) := by
  simp
  ring

private theorem code4_card (q : ℕ) :
    Fintype.card (Code4 q) = q ^ 4 + 12 * q ^ 2 + 6 := by
  simp

end MME.StothersFourth.ExplicitBoundaryCodes

open MME.StothersFourth.ExplicitBoundaryCodes

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 (4 * q))
        (MME.StothersFourth.cwFourthConstituent K q 0 1 7) ∧
    TensorObj.Restrict (MMObj K 1 1 (6 * q ^ 2 + 4))
        (MME.StothersFourth.cwFourthConstituent K q 0 2 6) ∧
    TensorObj.Restrict (MMObj K 1 1 (4 * q * (q ^ 2 + 3)))
        (MME.StothersFourth.cwFourthConstituent K q 0 3 5) ∧
    TensorObj.Restrict (MMObj K 1 1
        (q ^ 4 + 12 * q ^ 2 + 6))
      (MME.StothersFourth.cwFourthConstituent K q 0 4 4) := by
  have h1 := mme_CW_fourth_boundary_literal_code_restrict
    (K := K) (C := ULift.{u} (Code1 q)) q
      (liftEmbedding (code1Enc q)) (1 : Fin 9)
      (fun x => code1_weight q x.down)
  have h2 := mme_CW_fourth_boundary_literal_code_restrict
    (K := K) (C := ULift.{u} (Code2 q)) q
      (liftEmbedding (code2Enc q)) (2 : Fin 9)
      (fun x => code2_weight q x.down)
  have h3 := mme_CW_fourth_boundary_literal_code_restrict
    (K := K) (C := ULift.{u} (Code3 q)) q
      (liftEmbedding (code3Enc q)) (3 : Fin 9)
      (fun x => code3_weight q x.down)
  have h4 := mme_CW_fourth_boundary_literal_code_restrict
    (K := K) (C := ULift.{u} (Code4 q)) q
      (liftEmbedding (code4Enc q)) (4 : Fin 9)
      (fun x => code4_weight q x.down)
  rw [Fintype.card_ulift, code1_card] at h1
  rw [Fintype.card_ulift, code2_card] at h2
  rw [Fintype.card_ulift, code3_card] at h3
  rw [Fintype.card_ulift, code4_card] at h4
  exact ⟨h1, h2, h3, h4⟩
