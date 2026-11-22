-- Prove2me | Definitions.Def_Kourovka_Computability_ComputableWords
-- name    : Kourovka_Computability_ComputableWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:41:25.512001+00:00
-- url     : https://prove2.me/theorems/e47b38ec-1c10-47e9-a184-3eb46411855a
-- title:
--   Computable Words
-- statement:
--   Definitions and structural lemmas for Computable Words, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableWords.lean

import Definitions.Def_Kourovka_Certificates_WordCertificates
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ComputableWords
variable {α : Type*} [Primcodable α] [DecidableEq α]
def reduceStep (letter : α × Bool) (word : List (α × Bool)) : List (α × Bool) :=
  List.casesOn word [letter] fun head tail =>
    if letter.1 = head.1 ∧ letter.2 = !head.2 then tail else letter :: head :: tail
theorem reduceStep_primrec : Primrec₂ (@reduceStep α _) := by
  let hnil : Primrec (fun p : (α × Bool) × List (α × Bool) => [p.1]) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.const [])
  have hcond : PrimrecPred (fun p : ((α × Bool) × List (α × Bool)) ×
      ((α × Bool) × List (α × Bool)) =>
      p.1.1.1 = p.2.1.1 ∧ p.1.1.2 = !p.2.1.2) :=
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).and
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.not.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  have hbody : Primrec₂ (fun p : (α × Bool) × List (α × Bool) =>
      fun q : (α × Bool) × List (α × Bool) =>
      if p.1.1 = q.1.1 ∧ p.1.2 = !q.1.2 then q.2 else p.1 :: q.1 :: q.2) :=
    (Primrec.ite hcond (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)))).to₂
  exact Primrec.list_casesOn Primrec.snd hnil hbody
omit [Primcodable α] in
theorem reduce_eq_foldr (word : List (α × Bool)) :
    FreeGroup.reduce word = word.foldr reduceStep [] := by
  induction word with
  | nil => rfl
  | cons letter word ih => rw [FreeGroup.reduce.cons, List.foldr_cons, ← ih]; rfl
theorem reduce_primrec : Primrec (@FreeGroup.reduce α _) := by
  have h := Primrec.list_foldr (Primrec.id (α := List (α × Bool))) (Primrec.const [])
    ((reduceStep_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq (fun w => (reduce_eq_foldr w).symm)
def wordEq (left right : List (α × Bool)) : Bool :=
  decide (FreeGroup.reduce left = FreeGroup.reduce right)
abbrev ReducedWord (α : Type*) [DecidableEq α] :=
  {w : List (α × Bool) // FreeGroup.reduce w = w}
theorem reduced_primrec : PrimrecPred (fun w : List (α × Bool) => FreeGroup.reduce w = w) :=
  Primrec.eq.comp reduce_primrec Primrec.id
instance reducedWordPrimcodable : Primcodable (ReducedWord α) :=
  Primcodable.subtype reduced_primrec
def reducedWordEquiv : FreeGroup α ≃ ReducedWord α where
  toFun g := ⟨g.toWord, FreeGroup.reduce_toWord g⟩
  invFun w := FreeGroup.mk w.1
  left_inv _ := FreeGroup.mk_toWord
  right_inv w := Subtype.ext (by exact w.2)
instance freeGroupPrimcodable : Primcodable (FreeGroup α) :=
  Primcodable.ofEquiv (ReducedWord α) reducedWordEquiv
end Kourovka.MetabelianEnumeration.ComputableWords


