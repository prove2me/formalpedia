-- Prove2me | solution 1 for BerggrenZeta.blocks_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T19:38:43.331596+00:00
-- url     : https://prove2.me/submissions/46080a2e-19b9-4ad7-bf0d-371d83603a3f

import Mathlib
import Definitions.Def_Novelty_BerggrenTreeHyperbolicSubtree
import Definitions.Def_Novelty_BerggrenTreeSilverGrowth

open BerggrenZeta

private lemma blockList_length (b : Bool) : (blockList b).length = 2 := by
  cases b <;> simp [blockList]

private lemma blocks_length (bs : List Bool) : (blocks bs).length = 2 * bs.length := by
  induction bs with
  | nil => simp [blocks]
  | cons b bs ih =>
      simp [blocks, List.length_append, blockList_length, ih]
      ring

private def decodeHead : List (Fin 3) → Option Bool
  | (⟨1, _⟩ : Fin 3) :: (⟨1, _⟩ : Fin 3) :: _ => some true
  | (⟨1, _⟩ : Fin 3) :: (⟨2, _⟩ : Fin 3) :: _ => some false
  | _ => none

private lemma decodeHead_blockList (b : Bool) (tail : List (Fin 3)) :
    decodeHead (blockList b ++ tail) = some b := by
  cases b <;> simp [decodeHead, blockList]

theorem solution : Function.Injective blocks := by
  intro a b h
  induction a generalizing b with
  | nil =>
      have hlen : (blocks b).length = 0 := by
        simpa [blocks] using congrArg List.length h.symm
      have : b.length = 0 := by
        have := blocks_length b
        omega
      cases b with
      | nil => rfl
      | cons _ _ => cases this
  | cons x xs ih =>
      cases b with
      | nil =>
          have hlen : (blocks (x :: xs)).length = 0 := by
            simpa [blocks] using congrArg List.length h
          have : (x :: xs).length = 0 := by
            have := blocks_length (x :: xs)
            omega
          cases this
      | cons y ys =>
          have hx : decodeHead (blocks (x :: xs)) = some x := by
            simpa [blocks] using decodeHead_blockList x (blocks xs)
          have hy : decodeHead (blocks (y :: ys)) = some y := by
            simpa [blocks] using decodeHead_blockList y (blocks ys)
          have : x = y := by
            have : (some x : Option Bool) = some y := by
              rw [← hx, ← hy, h]
            exact Option.some.inj this
          subst this
          have htail : blocks xs = blocks ys := by
            have := congrArg (List.drop 2) h
            -- blocks (x::xs) = blockList x ++ blocks xs
            simp [blocks, blockList_length, List.drop_append_of_le_length] at this
            exact this
          simpa using ih htail
