-- Prove2me | solution 1 for UnitalMagmaDefect.AdjoinOne.defectSet_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T17:13:43.110541+00:00
-- url     : https://prove2.me/submissions/b6917419-6edc-458e-b324-184a5f71f9f9

import Mathlib
import Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
import Definitions.Def_Combinatorics_UnitalMagmaDefect
universe u
open UnitalMagmaDefect UnitalMagmaDefect.AdjoinOne Finset in
theorem solution {M : Type u} [Mul M] [Fintype M] [DecidableEq M]
    (hcomm : ∀ a b : M, a * b = b * a)
    {M : Type u} [Mul M] [One M] [Fintype M] [DecidableEq M]
    (hl : ∀ a : M, (1 : M) * a = a) (hr : ∀ a : M, a * (1 : M) = a)
    {α : Type u} [Mul α] [Fintype α] [DecidableEq α] :
    defectSet (AdjoinOne α)
      = (defectSet α).image (fun t => ((of t.1 : AdjoinOne α), of t.2.1, of t.2.2)) := by
  ext ⟨x, y, z⟩
  simp only [defectSet, mem_filter, mem_univ, true_and, mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · intro h
    cases x with
    | none => exact absurd rfl h
    | some a =>
      cases y with
      | none => exact absurd rfl h
      | some b =>
        cases z with
        | none => exact absurd rfl h
        | some c =>
          exact ⟨a, b, c, fun e => h (congrArg (fun v : α => (some v : Option α)) e), rfl, rfl, rfl⟩
  · rintro ⟨a, b, c, h, rfl, rfl, rfl⟩
    intro e
    exact h (Option.some.inj (e : (some ((a * b) * c) : Option α) = some (a * (b * c))))
