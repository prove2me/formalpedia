-- Prove2me | solution 1 for Kourovka.FinitePaths.ncard_le_of_bounded_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:17.746586+00:00
-- url     : https://prove2.me/submissions/e3205a0c-3177-4dc3-aa38-4acd56575e8f

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_FinitePaths
import Theorems.Thm_Kourovka_FinitePaths_exists_injective_prefix
import Theorems.Thm_Kourovka_FinitePaths_finite_of_bounded_prefixes

set_option autoImplicit true
open Kourovka
open Kourovka.FinitePaths
namespace Kourovka.FinitePaths
theorem _root_.solution {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b) : X.ncard ≤ b := by
  classical
  letI : Fintype X := (finite_of_bounded_prefixes X b hb).fintype
  obtain ⟨n, hn⟩ := exists_injective_prefix (fun x : X => x.val) Subtype.val_injective
  have hinj : Set.InjOn (initialSegment n) X := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hn (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  simpa only [Set.ncard_image_of_injOn hinj] using hb n
end Kourovka.FinitePaths
