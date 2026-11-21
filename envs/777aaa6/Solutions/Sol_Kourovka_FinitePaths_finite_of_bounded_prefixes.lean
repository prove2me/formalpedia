-- Prove2me | solution 1 for Kourovka.FinitePaths.finite_of_bounded_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:31:50.212105+00:00
-- url     : https://prove2.me/submissions/9f4ad887-7d15-47fb-959a-23f500900b4c

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_FinitePaths
import Theorems.Thm_Kourovka_FinitePaths_exists_injective_prefix

set_option autoImplicit true
open Kourovka
open Kourovka.FinitePaths
namespace Kourovka.FinitePaths
theorem _root_.solution {α : Type*} [Finite α]
    (X : Set (ℕ → α)) (b : ℕ)
    (hb : ∀ n, (initialSegment n '' X).ncard ≤ b) : X.Finite := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  by_contra hX
  obtain ⟨T, hTX, hT, hcard⟩ := Set.Infinite.exists_subset_ncard_eq hX (b + 1)
  letI : Fintype T := hT.fintype
  obtain ⟨n, hn⟩ := exists_injective_prefix (fun x : T => x.val) Subtype.val_injective
  have hinj : Set.InjOn (initialSegment n) T := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hn (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hle : (initialSegment n '' T).ncard ≤ (initialSegment n '' X).ncard :=
    Set.ncard_le_ncard (Set.image_mono hTX)
  rw [Set.ncard_image_of_injOn hinj, hcard] at hle
  have := hb n
  omega
end Kourovka.FinitePaths
