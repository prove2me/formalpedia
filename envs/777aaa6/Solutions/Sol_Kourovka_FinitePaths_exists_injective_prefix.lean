-- Prove2me | solution 1 for Kourovka.FinitePaths.exists_injective_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:31:25.957355+00:00
-- url     : https://prove2.me/submissions/f96dda95-a42c-4db3-8009-06377181df14

import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Kourovka_FinitePaths

set_option autoImplicit true
open Kourovka
open Kourovka.FinitePaths
namespace Kourovka.FinitePaths
theorem _root_.solution {α ι : Type*} [Fintype ι]
    (f : ι → ℕ → α) (hf : Function.Injective f) :
    ∃ n, Function.Injective (fun i => initialSegment n (f i)) := by
  classical
  have hsep : ∀ i j : ι, i ≠ j → ∃ k, f i k ≠ f j k := by
    intro i j hij
    exact Function.ne_iff.mp (fun h => hij (hf h))
  let d : ι × ι → ℕ := fun p =>
    if h : p.1 = p.2 then 0 else Classical.choose (hsep p.1 p.2 h)
  let n := Finset.univ.sup (fun p : ι × ι => d p + 1)
  refine ⟨n, ?_⟩
  intro i j hij
  by_contra hne
  have hd : f i (d (i, j)) ≠ f j (d (i, j)) := by
    simpa only [d, dif_neg hne] using Classical.choose_spec (hsep i j hne)
  have hdn : d (i, j) < n := by
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Finset.le_sup (f := fun p : ι × ι => d p + 1) (Finset.mem_univ (i, j)))
  exact hd (congrFun hij ⟨d (i, j), hdn⟩)
end Kourovka.FinitePaths
