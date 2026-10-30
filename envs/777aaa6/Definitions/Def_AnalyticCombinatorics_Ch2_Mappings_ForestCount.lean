-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ForestCount
-- name    : AnalyticCombinatorics_Ch2_Mappings_ForestCount
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:47:59.169707+00:00
-- url     : https://prove2.me/theorems/674eb9c4-3d0a-4e7b-8d3c-cab8b3f7b818
-- title:
--   Finite parent maps absorbed by a specified root set
-- statement:
--   For a specified set of labelled roots, a parent map is defined on the nonroot vertices. Its total extension fixes every root. A functional rooted forest is such a map for which every vertex eventually reaches the root set. The source specifies the finite-type structure used for cardinalities and maps for the all-root and single-nonroot cases.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/ForestCount.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Rooted forests with a specified root set

This file records the functional formulation of rooted labelled forests used in
Flajolet--Sedgewick, Chapter II: a forest rooted at a specified set `R` is a
parent map from non-roots to all vertices whose `step`-orbits are absorbed by
`R`.

The full Cayley--Pollak count is

`# rootedForests R = |R| * n ^ (n - |R| - 1)` for `0 < |R| < n`,

with the separate all-roots case equal to `1`.  The file proves the faithful
definitions, the all-roots and one-non-root cases, the total number of parent
maps, and the Abel/binomial identity that is the algebraic core of the standard
depth-one recurrence proof.
-/

open scoped BigOperators

namespace AnalyticCombinatorics.Ch2.Mappings.ForestCountNS

noncomputable section

/-- The non-root vertices for a specified root set. -/
abbrev NonRoot {n : ℕ} (R : Finset (Fin n)) : Type :=
  {x : Fin n // x ∉ R}

/--
Extend a partial parent map to all vertices by fixing the roots.  Non-roots move
to their chosen parent; roots are absorbing.
-/
def step {n : ℕ} (R : Finset (Fin n)) (g : NonRoot R → Fin n) (y : Fin n) : Fin n :=
  if h : y ∈ R then y else g ⟨y, h⟩

/-- A vertex reaches the root set under the absorbing extension of the parent map. -/
def Reaches {n : ℕ} (R : Finset (Fin n)) (g : NonRoot R → Fin n) (x : Fin n) : Prop :=
  ∃ m : ℕ, (step R g)^[m] x ∈ R

/-- Functional rooted forests with specified root set `R`. -/
abbrev RootedForests {n : ℕ} (R : Finset (Fin n)) : Type :=
  {g : NonRoot R → Fin n // ∀ x : Fin n, Reaches R g x}

/--
The explicit subtype fintype used for forest counts.  `Mathlib` also imports
category-theoretic finite-category instances; pinning this instance keeps the
cardinality statements definitionally stable.
-/
@[reducible] def rootedForestsFintype {n : ℕ} (R : Finset (Fin n)) :
    Fintype (RootedForests R) := by
  classical
  exact Subtype.fintype (fun g : NonRoot R → Fin n => ∀ x : Fin n, Reaches R g x)

@[simp] lemma step_of_notMem {n : ℕ} {R : Finset (Fin n)} (g : NonRoot R → Fin n)
    {y : Fin n} (hy : y ∉ R) :
    step R g y = g ⟨y, hy⟩ := by
  simp [step, hy]

lemma reaches_of_mem {n : ℕ} {R : Finset (Fin n)} (g : NonRoot R → Fin n)
    {x : Fin n} (hx : x ∈ R) :
    Reaches R g x := by
  exact ⟨0, by simpa [Reaches] using hx⟩

lemma forest_parent_of_unique_nonRoot_mem_roots {n : ℕ} {R : Finset (Fin n)}
    (a : NonRoot R) (ha : ∀ x : NonRoot R, x = a) (F : RootedForests R) :
    F.1 a ∈ R := by
  classical
  by_contra hnot
  have hstep : step R F.1 a.1 = a.1 := by
    simpa [step, a.2] using congrArg Subtype.val (ha ⟨F.1 a, hnot⟩)
  rcases F.2 a.1 with ⟨m, hm⟩
  have hfixed : (step R F.1)^[m] a.1 = a.1 :=
    Function.iterate_fixed hstep m
  exact a.2 (by simpa [hfixed] using hm)

lemma reaches_unique_nonRoot {n : ℕ} {R : Finset (Fin n)}
    (a : NonRoot R) (ha : ∀ x : NonRoot R, x = a) (r : R) :
    ∀ x : Fin n, Reaches R (fun _ : NonRoot R => (r : Fin n)) x := by
  intro x
  by_cases hx : x ∈ R
  · exact reaches_of_mem (fun _ : NonRoot R => (r : Fin n)) hx
  · have hx_eq : (⟨x, hx⟩ : NonRoot R) = a := ha ⟨x, hx⟩
    refine ⟨1, ?_⟩
    simp [step_of_notMem (fun _ : NonRoot R => (r : Fin n)) hx]

/--
If there is exactly one non-root vertex, a forest is determined by the root that
is its parent.
-/
def rootedForestsEquivRootsOfUniqueNonRoot {n : ℕ} {R : Finset (Fin n)}
    (a : NonRoot R) (ha : ∀ x : NonRoot R, x = a) :
    RootedForests R ≃ R where
  toFun F := ⟨F.1 a, forest_parent_of_unique_nonRoot_mem_roots a ha F⟩
  invFun r := ⟨(fun _ : NonRoot R => (r : Fin n)), reaches_unique_nonRoot a ha r⟩
  left_inv F := by
    apply Subtype.ext
    funext x
    have hx : x = a := ha x
    calc
      (fun _ : NonRoot R => F.1 a) x = F.1 a := rfl
      _ = F.1 x := by rw [hx]
  right_inv r := by
    ext
    rfl

end

end AnalyticCombinatorics.Ch2.Mappings.ForestCountNS


