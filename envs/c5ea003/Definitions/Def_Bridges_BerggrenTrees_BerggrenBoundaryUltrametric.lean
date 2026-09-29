-- Prove2me | Definitions.Def_Bridges_BerggrenTrees_BerggrenBoundaryUltrametric
-- name    : Bridges_BerggrenTrees_BerggrenBoundaryUltrametric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:50.830174+00:00
-- url     : https://prove2.me/theorems/58f7187e-e4fe-40ba-940d-0e7a240123ed
-- title:
--   Aether Catalog definitions — Bridges_BerggrenTrees_BerggrenBoundaryUltrametric
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenTrees.BerggrenBoundaryUltrametric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenTrees/BerggrenBoundaryUltrametric.lean by skeleton subtraction
import Mathlib
/-
  # The Berggren Boundary Ultrametric (Conjecture C1, analytic half)

  The ternary Berggren tree of primitive Pythagorean triples is a rooted `3`-ary tree:
  every primitive triple has exactly three children `A`, `B`, `C`.  An infinite descent
  through the tree is therefore an *address* `x : ℕ → Fin 3`, and the set of all such
  addresses is the boundary `Addr` of the tree.

  This file supplies the bespoke tree ultrametric

  `d x y = 2 ^ (-firstDiff x y)`,  `firstDiff x y = min { n | x n ≠ y n }`,

  together with all the axioms needed to package it as a Mathlib `MetricSpace` and
  `IsUltrametricDist` (which is done in `FunctorialTropicalPythagoreanMetric.lean`):
  `d_self`, `d_comm`, `d_nonneg`, `d_eq_zero_iff`, `d_ultra`, `d_triangle`, `d_le_one`,
  and the two branch lemmas `d_cons_same` (each branch insertion is an exact `1/2`
  similarity) and `d_cons_diff` (distinct branches are maximally separated).

  -- !-- Lab Notes -- !--
  HYPOTHESIS: the "first place where two descents through the Berggren tree diverge"
  is a genuine ultrametric, and branch insertion `cons k` scales it by exactly `1/2`.
  EXPERIMENT: define `firstDiff` as `sInf {n | x n ≠ y n}` and characterise it by the
  pair (`differs at n`, `agrees below n`); everything else follows from that lemma.
  ANALYSIS: the strong triangle inequality needs no induction — at the first index
  where `x` and `z` differ, one of `x, y` or `y, z` must already differ, so one of the
  two distances is at least `d x z`.
  CRITIQUE: `firstDiff x x = 0` by the `sInf ∅ = 0` convention, so `d` must be defined
  by a case split on `x = y`; every lemma below is stated for the case-split version.
-/

namespace CategoricalTropicalUltrametric

open Classical

/-- An address of a point of the boundary of the ternary Berggren tree: the infinite
sequence of branch choices `A`, `B`, `C` taken during the descent. -/
def Addr : Type := ℕ → Fin 3

instance : Inhabited Addr := ⟨fun _ => 0⟩

/-- Extensionality for addresses. -/
@[ext] theorem Addr.ext {x y : Addr} (h : ∀ n, x n = y n) : x = y := funext h

/-- The first index at which two addresses differ (`0` if they are equal). -/
noncomputable def firstDiff (x y : Addr) : ℕ := sInf {n | x n ≠ y n}


/-- At `firstDiff x y` two distinct addresses really do differ. -/
theorem firstDiff_spec {x y : Addr} (h : x ≠ y) : x (firstDiff x y) ≠ y (firstDiff x y) := by
  have : ∃ n, x n ≠ y n := by
    by_contra hc
    push_neg at hc
    exact h (Addr.ext hc)
  exact Nat.sInf_mem this


theorem firstDiff_comm (x y : Addr) : firstDiff x y = firstDiff y x := by
  unfold firstDiff
  congr 1
  ext n
  exact ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩

/-- The Berggren boundary ultrametric: `2 ^ (-firstDiff)`. -/
noncomputable def d (x y : Addr) : ℝ := if x = y then 0 else (1 / 2 : ℝ) ^ firstDiff x y

theorem d_self (x : Addr) : d x x = 0 := by simp [d]

theorem d_nonneg (x y : Addr) : 0 ≤ d x y := by
  unfold d
  split
  · exact le_rfl
  · positivity

theorem d_pos_of_ne {x y : Addr} (h : x ≠ y) : 0 < d x y := by
  simp only [d, if_neg h]
  positivity

theorem d_comm (x y : Addr) : d x y = d y x := by
  unfold d
  by_cases h : x = y
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h), firstDiff_comm]

theorem d_eq_zero_iff (x y : Addr) : d x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_gt (d_pos_of_ne hne))
  · intro h; rw [h, d_self]



/-- **Strong triangle inequality.**  `d` is an ultrametric. -/
theorem d_ultra (x y z : Addr) : d x z ≤ max (d x y) (d y z) := by
  by_cases hxz : x = z
  · simp only [hxz, d_self]
    exact le_max_of_le_left (d_nonneg _ _)
  set n := firstDiff x z with hn
  have hdiff : x n ≠ z n := firstDiff_spec hxz
  have hval : d x z = (1 / 2 : ℝ) ^ n := by rw [d, if_neg hxz]
  by_cases hxy : x n = y n
  · -- then `y` and `z` differ at `n`, so `d y z ≥ 2 ^ (-n)`
    have hyz : y n ≠ z n := by rw [← hxy]; exact hdiff
    have hyzne : y ≠ z := fun h => hyz (by rw [h])
    have hle : firstDiff y z ≤ n := Nat.sInf_le hyz
    have : (1 / 2 : ℝ) ^ n ≤ d y z := by
      rw [d, if_neg hyzne]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
    exact le_max_of_le_right (by rw [hval]; exact this)
  · have hxyne : x ≠ y := fun h => hxy (by rw [h])
    have hle : firstDiff x y ≤ n := Nat.sInf_le hxy
    have : (1 / 2 : ℝ) ^ n ≤ d x y := by
      rw [d, if_neg hxyne]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
    exact le_max_of_le_left (by rw [hval]; exact this)

/-- The ordinary triangle inequality, a consequence of the strong one. -/
theorem d_triangle (x y z : Addr) : d x z ≤ d x y + d y z := by
  refine (d_ultra x y z).trans ?_
  rcases max_cases (d x y) (d y z) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [d_nonneg y z]
  · rw [h]; linarith [d_nonneg x y]

/-- Insertion of one Berggren branch label in front of an address. -/
def cons (k : Fin 3) (x : Addr) : Addr
  | 0 => k
  | n + 1 => x n







end CategoricalTropicalUltrametric


