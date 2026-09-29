-- Prove2me | solution 2 for KitchenQuery.tasteCost_salad
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T08:25:05.412499+00:00
-- url     : https://prove2.me/submissions/6e03b7bd-4e4c-41d2-ae25-2ea775829f35

/-
# `KitchenQuery.tasteCost_salad`
Target `e76b7fb8` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN, built. Gift check (corrected logic): **SAFE**.

BINDERS — history is a single `SKETCH_ACCEPTED`, no CE and no WA, so there is no rejection text and
no mirror yet. The statement declares its argument INLINE — `(i : Fin n)` — over `variable {n : ℕ}`
(bundle line 85). The generated gate is the ONLY authority here and fails closed.

MATHS. `tasteCost f = sInf (tasteDepths f)` where
`tasteDepths f = {d | ∃ t, Computes t f ∧ t.depth ≤ d}`. Two halves:

  * UPPER — `probe i (serve false) (serve true)` has depth `1 + max 0 0 = 1` and evaluates to
    `if x i then true else false`, which is `salad i = fun x => x i`. So `1 ∈ tasteDepths`, and
    `Nat.sInf_le` gives `tasteCost ≤ 1`.
  * LOWER — `tasteCost ≠ 0`. Since the set is non-empty (the upper half exhibits a member),
    `Nat.sInf_eq_zero` reduces this to `0 ∉ tasteDepths`: a strategy of depth `≤ 0` must be a
    `serve b` (a `probe` has depth `1 + _ ≥ 1`), hence CONSTANT, while `salad i` differs at two
    pantries that disagree in coordinate `i`.

PROBED, NOT GUESSED — read out of Data/Nat/Lattice.lean:
  * `Nat.sInf_le {s} {m} (hm : m ∈ s) : sInf s ≤ m`
  * `Nat.sInf_eq_zero {s} : sInf s = 0 ↔ 0 ∈ s ∨ s = ∅`
  * `Nat.notMem_of_lt_sInf` also exists, as an alternative route to the lower bound.
  NOTE: I never located a `Nat.le_sInf`; the two above make it unnecessary, so the proof is written
  to avoid needing it rather than to assume it.
-/
import Mathlib
import Definitions.Def_Novelty_KitchenQueryComplexity

set_option autoImplicit false
set_option maxHeartbeats 400000

open KitchenQuery


open KitchenQuery in
/-- **The target, verbatim.** -/
theorem solution {n : ℕ} (i : Fin n) : tasteCost (salad i) = 1 := by
  classical
  -- the depth-1 witness
  have hcomp : Computes (Taste.probe i (Taste.serve false) (Taste.serve true)) (salad i) := by
    intro x
    simp [Taste.eval, salad]
  have hmem : (1 : ℕ) ∈ tasteDepths (salad i) :=
    ⟨Taste.probe i (Taste.serve false) (Taste.serve true), hcomp, by simp [Taste.depth]⟩
  have hle : tasteCost (salad i) ≤ 1 := Nat.sInf_le hmem
  -- the lower bound: 0 is not achievable, because a depth-0 strategy is constant
  have hzero : (0 : ℕ) ∉ tasteDepths (salad i) := by
    rintro ⟨t, hc, hd⟩
    -- a strategy of depth ≤ 0 must be a `serve`
    cases t with
    | probe j l r => simp [Taste.depth] at hd
    | serve b =>
        -- but `salad i` is not constant: it differs at two pantries disagreeing at `i`
        have h0 := hc (fun j => if j = i then false else false)
        have h1 := hc (fun j => if j = i then true else false)
        simp [Taste.eval, salad] at h0 h1
        exact absurd (h0.symm.trans h1) (by simp)
  have hne : tasteCost (salad i) ≠ 0 := by
    intro h
    rcases Nat.sInf_eq_zero.mp h with hin | hempty
    · exact hzero hin
    · exact absurd hmem (by rw [hempty]; simp)
  omega
