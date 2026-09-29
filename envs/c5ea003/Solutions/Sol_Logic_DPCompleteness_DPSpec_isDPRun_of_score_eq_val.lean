-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.isDPRun_of_score_eq_val
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:19:28.806967+00:00
-- url     : https://prove2.me/submissions/4972d84d-c8c7-494a-a02e-0c5cc910c588

import Mathlib
import Definitions.Def_Logic_DPCompleteness
open Logic.DPCompleteness in
theorem solution {S : Type*} {W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S]
    [LinearOrder W] [AddLeftMono W] [Fintype S] [Nonempty S] [LinearOrder W]
    [IsOrderedCancelAddMonoid W] (D : DPSpec S W) (f : ℕ → S) {n : ℕ} :
    D.score f n = D.val n (f n) → D.IsDPRun n f := by
  intro hn
  -- the score of a labelling never beats the DP value
  have hle : ∀ m : ℕ, D.score f m ≤ D.val m (f m) := by
    intro m
    induction m with
    | zero => exact le_of_eq rfl
    | succ m ih =>
      show D.score f m + D.step m (f m) (f (m + 1)) ≤ D.val (m + 1) (f (m + 1))
      have h1 : D.score f m + D.step m (f m) (f (m + 1))
          ≤ D.val m (f m) + D.step m (f m) (f (m + 1)) := by gcongr
      refine h1.trans ?_
      show D.val m (f m) + D.step m (f m) (f (m + 1))
          ≤ (Finset.univ : Finset S).sup' Finset.univ_nonempty
              (fun s => D.val m s + D.step m s (f (m + 1)))
      exact Finset.le_sup' (fun s => D.val m s + D.step m s (f (m + 1))) (Finset.mem_univ (f m))
  -- optimality at a stage forces optimality one stage earlier
  have hstep : ∀ m : ℕ, D.score f (m + 1) = D.val (m + 1) (f (m + 1)) →
      D.score f m = D.val m (f m) := by
    intro m hm
    by_contra hne
    have hlt : D.score f m < D.val m (f m) := lt_of_le_of_ne (hle m) hne
    have h1 : D.score f m + D.step m (f m) (f (m + 1))
        < D.val m (f m) + D.step m (f m) (f (m + 1)) := by
      gcongr
    have h2 : D.val m (f m) + D.step m (f m) (f (m + 1)) ≤ D.val (m + 1) (f (m + 1)) :=
      Finset.le_sup' (fun s => D.val m s + D.step m s (f (m + 1))) (Finset.mem_univ (f m))
    have h3 : D.score f (m + 1) < D.val (m + 1) (f (m + 1)) := lt_of_lt_of_le h1 h2
    rw [hm] at h3
    exact absurd h3 (lt_irrefl _)
  -- walk the equality all the way down
  have hdown : ∀ k i : ℕ, D.score f (i + k) = D.val (i + k) (f (i + k)) →
      D.score f i = D.val i (f i) := by
    intro k
    induction k with
    | zero => intro i h; simpa using h
    | succ k ih =>
      intro i h
      refine ih i (hstep (i + k) ?_)
      have hik : i + (k + 1) = (i + k) + 1 := by omega
      rwa [hik] at h
  intro i hi
  exact hdown (n - i) i (by rw [show i + (n - i) = n by omega]; exact hn)
