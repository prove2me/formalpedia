-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.isGreatest_val
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:01:48.030179+00:00
-- url     : https://prove2.me/submissions/23d38a8f-6a88-4339-a403-c8d31c325e3b

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessConstrained
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    [AddLeftMono W] [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    (D : DPSpec S W) (n : ℕ) (s : S) :
    IsGreatest {w | ∃ f : ℕ → S, f n = s ∧ D.score f n = w} (D.val n s) := by
  have hrun : ∀ (n : ℕ) (s : S), ∃ f : ℕ → S, f n = s ∧ D.IsDPRun n f := by
    have hbt : ∀ (n : ℕ) (s : S), ∃ f : ℕ → S, f n = s ∧ D.IsBacktrace n f := by
      -- every DP value is attained by some predecessor
      have hpred : ∀ (i : ℕ) (t : S), ∃ s' : S,
          D.val i s' + D.step i s' t = D.val (i + 1) t := by
        intro i t
        obtain ⟨s', _, hs'⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := S))
          (fun s => D.val i s + D.step i s t)
        exact ⟨s', hs'.symm⟩
      choose pred hpred using hpred
      intro n s
      -- walk backwards from `s` at stage `n`
      refine ⟨fun i => Nat.rec s (fun j prev => pred (n - (j + 1)) prev) (n - i), by simp, ?_⟩
      intro i hi
      have h1 : n - i = (n - (i + 1)) + 1 := by omega
      have h2 : n - (n - (i + 1) + 1) = i := by omega
      show D.val i (Nat.rec s (fun j prev => pred (n - (j + 1)) prev) (n - i))
          + D.step i (Nat.rec s (fun j prev => pred (n - (j + 1)) prev) (n - i))
            (Nat.rec s (fun j prev => pred (n - (j + 1)) prev) (n - (i + 1)))
          = D.val (i + 1) (Nat.rec s (fun j prev => pred (n - (j + 1)) prev) (n - (i + 1)))
      rw [h1]
      show D.val i (pred (n - (n - (i + 1) + 1))
            (Nat.rec s (fun j prev => pred (n - (j + 1)) prev) (n - (i + 1))))
          + D.step i (pred (n - (n - (i + 1) + 1))
            (Nat.rec s (fun j prev => pred (n - (j + 1)) prev) (n - (i + 1))))
            (Nat.rec s (fun j prev => pred (n - (j + 1)) prev) (n - (i + 1)))
          = D.val (i + 1) (Nat.rec s (fun j prev => pred (n - (j + 1)) prev) (n - (i + 1)))
      rw [h2]
      exact hpred i _
    intro n s
    obtain ⟨f, hfn, hf⟩ := hbt n s
    refine ⟨f, hfn, ?_⟩
    -- along a backtrace every prefix score is the DP value
    have key : ∀ i, i ≤ n → D.score f i = D.val i (f i) := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        have hi' : i < n := by omega
        have hstep := hf i hi'
        show D.score f i + D.step i (f i) (f (i + 1)) = D.val (i + 1) (f (i + 1))
        rw [ih (by omega), hstep]
    exact key
  have hle : ∀ (f : ℕ → S) (m : ℕ), D.score f m ≤ D.val m (f m) := by
    intro f
    intro m
    induction m with
    | zero => exact le_of_eq rfl
    | succ m ih =>
      show D.score f m + D.step m (f m) (f (m + 1)) ≤ D.val (m + 1) (f (m + 1))
      have h1 : D.score f m + D.step m (f m) (f (m + 1))
          ≤ D.val m (f m) + D.step m (f m) (f (m + 1)) := by gcongr
      refine h1.trans ?_
      exact Finset.le_sup' (fun s => D.val m s + D.step m s (f (m + 1))) (Finset.mem_univ (f m))
  constructor
  · obtain ⟨f, hfn, hf⟩ := hrun n s
    exact ⟨f, hfn, by rw [hf n le_rfl, hfn]⟩
  · rintro w ⟨f, hfn, rfl⟩
    have := hle f n
    rwa [hfn] at this
