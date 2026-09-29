-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.exists_dpRun_ending
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:57:56.255459+00:00
-- url     : https://prove2.me/submissions/8acdc1e3-deb9-43b4-93b8-5f0e14ed409a

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessConstrained
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    [AddLeftMono W] [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    (D : DPSpec S W) :
    ∀ (n : ℕ) (s : S), ∃ f : ℕ → S, f n = s ∧ D.IsDPRun n f := by
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
