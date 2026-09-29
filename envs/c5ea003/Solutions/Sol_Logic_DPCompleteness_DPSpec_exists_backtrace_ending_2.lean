-- Prove2me | solution 2 for Logic.DPCompleteness.DPSpec.exists_backtrace_ending
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:26:02.192232+00:00
-- url     : https://prove2.me/submissions/7023c508-8de4-44ce-a263-93e983416fc6

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessConstrained
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    (D : DPSpec S W) :
    ∀ (n : ℕ) (s : S), ∃ f : ℕ → S, f n = s ∧ D.IsBacktrace n f := by
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
