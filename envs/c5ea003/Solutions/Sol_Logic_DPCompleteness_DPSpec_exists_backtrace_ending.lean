-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.exists_backtrace_ending
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:07:12.618559+00:00
-- url     : https://prove2.me/submissions/27f55b14-1603-4552-a0c3-773d64a588ac

-- Sol generated from Logic/DPCompletenessConstrained.lean
import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessConstrained
import Theorems.Thm_Logic_DPCompleteness_DPSpec_val_succ
/-
# Completeness without cancellativity, and constrained dynamic programming

In `Logic.DPCompleteness` the notion `IsDPRun` was *semantic* (all prefix scores are optimal)
and the existence of runs was proved using cancellativity of the weight monoid.  This file
removes that hypothesis by working with the *structural* (backtrace) notion of a run:

> `IsBacktrace D n f` : at each stage the DP recursion is realised on the nose,
> `val i (f i) + step i (f i) (f (i+1)) = val (i+1) (f (i+1))`.

The two notions turn out to be equivalent for **every** ordered weight monoid
(`isBacktrace_iff_isDPRun`), and completeness holds with no cancellativity assumption
(`dp_complete_general`).  This is exactly what is needed to cover **constrained** dynamic
programming, where infeasible transitions carry the absorbing weight `⊥` of `WithBot W` — a
monoid that is emphatically *not* cancellative.

As an application we characterise infeasibility (`val_eq_bot_iff`) and instantiate the theory on
the classical maximum-weight independent set problem on a path.
-/


open Logic.DPCompleteness

open DPSpec

/-! ## Structural runs -/


variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]









/-! ## Constrained dynamic programming over `WithBot` -/


variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]




/-! ## Application: maximum-weight independent set on a path -/









open Logic.DPCompleteness in
omit [AddLeftMono W] in
theorem solution(D : DPSpec S W) :
    ∀ (n : ℕ) (s : S), ∃ f : ℕ → S, f n = s ∧ D.IsBacktrace n f := by
  intro n
  induction n with
  | zero => intro s; exact ⟨fun _ => s, rfl, by intro i hi; omega⟩
  | succ n ih =>
      intro t
      obtain ⟨s, -, hs⟩ :=
        Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := S))
          (fun s => D.val n s + D.step n s t)
      obtain ⟨f, hfn, hf⟩ := ih s
      set g : ℕ → S := fun i => if i ≤ n then f i else t with hgdef
      have hgn : g n = f n := by simp [hgdef]
      have hgn1 : g (n + 1) = t := by simp [hgdef]
      refine ⟨g, hgn1, ?_⟩
      intro i hi
      rcases Nat.lt_or_ge i n with hlt | hge
      · have e1 : g i = f i := by simp [hgdef, Nat.le_of_lt hlt]
        have e2 : g (i + 1) = f (i + 1) := by simp [hgdef, hlt]
        rw [e1, e2]
        exact hf i hlt
      · have hin : i = n := le_antisymm (Nat.lt_succ_iff.mp hi) hge
        subst hin
        rw [hgn, hgn1, hfn, val_succ, hs]
