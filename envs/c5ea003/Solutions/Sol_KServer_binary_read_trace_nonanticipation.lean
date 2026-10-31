-- Prove2me | solution 1 for KServer.binary_read_trace_nonanticipation
-- status  : ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T17:47:15.74271+00:00
-- url     : https://prove2.me/submissions/9ff9b99a-4e19-4d15-a0f4-417f5880da85

import Definitions.Def_KServer_binary_read_trace
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open KServer

theorem solution {ι : Type*} (grade : ι → ℕ)
    (choose : ℕ → (ℕ → Bool) → ι) (N : ℕ)
    (hgrade : ∀ n < N, ∀ history : ℕ → Bool, grade (choose n history) = n)
    (n : ℕ) (hn : n ≤ N) (seed seed' : ι → Bool)
    (hagree : ∀ i, grade i < n → seed i = seed' i) :
    binaryReadTrace choose seed n = binaryReadTrace choose seed' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprefix : binaryReadTrace choose seed n = binaryReadTrace choose seed' n :=
      ih (by omega) (fun i hi => hagree i (by omega))
    have hnow : seed (choose n (binaryReadTrace choose seed' n)) =
        seed' (choose n (binaryReadTrace choose seed' n)) := by
      apply hagree
      rw [hgrade n (by omega)]
      omega
    simp only [binaryReadTrace, hprefix, hnow]
