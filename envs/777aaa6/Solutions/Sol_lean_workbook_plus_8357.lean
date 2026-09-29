-- Prove2me | solution 1 for lean_workbook_plus_8357
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:53:07.198545+00:00
-- url     : https://prove2.me/submissions/085ce73d-7fc2-45b9-8aec-09dea242d246

import Mathlib.Analysis.Complex.Basic
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

theorem solution (E : Type) (g : E → E) (a : E) : ∃! f : ℕ → E, f 0 = a ∧ ∀ n, f (n + 1) = g (f n) := by
  refine ⟨fun n => g^[n] a, ⟨rfl, fun n => Function.iterate_succ_apply' g n a⟩, ?_⟩
  intro f hf
  funext n
  induction n with
  | zero => exact hf.1
  | succ n ih => rw [hf.2, Function.iterate_succ_apply', ih]
