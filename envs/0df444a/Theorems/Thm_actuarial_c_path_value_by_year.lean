-- Prove2me | Theorems.Thm_actuarial_c_path_value_by_year
-- name    : actuarial_c_path_value_by_year
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:23:12.814745+00:00
-- url     : https://prove2.me/theorems/4d9af383-493f-41e5-aaf0-e582c95aa09e
-- title:
--   Realised single death-year insurance present value
-- statement:
--   For a finite right-censored single-life model, prove that the realised year-end life assurance present value is exactly v^(k+1) times death benefit b_k when the death-year index k is before the terminal horizon h, and zero otherwise. This makes the unique covered death event explicit and excludes terminal survivors from the death benefit.
--
--   The original mathematical identity is an open formal mission target. Its type has been copied exactly from a successful private remote Lean proof, which does not establish acceptance of this individual Prove2Me target.
-- source:
--   Original actuarial formalisation informed by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 and 5. Where the result is pure finite-sum algebra, it is an independently derived supporting identity, not claimed as a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_death

open ActuarialAssurances

theorem actuarial_c_path_value_by_year (h k : ℕ) (v : ℝ) (b : ℕ → ℝ) :
    path h v b k = if k < h then v^(k+1)*b k else 0 := by sorry
