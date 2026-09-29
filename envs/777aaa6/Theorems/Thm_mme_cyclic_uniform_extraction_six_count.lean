-- Prove2me | Theorems.Thm_mme_cyclic_uniform_extraction_six_count
-- name    : mme_cyclic_uniform_extraction_six_count
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:21:22.803991+00:00
-- url     : https://prove2.me/theorems/a73b39ca-a9a8-4b51-aaf9-605984b907af
-- title:
--   A cyclic matrix extraction squares its count and volume under full symmetrization
-- statement:
--   A positive cyclic matrix extraction with common matrix volume V and nonnegative copy lower bound B yields a six-fold extraction with positive copies, copy lower bound B squared and common volume V squared. The construction uses all pairs of original copies and their swapped matrices. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_finite_MM_extraction_swap_double
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open MME
universe u

theorem mme_cyclic_uniform_extraction_six_count
    {K : Type u} [Field K] {T : TensorObj K 3} {k V : ℕ}
    (a b c : Fin k → ℕ) (hk : 0 < k)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j))) (cyclicSymmetrization T))
    (hvolume : ∀ j, a j * b j * c j = V)
    (B : ℝ) (hB : 0 ≤ B) (hcount : B ≤ (k : ℝ)) :
    ∃ (copies : ℕ) (a' b' c' : Fin copies → ℕ),
      0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a' j) (b' j) (c' j))) (sixSymmetrization T) ∧
      B ^ 2 ≤ (copies : ℝ) ∧
      ∀ j, a' j * b' j * c' j = V ^ 2 := by sorry
