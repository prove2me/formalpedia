-- Prove2me | Theorems.Thm_term_denotable_finite_support
-- name    : term_denotable_finite_support
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:04:27.866237+00:00
-- url     : https://prove2.me/theorems/7f204594-e9f0-4b7d-bf77-abdca09411da
-- title:
--   `term_denotable_finite_support` (v : DenseCore) : (Function.support (v : ℕ → ℝ)).Finite
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPaFreeCompletion`.
--
--   `term_denotable_finite_support` (v : DenseCore) : (Function.support (v : ℕ → ℝ)).Finite
--
--   Formalization note: Lean 4 identifier `term_denotable_finite_support`.

-- Generated from ChapterPaFreeCompletion.lean — theorem term_denotable_finite_support
import Definitions.Def_ChapterRieszFischer
import Mathlib
import Definitions.Def_ChapterPaFreeCompletion
import Definitions.Def_ChapterA4


open Set
open Filter
open BookProof.ChapterRieszFischer

theorem term_denotable_finite_support (v : DenseCore) :
    (Function.support (v : ℕ → ℝ)).Finite := by sorry
