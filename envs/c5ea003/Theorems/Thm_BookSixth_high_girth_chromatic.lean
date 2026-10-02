-- Prove2me | Theorems.Thm_BookSixth_high_girth_chromatic
-- name    : BookSixth.high_girth_chromatic
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-13T01:37:21.957241+00:00
-- url     : https://prove2.me/theorems/492eed0e-887f-4c2f-b442-46dfedbca013
-- title:
--   Chapter 45, Theorem 3: high girth and chromatic number
-- statement:
--   For every integer k at least 2, some finite simple graph is not properly k-colorable and has no simple cycle of length at most k. Thus its chromatic number and girth both exceed k.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 3: high girth and chromatic number, p. 314. https://doi.org/10.1007/978-3-662-57265-8_45

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.high_girth_chromatic (k : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, ∃ G : SimpleGraph (Fin N), ¬ HasColoring G k ∧
      ∀ l : ℕ, l ≤ k → ¬ HasCycle G l := by sorry
