-- Prove2me | Theorems.Thm_BookSixth_isUnlink_path_image
-- name    : BookSixth.isUnlink_path_image
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T06:43:17.01812+00:00
-- url     : https://prove2.me/theorems/c8865be9-02ba-4cc8-a82e-0843ef213a5f
-- title:
--   Chapter 15 bridge: transport an unlink certificate along an isotopy path
-- statement:
--   If a finite ordered family is an unlink, applying the endpoint of a continuous ambient-isotopy path to every component gives another unlink. The path begins at the identity, so the transported family is again the image of an isotopy starting at the identity.
-- source:
--   Source-faithful reindexing invariant for the Chapter 15, Theorem 1 ambient-transport construction in Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 100. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.isUnlink_path_image {m : ℕ}
    (C : Fin m → Set Space3)
    (K : ℝ → Space3 ≃ₜ Space3)
    (hK : Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x))
    (hC : IsUnlink C) :
    IsUnlink (fun i => K 1 '' C i) := by sorry
