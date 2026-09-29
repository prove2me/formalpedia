-- Prove2me | Theorems.Thm_mme_CW_quarter_root_count_absorption
-- name    : mme_CW_quarter_root_count_absorption
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:14:37.267881+00:00
-- url     : https://prove2.me/theorems/bcc2b343-9b57-4d04-b52b-d559b79fef5e
-- title:
--   Absorb the primary and induced-matching half-losses
-- statement:
--   Let \(N,A,H,k\) be natural numbers and let \(R,\delta,W\) be real numbers with \(W\ge0\).  If
--   \[
--   (R e^{-\delta/2})^{2N}\le A^3H^2W
--   \qquad\text{and}\qquad
--   H^2e^{-N\delta}\le k,
--   \]
--   then
--   \[
--   (R e^{-\delta})^{2N}\le A^3kW.
--   \]
--
--   This elementary lemma combines the loss budget assigned to the primary C-tensor pruning with the loss budget assigned to the separate induced-matching extraction.  It uses an exact exponential identity, so no sign hypothesis on \(R\) is required.
-- source:
--   Elementary real-algebra consequence of the two quantitative stages in the coupled Coppersmith--Winograd extraction.

import Mathlib.Analysis.SpecialFunctions.Exp
open Real

theorem mme_CW_quarter_root_count_absorption
    (N A H k : ℕ) (raw loss W : ℝ)
    (hW : 0 ≤ W)
    (hprimary :
      (raw * Real.exp (-(loss / 2))) ^ (2 * N) ≤
        (((A ^ 3 : ℕ) : ℝ) * ((H : ℝ) ^ 2)) * W)
    (hsecondary :
      ((H : ℝ) ^ 2) * Real.exp (-((N : ℝ) * loss)) ≤ (k : ℝ)) :
    (raw * Real.exp (-loss)) ^ (2 * N) ≤
      ((((A ^ 3) * k : ℕ) : ℝ)) * W := by sorry
