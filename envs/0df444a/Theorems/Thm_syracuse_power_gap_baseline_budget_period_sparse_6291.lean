-- Prove2me | Theorems.Thm_syracuse_power_gap_baseline_budget_period_sparse_6291
-- name    : syracuse_power_gap_baseline_budget_period_sparse_6291
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-02T14:17:04.386424+00:00
-- url     : https://prove2.me/theorems/86d6ebd5-f48c-4488-ad86-577e76e9b0b1
-- title:
--   Sparse periods under the explicit 2310000 power-gap budget
-- statement:
--   Let p and K be natural numbers with p at least6291. Assume explicitly the strict power gap 3^p < 2^K and the arithmetic budget 2^K * 2310000^p <= 6930001^p. Then either p=6291 or p is at least6956. Equivalently, these exact premises exclude the integer periods6292 through6955. This is a pure arithmetic implication: no Syracuse orbit, cycle, least period, minimum, primitive word or valuation realization is assumed or proved. Neither supplied arithmetic premise is inferred for arbitrary p,K. The constants preserve the original2310000 budget, not an improved baseline. The pair p6291/K9971 remains compatible with the premises and is not eliminated. The proposed theorem name follows the surrounding research's naming convention but its type needs onlyMathlib. This source-only candidate has not been elaborated, kernel-verified, independently reviewed as a submission packet, published or accepted; no unbounded parent or Collatz proof is claimed.
-- source:
--   Task94 source-only submission assembly from the independently source-reviewed Task93 arithmetic draft at C:/Users/jason/prove2me/cycle_budget_period_sparse_6291_draft_01.lean, with companion explanation/preparation and the actual completed main-source-review record. The new submission retains all proof bodies and constants, changes only the outer entry name to solution and the truthful source-only header, and omits four unexecuted axiom-print requests plus their audit comment/separator. Its proved repeated-squaring evaluator is copied from the fixed5626 source pattern. The accompanying preparation freezes exact raw input/output hashes and transformations. No community theorem/definition, Open obligation, target or public theorem is imported. Historical source review and source-pattern acceptance are provenance only, not kernel verification or review of this assembled packet. This problem JSON is a conventional env/problems publication-shaped payload; its sorry is solely a statement placeholder, not the solution proof. No public UUID, registration, frontier assignment, publication authorization, mathematical novelty claim or proof transport is supplied.

import Mathlib

set_option autoImplicit false

theorem syracuse_power_gap_baseline_budget_period_sparse_6291 (p K : ℕ) (hlarge : 6291 ≤ p)
    (hgap : 3 ^ p < 2 ^ K)
    (hbudget : 2 ^ K * 2310000 ^ p ≤ 6930001 ^ p) :
    p = 6291 ∨ 6956 ≤ p := by sorry
