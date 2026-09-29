-- Prove2me | Theorems.Thm_syracuse_crossing_cardinality
-- name    : syracuse_crossing_cardinality
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T05:31:39.829717+00:00
-- url     : https://prove2.me/theorems/37b79a37-f9b8-447d-abf9-e558b094dbfa
-- title:
--   Actual Syracuse crossing inputs satisfy the deterministic residue-count bound
-- statement:
--   For an ambient width b, a positive threshold q with q ≤ b, and an independent prefix length t, consider positive odd integers x with x < 2^b (equivalently, least nonnegative residue representatives) whose first t accelerated Syracuse valuation exponents have sum at least q. Their cardinality is at most 2^(b-q) times the sum over k<t of binom(q-1,k). This is only the deterministic finite crossing-count step: it does not assert invariance over all residue representatives or Tao's probabilistic or density conclusion.
-- source:
--   Deterministic finite crossing-label count in Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 4, proof of Lemma 4.1. The producer reuses the published generic crossing-residue cardinality and valuation-prefix residue interfaces, while supplying the Syracuse orbit-label adapter locally.

import Mathlib
import Definitions.Def_syracuseStep
set_option autoImplicit false
open scoped BigOperators
open Classical

theorem syracuse_crossing_cardinality (b q t : ℕ) (hq : 0 < q) (hqb : q ≤ b) : (Finset.univ.filter (fun x : Fin (2 ^ b) => 0 < x.val ∧ Odd x.val ∧ q ≤ ∑ i ∈ Finset.range t, (3 * (syracuseStep^[i]) x.val + 1).factorization 2)).card ≤ 2 ^ (b - q) * (∑ k : Fin t, Nat.choose (q - 1) k) := by sorry
