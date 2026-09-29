-- Prove2me | Theorems.Thm_positive_exponent_prefix_cardinality
-- name    : positive_exponent_prefix_cardinality
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T04:17:48.986614+00:00
-- url     : https://prove2.me/theorems/d229945b-1584-44ca-bc10-b8373e037687
-- title:
--   Positive exponent prefixes are counted by a binomial coefficient
-- statement:
--   For any natural k and any positive natural threshold n', the finite set of k-tuples of positive exponents whose sum is strictly less than n' has cardinality Nat.choose (n' - 1) k. The proof appends the positive slack n' minus the exponent sum, obtaining a positive composition of n' with k+1 parts, and identifies the k interior cut positions with a k-element subset of Fin (n' - 1). The statement includes the empty tuple case k=0 and the boundary case n'=1.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 4, proof of Lemma 4.1. https://arxiv.org/html/1909.03562v7 . This is the deterministic positive-prefix counting factor only; it is narrower than Tao's probabilistic lemma and makes no orbit-distribution claim.

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
set_option autoImplicit false
open scoped BigOperators
open Classical

theorem positive_exponent_prefix_cardinality (k n' : ℕ) (hn' : 0 < n') : Fintype.card {a : Fin k → Fin n' // (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < n'} = Nat.choose (n' - 1) k := by sorry
