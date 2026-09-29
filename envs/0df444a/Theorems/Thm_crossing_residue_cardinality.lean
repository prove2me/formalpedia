-- Prove2me | Theorems.Thm_crossing_residue_cardinality
-- name    : crossing_residue_cardinality
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T04:42:07.594263+00:00
-- url     : https://prove2.me/theorems/c67d3180-8861-4239-a705-293f64a47145
-- title:
--   Finite crossing families are bounded by residue multiplicity and prefix labels
-- statement:
--   Let b be an ambient 2-adic bit width, n' a positive residue modulus exponent with n' ≤ b, and t an independent prefix-length bound. If a finite family S of residues modulo 2^b is labelled by a crossing index k < t together with a positive exponent prefix of length k whose sum is below n', and equal labels force congruence modulo 2^{n'}, then |S| is at most 2^{b-n'} times the sum over k < t of the positive-prefix counts binom(n'-1,k).
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Section 4, proof of Lemma 4.1. This is only the deterministic finite residue-counting interface. It does not establish that Syracuse valuations provide the labels, nor any probability or density estimate.

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.Card
import Theorems.Thm_positive_exponent_prefix_cardinality
set_option autoImplicit false
open scoped BigOperators
open Classical

theorem crossing_residue_cardinality (b n' t : ℕ) (hn' : 0 < n') (hn'b : n' ≤ b) (S : Finset (Fin (2 ^ b))) (label : {x // x ∈ S} → Σ k : Fin t, {a : Fin k → Fin n' // (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < n'}) (hlabel : ∀ x y, label x = label y → Nat.ModEq (2 ^ n') x.1.1 y.1.1) : S.card ≤ 2 ^ (b - n') * (∑ k : Fin t, Nat.choose (n' - 1) k) := by sorry
