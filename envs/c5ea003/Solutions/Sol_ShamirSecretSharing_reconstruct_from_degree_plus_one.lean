-- Prove2me | solution 1 for ShamirSecretSharing.reconstruct_from_degree_plus_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:04:34.670682+00:00
-- url     : https://prove2.me/submissions/a62d0ba0-9f1d-43ee-a0f7-2e92d49b33f6

-- Sol generated from Cryptography/ShamirSecretSharing.lean
import Mathlib
import Definitions.Def_Cryptography_ShamirSecretSharing

/-!
# Shamir secret sharing

This file formalizes the algebraic and information-theoretic core of Shamir's
scheme over an arbitrary field.  A sharing polynomial has its secret as its
value at zero.  Privacy is expressed without choosing a probability API: after
fixing any values at `t - 1` nonzero locations, every possible secret has
exactly one degree-`< t` polynomial extension.  Consequently a uniformly
random sharing polynomial induces exactly the same observation distribution
for every secret.
-/

open ShamirSecretSharing

open Polynomial

variable {F : Type*} [Field F]









open ShamirSecretSharing in
theorem solution[DecidableEq F]
    (locations : Finset F) (d : ℕ) (hcard : locations.card = d + 1)
    (p q : F[X]) (hp : p.degree ≤ (d : WithBot ℕ))
    (hq : q.degree ≤ (d : WithBot ℕ))
    (hagrees : ∀ x ∈ locations, p.eval x = q.eval x) : p = q := by
  by_contra hne
  have hdiff : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (p - q).degree ≤ (d : WithBot ℕ) := by
    exact (Polynomial.degree_sub_le p q).trans (max_le hp hq)
  have hroots : ∀ x ∈ locations, (p - q).eval x = 0 := by
    intro x hx
    rw [Polynomial.eval_sub, hagrees x hx, sub_self]
  have hcard_roots : (p - q).roots.toFinset.card ≤ d := by
    have h1 : (p - q).roots.toFinset.card ≤ (p - q).roots.card := Multiset.toFinset_card_le _
    have h2 : (p - q).roots.card ≤ (p - q).degree := Polynomial.card_roots hdiff
    have hchain : (↑(p - q).roots.card : WithBot ℕ) ≤ ↑d := h2.trans hdeg
    exact Nat.le_trans h1 (WithBot.coe_le_coe.mp hchain)
  have hsubset : locations ⊆ (p - q).roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots hdiff |>.mpr (hroots x hx))
  have hcard_le : locations.card ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsubset
  omega
