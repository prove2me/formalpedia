-- Prove2me | solution 1 for ShamirSecretSharing.degree_many_shares_do_not_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:04:31.937744+00:00
-- url     : https://prove2.me/submissions/36ddc8df-7fbd-4be2-9c8c-e6b41c0aaa7f

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
    (locations : Finset F) (d : ℕ) (hcard : locations.card = d)
    (hzero : 0 ∉ locations) :
    ∃ p q : F[X], p ≠ q ∧
      p.degree ≤ (d : WithBot ℕ) ∧ q.degree ≤ (d : WithBot ℕ) ∧
      (∀ x ∈ locations, p.eval x = q.eval x) ∧ p.eval 0 ≠ q.eval 0 := by
  -- Define p as the product of (X - x) for all x in locations
  let p : F[X] := locations.prod (fun x => Polynomial.X - Polynomial.C x)
  -- Use q = 0 as the other polynomial
  -- First show p.eval 0 ≠ 0
  have heval0 : p.eval 0 ≠ 0 := by
    simp [p, Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro x hx
    intro heq
    simp_all
  refine ⟨p, 0, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => heval0 <| h.symm ▸ by simp
  · -- p.degree ≤ d
    simp [p]
    have hdeg : ∀ x ∈ locations, (X - C x : F[X]).degree ≤ 1 := fun x _ => by simp
    refine le_trans (Polynomial.degree_prod_le _ _) ?_
    calc (∑ x ∈ locations, (X - C x : F[X]).degree)
        ≤ ∑ _x ∈ locations, (1 : WithBot ℕ) := Finset.sum_le_sum hdeg
      _ = locations.card := by simp
      _ = d := congrArg _ hcard
  · -- degree 0 ≤ d
    exact le_trans bot_le (WithBot.coe_le_coe.mpr (Nat.zero_le d))
  · -- ∀ x ∈ locations, p.eval x = 0
    intro x hx
    simp [p, Polynomial.eval_prod]
    rw [Finset.prod_eq_zero hx]
    simp
  · -- p.eval 0 ≠ 0
    simpa using heval0
