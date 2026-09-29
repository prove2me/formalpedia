-- Prove2me | Theorems.Thm_input_valuation_equidistribution
-- name    : input_valuation_equidistribution
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-29T00:02:51.709704+00:00
-- url     : https://prove2.me/theorems/cf32ac58-dc23-436e-874f-578f99027eea
-- title:
--   Tao Proposition 1.9 (elementary residue form): valuation-vector equidistribution
-- statement:
--   Child decomposition node for `syracuse_first_passage_finite_tail_bound` (b179e2a6-29fd-4151-8b97-35fd2e1bb5a1) in the tao-collatz mission; it is the deepest input used in the Section 5 proof of Tao 2022 Proposition 1.11 estimate (1.19), which is itself the finite-time input to Theorem 3.1. Tao 2022, Proposition 1.9 in elementary residue form, used at (5.4): for `n_0 >= 1`, every valuation vector `a` of length `n_0` with all entries at least 1 and total sum at most `m` occurs for exactly `2^(m - sum a)` odd residues modulo `2^m`. Proof (Terras): `nu_2(3r+1) = a_1` pins `a_1` bits of `r` (3 is invertible modulo `2^a_1`); then `Syr(r)` modulo `2^{m-a_1}` is determined and `a_2` pins `a_2` more bits; inductively `sum a` bits are pinned, leaving `2^(m - sum a)` residues.

import Mathlib
import Definitions.Def_syracuseOrbitMin

noncomputable section


attribute [instance] Classical.propDecidable

/-- The 2-adic valuation of `3n+1` (Tao 2022, section 1.2). -/
def syrVal (n : ℕ) : ℕ := Nat.factorization (3 * n + 1) 2

/-- The Syracuse valuation vector of length `n₀` (Tao 2022, (1.8)). -/
def valVec (n₀ : ℕ) (n : ℕ) : Fin n₀ → ℕ := fun j => syrVal (syracuseStep^[j.val] n)

/-- The valuation-vector sum (Tao 2022, (1.4)). -/
def valSum (n₀ n : ℕ) : ℕ := Finset.sum Finset.univ (fun j => valVec n₀ n j)

theorem input_valuation_equidistribution :
    ∀ n₀ m : ℕ, 1 ≤ n₀ → ∀ ā : Fin n₀ → ℕ, (∀ j, 1 ≤ ā j) →
      Finset.sum Finset.univ (fun j => ā j) ≤ m →
      (Finset.filter (fun r => Odd r ∧ valVec n₀ r = ā) (Finset.range (2 ^ m))).card
        = 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) := by sorry
