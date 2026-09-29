-- Prove2me | solution 1 for FactoringLab.polynomial_barrier_counting
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:38:41.884923+00:00
-- url     : https://prove2.me/submissions/9d4d6e2b-f3a4-4c04-85a1-e74f6b19d29a

-- Sol generated from Probability/FactoringBarriers.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
/-
# Barriers I: the polynomial barrier, rational escape, holomorphic rigidity

Three of the eight barriers of the Factoring Lab framework, proved.

* `FactoringLab.polynomial_barrier` — no polynomial with rational coefficients
  computes the smaller prime factor of a semiprime.
* `FactoringLab.rational_escape_illusory` (WWW) — the same for *rational
  functions* `A/B`: passing from polynomials to quotients buys nothing.
* `FactoringLab.algebraic_barrier` — the strongest form: *no* nonzero
  polynomial relation `F(N, p) = 0` in two variables over `ℚ` holds for all
  semiprimes.  The polynomial and rational barriers are special cases.
* `FactoringLab.polynomial_barrier_counting` — a quantitative version: for a
  fixed small factor `p`, a polynomial of degree `d` can return the correct
  factor at no more than `d` semiprimes `pq`.
* `FactoringLab.holomorphic_rigidity` / `holomorphic_rigidity_barrier` (HRB) —
  an entire function that reproduces the reciprocal of the smaller prime factor
  at the reciprocals of semiprimes is forced by the identity theorem to be
  constant, which is impossible.

The proofs share one mechanism: fixing the small factor makes the sample set
accumulate (at infinity for polynomials, at `0` for the holomorphic version),
and rigidity of the function class then forces a constant, which two different
choices of the small factor contradict.
-/

open FactoringLab

open Polynomial Filter Set

/-! ### Arithmetic input: infinitely many primes above any bound -/



/-! ### The polynomial and rational barriers -/




/-! ### The algebraic barrier: no algebraic relation between `N` and `p` -/




/-! ### Holomorphic rigidity -/










open FactoringLab in
theorem solution(P : Polynomial ℚ) {p : ℕ} (hp : p.Prime)
    (hne : P ≠ Polynomial.C (p : ℚ)) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ p < q ∧ P.eval ((p * q : ℕ) : ℚ) = (p : ℚ)) :
    S.card ≤ P.natDegree := by
  set G : Polynomial ℚ := P - Polynomial.C (p : ℚ) with hG
  have hG0 : G ≠ 0 := sub_ne_zero.2 hne
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hmap : ∀ q ∈ S, ((p : ℚ) * (q : ℚ)) ∈ G.roots.toFinset := by
    intro q hq
    obtain ⟨-, -, hval⟩ := hS q hq
    have hx : ((p * q : ℕ) : ℚ) = (p : ℚ) * (q : ℚ) := by push_cast; ring
    rw [hx] at hval
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hG0]
    simp only [hG, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C, hval,
      sub_self]
  have hinj : ∀ a ∈ S, ∀ b ∈ S, (p : ℚ) * (a : ℚ) = (p : ℚ) * (b : ℚ) → a = b := by
    intro a _ b _ hab
    have : (a : ℚ) = b := mul_left_cancel₀ hpne hab
    exact_mod_cast this
  calc S.card ≤ G.roots.toFinset.card :=
        Finset.card_le_card_of_injOn (fun q => (p : ℚ) * (q : ℚ)) hmap hinj
    _ ≤ Multiset.card G.roots := G.roots.toFinset_card_le
    _ ≤ G.natDegree := G.card_roots'
    _ = P.natDegree := by rw [hG, Polynomial.natDegree_sub_C]
