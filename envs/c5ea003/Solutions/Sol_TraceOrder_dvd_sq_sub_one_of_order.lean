-- Prove2me | solution 1 for TraceOrder.dvd_sq_sub_one_of_order
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:08:15.944213+00:00
-- url     : https://prove2.me/submissions/5ec0e302-bb03-4e38-9a63-1f1aa89a9f42

-- Sol generated from Applications/CyclicCubicTypeChannel/TraceOrder.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_CyclicCubicTypeChannel_TraceOrder
/-
# The Frobenius trace criterion for an arbitrary conductor

## Context (FACT round-32 #3, cycle 2)

`Applications.CyclicCubicTypeChannel.Splitting` settles conductor `7`: the cubic
`X³ + X² − 2X − 1` has a root mod `p` iff `p ≡ ±1 (mod 7)`.  The proof used one
structural fact — the companion matrix of `Y² − xY + 1` has order `7` exactly
when `x = ζ + ζ⁻¹` — which has nothing to do with `7`.

This file isolates that structure for an arbitrary odd prime conductor `m`,
using the Chebyshev-type coefficient sequence

  `A₀ = 0`, `A₁ = 1`, `A_{n+2}(t) = t·A_{n+1}(t) − A_n(t)`,

which satisfies `M^{n+1} = A_{n+1}(t)·M − A_n(t)·I` for every `2 × 2` matrix of
trace `t` and determinant `1`.  Main results:

* `TraceOrder.pow_eq_cheb` — the closed form for powers;
* `TraceOrder.companion_pow_of_matrix_pow` — *any* order-`m` element of
  `SL₂(𝔽_p)` that is not scalar transfers its order to the companion matrix of
  its trace;
* `TraceOrder.exists_companion_order_iff` — for odd primes `m ≠ p`:
  a companion matrix of order `m` exists over `𝔽_p` **iff** `p ≡ ±1 (mod m)`
  (in the form `m ∣ p² − 1`);
* `TraceOrder.cheb_root_iff` — the polynomial form: the pair
  `(A_m, A_{m−1}) = (0, −1)` is solvable over `𝔽_p` iff `m ∣ p² − 1`;
* `TraceOrder.golden_iff` — conductor `5`: `X² + X − 1` has a root mod `p` iff
  `p ≡ ±1 (mod 5)` (the golden-ratio / Fibonacci criterion);
* `TraceOrder.cubic_seven_iff` — conductor `7`: an independent second proof of
  `CyclicCubic.root_iff`, obtained by specialising the general criterion;
* `TraceOrder.quintic_eleven_iff` — conductor `11`: the quintic
  `X⁵ + X⁴ − 4X³ − 3X² + 3X + 1` (minimal polynomial of `ζ₁₁ + ζ₁₁⁻¹`) has a
  root mod `p` iff `p ≡ ±1 (mod 11)`.
-/

open Matrix

open TraceOrder

/-! ## Chebyshev-type coefficients -/



variable {R : Type*} [CommRing R]


/-! ## The companion matrix -/







/-! ## Transfer from an arbitrary matrix to a companion matrix -/


variable {K : Type*} [Field K]



/-! ## The order criterion over `𝔽_p` -/


variable (p : ℕ) [hp : Fact p.Prime]

private lemma card_GL_two_eq :
    Fintype.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]









/-! ## Explicit Chebyshev coefficients -/


variable {R : Type*} [CommRing R]








/-! ## Reading the criterion as a congruence -/





variable (p : ℕ) [hp : Fact p.Prime]


/-! ## Conductor 5: the golden-ratio criterion -/


/-! ## Conductor 7: an independent proof of the cyclic-cubic splitting law -/


/-! ## Conductor 11: the quintic criterion -/




open TraceOrder in
theorem solution{M : Matrix (Fin 2) (Fin 2) (ZMod p)} {m : ℕ}
    (hm : m.Prime) (hmp : m ≠ p) (hpow : M ^ m = 1) (hne : M ≠ 1) : m ∣ p ^ 2 - 1 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hm1 : 1 ≤ m := hm.one_lt.le
  let U : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ :=
    ⟨M, M ^ (m - 1), by
        rw [← pow_succ', Nat.sub_add_cancel hm1]
        exact hpow, by
        rw [← pow_succ]
        rwa [Nat.sub_add_cancel hm1]⟩
  have hUpow : U ^ m = 1 := Units.ext (by simpa using hpow)
  have hUne : U ≠ 1 := fun h => hne (congrArg Units.val h)
  have hord : orderOf U = m := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hm _ (orderOf_dvd_of_pow_eq_one hUpow)) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hUne
    · exact h
  have hdvd : m ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
    have hdc := orderOf_dvd_natCard (G := GL (Fin 2) (ZMod p)) U
    rwa [hord, Nat.card_eq_fintype_card, card_GL_two_eq p] at hdc
  rcases (Nat.Prime.dvd_mul hm).mp hdvd with h1 | h2
  · exact h1
  · have hfac : (p : ℕ) ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub, mul_one, sq]
    rw [hfac] at h2
    rcases (Nat.Prime.dvd_mul hm).mp h2 with hA | hB
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hm hp.out).mp hA) hmp
    · -- `m ∣ p − 1` also gives `m ∣ p² − 1 = (p−1)(p+1)`
      obtain ⟨k, hk⟩ := hB
      refine ⟨k * (p + 1), ?_⟩
      have hpp : p ^ 2 - 1 = (p - 1) * (p + 1) := by
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        have h1 : (q + 1) ^ 2 = q * (q + 1 + 1) + 1 := by ring
        rw [h1, Nat.add_sub_cancel, Nat.add_sub_cancel]
      rw [hpp, hk, mul_assoc]
