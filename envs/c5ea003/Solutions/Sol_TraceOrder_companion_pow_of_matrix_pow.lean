-- Prove2me | solution 1 for TraceOrder.companion_pow_of_matrix_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:27:36.777237+00:00
-- url     : https://prove2.me/submissions/917a50bb-09a8-4bc6-911f-f1efd13c44f2

-- Sol generated from Applications/CyclicCubicTypeChannel/TraceOrder.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_CyclicCubicTypeChannel_TraceOrder
import Theorems.Thm_CyclicCubic_cayley_two
import Theorems.Thm_CyclicCubic_pow_step
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


lemma chebA_succ_succ {R : Type*} [CommRing R] (t : R) (n : ℕ) :
    chebA t (n + 2) = t * chebA t (n + 1) - chebA t n := rfl

variable {R : Type*} [CommRing R]

/-- Powers of a trace-`t`, determinant-one `2 × 2` matrix. -/
theorem pow_eq_cheb {M : Matrix (Fin 2) (Fin 2) R} {t : R} (hM : M ^ 2 = t • M - 1) :
    ∀ n : ℕ, M ^ (n + 1) = chebA t (n + 1) • M - chebA t n • 1 := by
  intro n
  induction n with
  | zero => simp [chebA]
  | succ k ih =>
      have h := CyclicCubic.pow_step hM ih
      rw [h, chebA_succ_succ]
      congr 1
      congr 1
      ring

/-! ## The companion matrix -/







/-! ## Transfer from an arbitrary matrix to a companion matrix -/


variable {K : Type*} [Field K]



/-! ## The order criterion over `𝔽_p` -/


variable (p : ℕ) [hp : Fact p.Prime]










/-! ## Explicit Chebyshev coefficients -/


variable {R : Type*} [CommRing R]








/-! ## Reading the criterion as a congruence -/





variable (p : ℕ) [hp : Fact p.Prime]


/-! ## Conductor 5: the golden-ratio criterion -/


/-! ## Conductor 7: an independent proof of the cyclic-cubic splitting law -/


/-! ## Conductor 11: the quintic criterion -/




open TraceOrder in
theorem solution{M : Matrix (Fin 2) (Fin 2) K} {n : ℕ}
    (hdet : M.det = 1) (hpow : M ^ (n + 1) = 1)
    (hns : ∀ c : K, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    chebA M.trace (n + 1) = 0 ∧ chebA M.trace n = -1 := by
  have hM2 : M ^ 2 = M.trace • M - 1 := by rw [CyclicCubic.cayley_two M, hdet, one_smul]
  have hkey := pow_eq_cheb hM2 n
  rw [hpow] at hkey
  by_cases h0 : chebA M.trace (n + 1) = 0
  · refine ⟨h0, ?_⟩
    rw [h0, zero_smul, zero_sub] at hkey
    have h11 : (1 : K) = -(chebA M.trace n) := by
      have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => N 0 0) hkey
      simpa [Matrix.one_apply] using h
    linear_combination h11
  · exfalso
    have hscal : (chebA M.trace (n + 1)) • M
        = (1 + chebA M.trace n) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      linear_combination (norm := module) -hkey
    have hMc : M = ((chebA M.trace (n + 1))⁻¹ * (1 + chebA M.trace n))
        • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h2 := congrArg (fun N => (chebA M.trace (n + 1))⁻¹ • N) hscal
      simpa [smul_smul, inv_mul_cancel₀ h0] using h2
    exact hns _ hMc
