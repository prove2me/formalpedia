-- Prove2me | solution 1 for search_to_decision_advantage_bound
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:45:58.360195+00:00
-- url     : https://prove2.me/submissions/312358b8-9741-4846-8ee3-2932681969bc

-- Thm stub generated from Cryptography/LWE/SearchDecisionCore.lean
import Mathlib
import Definitions.Def_Cryptography_LWE_SearchDecisionCore

/-!
# LWE Search-to-Decision Reduction: Algebraic Core

This module formalizes the key algebraic and analytic ingredients underlying
the search-to-decision reduction for the Learning with Errors problem.

## Mathematical Background

The LWE search-to-decision reduction (Regev 2005, Peikert 2009) reduces
distinguishing LWE samples from uniform to recovering the secret vector.
The reduction proceeds coordinate-by-coordinate: for prime modulus q,
one can guess each coordinate of the secret and verify correctness using
the algebraic structure of ℤ_q as a field.

The core algebraic fact is that for prime q, affine maps x ↦ ax + b
are bijections on ℤ_q when a ≠ 0. This ensures that rerandomizing an
LWE sample by an affine transformation preserves uniformity on the
"wrong guess" side of the hybrid argument.

## Main Results

1. `ZMod.affine_bijective` — Affine maps are bijections over ℤ_p (p prime)
2. `noise_accumulation_bound` — Accumulated noise from m LWE samples ≤ mB
3. `regev_rounding_bit1` — Rounding-based decryption works when |e| < q/4
4. `search_to_decision_advantage_bound` — Advantage loss factor of n

## References

* Regev, "On Lattices, Learning with Errors, Random Linear Codes,
  and Cryptography", STOC 2005 / JACM 2009
* Peikert, "Public-Key Cryptosystems from the Worst-Case Shortest
  Vector Problem", STOC 2009
-/

open Finset BigOperators Real

noncomputable section

/-! ## Section 1: Affine Bijections over ℤ_p -/

-- !-- The key algebraic fact: for prime p, multiplication by a nonzero
-- element is injective (hence bijective on a finite type). This is
-- because ℤ_p is a field when p is prime. Combined with the bijection
-- of translation, affine maps are bijections. -- !--




/-
**The inverse of an affine map is affine**.
If f(x) = ax + b, then f⁻¹(y) = a⁻¹(y - b).
-/




/-! ## Section 2: Noise Accumulation Bounds -/

-- !-- In Regev's encryption, ciphertext noise = subset sum of LWE errors.
-- The accumulated noise is bounded by (subset size) × (per-sample bound). -- !--




/-! ## Section 3: Regev Encryption Rounding Correctness -/

-- !-- Regev's encryption encodes bit μ ∈ {0,1} as μ · (q/2).
-- Decryption checks which "half" of [0,q) the noisy value falls in.
-- Correctness requires accumulated noise |e| < q/4. -- !--





/-! ## Section 4: Search-to-Decision Advantage Bound -/

-- !-- The search-to-decision reduction decomposes total advantage δ
-- into n coordinate contributions via a hybrid argument. By pigeonhole,
-- at least one coordinate contributes ≥ δ/n. -- !--

theorem solution (n : ℕ) (hn : 0 < n)
    (δ : ℝ)
    (coordAdvantage : Fin n → ℝ)
    (htotal : δ ≤ ∑ i, coordAdvantage i) :
    ∃ i : Fin n, δ / ↑n ≤ coordAdvantage i := by
  by_contra h
  push_neg at h
  have : ∑ i, coordAdvantage i < ∑ _i : Fin n, δ / ↑n :=
    Finset.sum_lt_sum (fun i _ => le_of_lt (h i)) ⟨⟨0, hn⟩, Finset.mem_univ _, h ⟨0, hn⟩⟩
  simp [Finset.sum_const, nsmul_eq_mul] at this
  rw [mul_div_cancel₀ δ (Nat.cast_ne_zero.mpr (by omega))] at this
  linarith

#print axioms solution
