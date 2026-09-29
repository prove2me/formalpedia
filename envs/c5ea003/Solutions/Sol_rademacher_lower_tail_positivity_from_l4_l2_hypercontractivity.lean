-- Prove2me | solution 1 for rademacher_lower_tail_positivity_from_l4_l2_hypercontractivity
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T05:06:56.015146+00:00
-- url     : https://prove2.me/submissions/f3fb1777-8797-4fa1-8eb6-1f02d44325a0

import Theorems.Thm_rademacher_l2_le_l1_of_l4_le_l2sq
import Theorems.Thm_rademacher_paley_zygmund_meanzero_positivity
import Mathlib.Algebra.Order.Field.Basic
open MatrixCompletion
open scoped Classical BigOperators

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211), Lemma 2 (real-valued case),
the lower-bound assembly  P(F ≥ 0) ≥ c⁻¹, stated on the SYMMETRIC Rademacher (±1)
fiber `rademacherExpectation` (uniform `(1/2)^N` weights on sign assignments).

This is the conditional Lemma 2 (eq. (6), p.4) CONTENT on the σ-sign Rademacher
fiber: for a real mean-zero sign-chaos statistic F with hypercontractive control
`E[F⁴] ≤ K(E F²)²`, the diagonal chaos survives a fixed fraction of the mass:
  P(F ≥ 0) ≥ 1/(4K),
with P(F ≥ 0) = E[1_{F ≥ 0}] on the uniform sign measure.  de la Peña's proof
composes exactly two ingredients:

  • the L4→L2→L1 moment transfer (Lemma 2, "‖ξ‖₄ ≤ σ⁻²‖ξ‖₂ ⟹ ‖ξ‖₂ ≤ σ⁻⁴‖ξ‖₁"),
    here  E[F⁴] ≤ K(E F²)²  ⟹  E[F²] ≤ K(E|F|)²   (the brick
    `rademacher_l2_le_l1_of_l4_le_l2sq`), and
  • Proposition 1 (Paley–Zygmund positivity),  (E|F|)² ≤ 4 E[F²]·E[1_{F≥0}]
    (the brick `rademacher_paley_zygmund_meanzero_positivity`).

Chaining them:
    E[F²] ≤ K(E|F|)² ≤ K·4 E[F²]·E[1_{F≥0}] = 4K·E[F²]·E[1_{F≥0}].
Dividing by E[F²] > 0 gives  1 ≤ 4K·E[1_{F≥0}], i.e.  E[1_{F≥0}] ≥ 1/(4K).

Rademacher-fiber analogue of `bernoulli_lower_tail_positivity_from_l4_l2_
hypercontractivity` (2edc63a6), MORE source-faithful: dlP–MS Lemma 2 / the
Paley–Zygmund lower tail is the classical ±1-cube tool.  The L4↔L2 hypercontractivity
`E[F⁴] ≤ K(E F²)²` is taken as a HYPOTHESIS; for degree-≤2 sign chaos it is exactly
the Bonami inequality K = 9² (`rademacher_bilinear_chaos_l4_l2_bonami_
hypercontractivity` / `BonamiCube.bonami`, ddd7e198).  Cite dlP–MS 1995 Lemma 2 +
Bonami 1970 / O'Donnell "Analysis of Boolean Functions" Ch. 9.
-/

theorem solution
    {n₁ n₂ : ℕ} (K : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    0 < K →
    rademacherExpectation F = 0 →
    0 < rademacherExpectation (fun ε => (F ε) ^ 2) →
    rademacherExpectation (fun ε => (F ε) ^ 4) ≤
        K * (rademacherExpectation (fun ε => (F ε) ^ 2)) ^ 2 →
    (1 : ℝ) / (4 * K) ≤
      rademacherExpectation (fun ε => if 0 ≤ F ε then (1 : ℝ) else 0) := by
  intro hK hmean hvar hHC
  set b : ℝ := rademacherExpectation (fun ε => (F ε) ^ 2) with hb
  set a : ℝ := rademacherExpectation (fun ε => |F ε|) with ha
  set P : ℝ := rademacherExpectation (fun ε => if 0 ≤ F ε then (1 : ℝ) else 0) with hP
  -- L4 → L2 → L1 transfer (brick rademacher_l2_le_l1_of_l4_le_l2sq):  b ≤ K · a²
  have hTransfer : b ≤ K * a ^ 2 := by
    have := rademacher_l2_le_l1_of_l4_le_l2sq K F (le_of_lt hK) hHC
    simpa [hb, ha] using this
  -- Paley–Zygmund positivity (brick rademacher_paley_zygmund...):  a² ≤ 4 · b · P
  have hPZ : a ^ 2 ≤ 4 * b * P := by
    have := rademacher_paley_zygmund_meanzero_positivity F hmean
    simpa [ha, hb, hP] using this
  -- chain:  b ≤ K·a² ≤ K·(4·b·P) = 4K·b·P
  have hchain : b ≤ 4 * K * b * P := by
    calc b ≤ K * a ^ 2 := hTransfer
      _ ≤ K * (4 * b * P) := by
            apply mul_le_mul_of_nonneg_left hPZ (le_of_lt hK)
      _ = 4 * K * b * P := by ring
  have h4Kpos : (0 : ℝ) < 4 * K := by linarith
  have hone : (1 : ℝ) ≤ 4 * K * P := by
    have hb' : b * 1 ≤ b * (4 * K * P) := by
      have : b ≤ b * (4 * K * P) := by
        calc b ≤ 4 * K * b * P := hchain
          _ = b * (4 * K * P) := by ring
      simpa using this
    exact le_of_mul_le_mul_left (by simpa using hb') hvar
  rw [div_le_iff₀ h4Kpos]
  linarith [hone]
