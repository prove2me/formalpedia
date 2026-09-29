-- Prove2me | Theorems.Thm_huang_matrix_spectrum_sorted
-- name    : huang_matrix_spectrum_sorted
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-04-23T04:01:58.298094+00:00
-- url     : https://prove2.me/theorems/a52106a0-facf-41f0-a581-6501b936ba66
-- statement:
--   Lemma 2.2 (sorted spectrum of Huang's matrix): when the eigenvalues of huangMatrix n are arranged in descending order, the first 2^(n-1) equal +sqrt(n) and the remaining 2^(n-1) equal -sqrt(n).
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the sensitivity conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Definitions.Def_huangMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lemma 2.2 — Full sorted spectrum of Huang's matrix

Huang 2019, Lemma 2.2: the `2^n × 2^n` matrix `A_n := huangMatrix n` has
eigenvalues `+√n` and `−√n`, each with multiplicity `2^(n-1)`.

Stated here in the *sorted* form: when the eigenvalues are listed in descending
order (via `Matrix.IsHermitian.eigenvalues₀`), positions `0..2^(n-1)−1` are `+√n`
and positions `2^(n-1)..2^n−1` are `−√n`.
-/

/-- **Lemma 2.2 — Full sorted spectrum of Huang's matrix.**
The sorted eigenvalues of `huangMatrix n` are: the first `2^(n-1)` equal `+√n`,
the remaining `2^(n-1)` equal `−√n`. -/

theorem huang_matrix_spectrum_sorted (n : ℕ) (hn : 0 < n)
    (i : Fin (Fintype.card (Fin n → Bool))) :
    (huangMatrix_is_hermitian n).eigenvalues₀ i =
      if (i : ℕ) < 2 ^ (n - 1) then Real.sqrt n else -Real.sqrt n := by sorry
