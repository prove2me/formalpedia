-- Prove2me | Theorems.Thm_invariant_subspace_problem
-- name    : invariant_subspace_problem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T19:14:21.57246+00:00
-- url     : https://prove2.me/theorems/73cae8f2-f0d4-4497-b8df-0aebeafed525
-- statement:
--   **Invariant Subspace Problem**: Does every bounded linear operator $T \neq 0$ on a separable infinite-dimensional complex Hilbert space have a non-trivial closed invariant subspace?
--
--   A closed subspace $\{0\} \subsetneq S \subsetneq H$ is invariant if $T(S) \subseteq S$. Known for compact operators (Lomonosov 1973), normal operators (spectral theorem), and operators on finite-dimensional spaces. Open for general bounded operators on $\ell^2(\mathbb{N})$.
--
--   **Source**: Halmos, P.R. (1970). Bulletin of the AMS 76(5), 887–933. DOI:10.1090/S0002-9904-1970-12504-2
-- source:
--   https://en.wikipedia.org/wiki/Invariant_subspace_problem

import Mathlib

theorem invariant_subspace_problem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (hinfty : ¬FiniteDimensional ℂ H)
    (T : H →L[ℂ] H) (hT : T ≠ 0) :
    ∃ S : Submodule ℂ H,
      S ≠ ⊥ ∧ S ≠ ⊤ ∧
      S ∈ Module.End.invtSubmodule (T : H →ₗ[ℂ] H) := by
  sorry
