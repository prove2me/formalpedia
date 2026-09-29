-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_of_regularity
-- name    : mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_of_regularity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:13:26.134356+00:00
-- url     : https://prove2.me/theorems/6bb925ce-09b4-4fb2-b345-3062f46f293d
-- title:
--   Finite Salem–Spencer star extraction from exact q=6 profile regularity
-- statement:
--   Suppose the exact q=6 profile incidence hypergraph has the CW90 regularity counts at every balanced profile in two integer sequences $L_N,G_N$. Then one fixed constant $C≥0$ suffices so that, eventually and whenever $341L_N<100G_N$, Salem–Spencer hashing and collision pruning produce an induced family of uniform positive Z-centered stars with
--
--   $$Z_N e^{-C sqrt(N+1)} ≤ A,$$
--
--   $$B_N e^{-C sqrt(N+1)} ≤ 4X_N^2H,$$
--
--   and $H≤4^N$.
--
--   This theorem isolates the genuine finite hashing work: modular arithmetic-progression control, the dependent-weight count, X/Y collision deletion, and extraction of one common star size while retaining enough outer fibers. It assumes the exact incidence enumeration explicitly and makes no tensor-realization claim.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270–271: M=4*choose(L+G,G)^2+1, Salem–Spencer hashing, X/Y collision deletion, and the asymptotic common-H estimate; https://doi.org/10.1016/S0747-7171(08)80013-2. The fixed square-root envelope records explicit finite Behrend and polynomial pruning losses.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_q6_exact_address_incidence

open MME Filter Topology

theorem mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_of_regularity
    (L G : ℕ → ℕ)
    (hregular : ∀ N : ℕ, L N + G N = N →
      CWQ6ExactAddressRegularity N (L N) (G N)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        let Zcount : ℕ :=
          Nat.choose (2 * N) (L N) *
            Nat.choose (2 * N - L N) (L N)
        let Xcount : ℕ := Nat.choose N (G N)
        let middle : ℕ := Nat.choose (2 * G N) (G N)
        (0 < L N ∧ L N + G N = N ∧ 341 * L N < 100 * G N) →
        ∃ A H : ℕ,
          ∃ family : CWQ6PrimaryHashFamily N (L N) (G N) A H,
            H ≤ 4 ^ N ∧
            (Zcount : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (A : ℝ) ∧
            (middle : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by sorry
