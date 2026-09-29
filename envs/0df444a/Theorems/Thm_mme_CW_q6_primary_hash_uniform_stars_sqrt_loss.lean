-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
-- name    : mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:06:33.750314+00:00
-- url     : https://prove2.me/theorems/357cf4eb-97a9-416c-8157-1a1a39a190e5
-- title:
--   Uniform q=6 primary hash stars with a fixed square-root loss
-- statement:
--   Let $L_N,G_N$ be any integer profile sequences. There is a fixed constant $C ≥ 0$ such that, for all sufficiently large $N$ satisfying $L_N>0$, $L_N+G_N=N$, and $341L_N<100G_N$, the exact coupled q=6 profile hypergraph contains an induced family of $A$ uniform stars of a common positive size $H$. Its outer and middle counts satisfy
--
--   $$Z_N e^{-C sqrt(N+1)} ≤ A,$$
--
--   $$B_N e^{-C sqrt(N+1)} ≤ 4 X_N^2 H,$$
--
--   with $H≤4^N$, where $Z_N=choose(2N,L_N)choose(2N-L_N,L_N)$, $X_N=choose(N,G_N)$, and $B_N=choose(2G_N,G_N)$. The family has globally distinct first- and second-mode words, one shared third-mode word inside each star, distinct third-mode words between stars, and no unintended supported mixed address.
--
--   This is the rigorous finite form of the first Salem-Spencer hashing, X/Y collision deletion, and uniform C-tensor fiber extraction on CW90 p. 271. The unspecified universal constant records the explicit Behrend, finite pruning, and degree-uniformization losses without inventing an unsupported numerical coefficient.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270–271: fixed X/Y degree choose(L+G,G)^2, Z degree choose(2G,G), modulus M=4*choose(L+G,G)^2+1, Salem-Spencer hashing, collision deletion, and the displayed asymptotic H; https://doi.org/10.1016/S0747-7171(08)80013-2. Explicit finite Behrend density: Prove2Me theorem cb45e6ba-b86a-4119-a08e-f162c8fbc86b.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME Filter Topology

theorem mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
    (L G : ℕ → ℕ) :
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
