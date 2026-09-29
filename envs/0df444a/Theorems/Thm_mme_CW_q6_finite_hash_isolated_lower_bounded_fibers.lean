-- Prove2me | Theorems.Thm_mme_CW_q6_finite_hash_isolated_lower_bounded_fibers
-- name    : mme_CW_q6_finite_hash_isolated_lower_bounded_fibers
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T20:19:58.672047+00:00
-- url     : https://prove2.me/theorems/0b5c4e8a-dd03-4448-8f6d-18b04ca54c4e
-- title:
--   Finite q=6 hash averaging yields isolated lower-bounded Z-fibers
-- statement:
--   There is a fixed positive integer $d$ governing the finite losses in the q=6 first hash. For a regular exact coupled profile, put\n\n$$\nZ=\binom{2N}{L}\binom{2N-L}{L},\qquad X=\binom NG,\qquad B=\binom{2G}{G},\qquad M=4X^2+1.\n$$\n\nFor every nonempty three-term-progression-free set $S\subseteq\{0,\ldots,\lfloor M/2\rfloor-1\}$, there are finite exact-address families $F\subseteq E$ and an integer $H>0$ with the following properties. Every address retained in $F$ is isolated, relative to all of the ambient hash bucket $E$, in both the X and Y modes. Every represented Z-address has degree at least $H$ in $F$. Supported mixing of three retained modes is closed inside $E$. Moreover, $H\le4^N$ and\n\n$$\nZ\,\frac{(|S|/M)^d}{(N+1)^d}\le |z(F)|,\qquad B\,\frac{(|S|/M)^d}{(N+1)^d}\le4X^2H.\n$$\n\nThis is the remaining quantitative finite step: dependent-weight averaging, X/Y collision deletion, and degree-threshold extraction. Exact common-$H$ truncation and enumeration into a primary family are separate proved theorems. In particular, this statement preserves shared Z multiplicity and makes no three-mode matching or tensor-factor identification claim.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--271: the q=6 exact-profile hash with M=4*choose(N,G)^2+1, Salem--Spencer retention, deletion of repeated X/Y blocks, and extraction of many positive-degree Z-blocks; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_exact_address_incidence
import Theorems.Thm_mme_3AP_free_no_collision

open MME

theorem mme_CW_q6_finite_hash_isolated_lower_bounded_fibers :
    ∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ E F : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              F ⊆ E ∧
              (∀ e ∈ F, ∀ e' ∈ E,
                (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
              (∀ c ∈ F.image (fun e => e.1 2),
                H ≤ (F.filter (fun e => e.1 2 = c)).card) ∧
              (∀ ex ∈ F, ∀ ey ∈ F, ∀ ez ∈ F,
                CWQ6CoupledCoordinatewiseSupported
                    (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
                  ∃ e' ∈ E,
                    e'.1 0 = ex.1 0 ∧
                    e'.1 1 = ey.1 1 ∧
                    e'.1 2 = ez.1 2) ∧
              H ≤ 4 ^ N ∧
              (Zcount : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                ((F.image (fun e => e.1 2)).card : ℝ) ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by sorry
