-- Prove2me | Theorems.Thm_mme_CW_q6_finite_affine_hash_isolated_residual_mass
-- name    : mme_CW_q6_finite_affine_hash_isolated_residual_mass
-- status  : Disproved
-- author  : @marwahaha
-- created : 2026-08-24T20:33:50.382073+00:00
-- url     : https://prove2.me/theorems/194670e6-78e9-4499-bca8-dff5b0203b9d
-- title:
--   Finite affine q=6 hash leaves isolated residual Z-mass
-- statement:
--   There is a universal positive loss exponent $d$ for the following finite q=6 affine-hash construction. For the regular exact profile, write\n\n$$\nZ=\binom{2N}{L}\binom{2N-L}{L},\quad X=\binom NG,\quad B=\binom{2G}{G},\quad M=4X^2+1,\quad \rho=\frac{(|S|/M)^d}{(N+1)^d}.\n$$\n\nFor every nonempty lower-half three-term-progression-free set $S$, there are an ambient hash bucket $E$, an X/Y-isolated subfamily $I\subseteq E$, and $H>0$. Every Z-fiber of $I$ has size at most $B$, supported mixing of retained modes closes in $E$, and\n\n$$\nH\le4^N,\qquad B\rho\le4X^2H,\qquad H|z(I)|+BZ\rho\le|I|.\n$$\n\nThe last inequality is a residual-mass form of the dependent-weight averaging and ordered X/Y collision estimate: after reserving $H$ elements for each represented Z-label, enough isolated edge mass remains to force at least $Z\rho$ labels through deterministic degree-thresholding. That thresholding and exact common-$H$ truncation are separate proved lemmas. The statement keeps shared Z multiplicity and does not assert three-mode isolation or any tensor-factor identification.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--271: affine hashing modulo M=4*choose(N,G)^2+1, Salem--Spencer retention, expected collision deletion, and the residual edge count used for common-degree C-tensor extraction; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_exact_address_incidence
import Theorems.Thm_mme_3AP_free_no_collision

open MME

theorem mme_CW_q6_finite_affine_hash_isolated_residual_mass :
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
          ∃ E I : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              I ⊆ E ∧
              (∀ e ∈ I, ∀ e' ∈ E,
                (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
              (∀ c ∈ I.image (fun e => e.1 2),
                (I.filter (fun e => e.1 2 = c)).card ≤ middle) ∧
              (∀ ex ∈ I, ∀ ey ∈ I, ∀ ez ∈ I,
                CWQ6CoupledCoordinatewiseSupported
                    (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
                  ∃ e' ∈ E,
                    e'.1 0 = ex.1 0 ∧
                    e'.1 1 = ey.1 1 ∧
                    e'.1 2 = ez.1 2) ∧
              H ≤ 4 ^ N ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
              (H : ℝ) *
                    ((I.image (fun e => e.1 2)).card : ℝ) +
                  (middle : ℝ) *
                    ((Zcount : ℝ) *
                      ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                        (((N + 1 : ℕ) : ℝ) ^ d))) ≤
                (I.card : ℝ) := by sorry
