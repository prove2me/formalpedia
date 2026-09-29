-- Prove2me | Theorems.Thm_mme_CW_q6_finite_affine_hash_raw_collision_budget
-- name    : mme_CW_q6_finite_affine_hash_raw_collision_budget
-- status  : Disproved
-- author  : @marwahaha
-- created : 2026-08-24T20:40:16.439633+00:00
-- url     : https://prove2.me/theorems/aa6f2114-c3c3-423a-8ea5-e2aefc830838
-- title:
--   Raw q=6 affine bucket pays its ordered X/Y collision budget
-- statement:
--   There is a universal positive exponent $d$ such that the finite affine q=6 hash has the following raw-bucket form. Put\n\n$$\nZ=\binom{2N}{L}\binom{2N-L}{L},\quad X=\binom NG,\quad B=\binom{2G}{G},\quad M=4X^2+1,\quad \rho=\frac{(|S|/M)^d}{(N+1)^d}.\n$$\n\nFor every nonempty lower-half three-term-progression-free set $S$, there are a finite exact-address bucket $E$ and $H>0$. Its represented Z-label count is at most $Z$, every Z-fiber has size at most $B$, and supported mixing of three bucket modes is closed inside $E$. Let\n\n$$\nC=\{(e,e')\in E^2:e\ne e',\ x(e)=x(e')\text{ or }y(e)=y(e')\}\n$$\n\nbe the explicit ordered X/Y collision set. Then\n\n$$\nH\le4^N,\qquad B\rho\le4X^2H,\qquad HZ+BZ\rho+|C|\le|E|.\n$$\n\nThus the affine-hash averaging leaves enough raw edge mass to delete every edge participating in an ordered X/Y collision and still retain both the baseline $H$ mass per possible Z-label and the normalized residual $BZ\rho$. Collision deletion, degree thresholding, and exact common-fiber truncation are separate proved deterministic steps. No Z-collision is deleted and no tensor realization is asserted.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--271: affine q=6 hashing modulo M=4*choose(N,G)^2+1, dependent-weight averaging, and the ordered repeated-X/Y-block collision estimate paid before C-tensor degree extraction; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_exact_address_incidence
import Theorems.Thm_mme_3AP_free_no_collision

open MME

noncomputable local instance q6ExactAddressDecidableEq (N L G : ℕ) :
    DecidableEq (CWQ6ExactCoupledAddress N L G) := Classical.decEq _

theorem mme_CW_q6_finite_affine_hash_raw_collision_budget :
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
          ∃ E : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              (E.image (fun e => e.1 2)).card ≤ Zcount ∧
              (∀ c ∈ E.image (fun e => e.1 2),
                (E.filter (fun e => e.1 2 = c)).card ≤ middle) ∧
              (∀ ex ∈ E, ∀ ey ∈ E, ∀ ez ∈ E,
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
              (H : ℝ) * (Zcount : ℝ) +
                    (middle : ℝ) *
                      ((Zcount : ℝ) *
                        ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                          (((N + 1 : ℕ) : ℝ) ^ d))) +
                    (((E.product E).filter (fun p =>
                      p.1 ≠ p.2 ∧
                        (p.1.1 0 = p.2.1 0 ∨
                          p.1.1 1 = p.2.1 1))).card : ℝ) ≤
                (E.card : ℝ) := by sorry
