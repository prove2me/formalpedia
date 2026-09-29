-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_bucket_collision_budget_averaging
-- name    : mme_CW_q6_primary_hash_bucket_collision_budget_averaging
-- status  : Disproved
-- author  : @marwahaha
-- created : 2026-08-24T20:54:14.066526+00:00
-- url     : https://prove2.me/theorems/fa9f14f3-dcf5-49eb-ad39-2663ba3997a1
-- title:
--   Affine q=6 averaging finds a bucket above its X/Y collision budget
-- statement:
--   There is a universal positive exponent $d$ such that one can choose the offset and weight vector of the literal q=6 affine hash with a favorable simultaneous edge/collision count. Write\n\n$$\nZ=\binom{2N}{L}\binom{2N-L}{L},\quad X=\binom NG,\quad B=\binom{2G}{G},\quad M=4X^2+1,\quad \rho=\frac{(|S|/M)^d}{(N+1)^d}.\n$$\n\nFor every nonempty lower-half three-term-progression-free set $S$, there are affine parameters $(b_0,w)$ and an integer $H>0$. If $E$ is their literal common-label bucket and\n\n$$\nC(E)=\{(e,e')\in E^2:e\ne e',\ x(e)=x(e')\text{ or }y(e)=y(e')\},\n$$\n\nthen\n\n$$\nH\le4^N,\qquad B\rho\le4X^2H,\qquad HZ+BZ\rho+|C(E)|\le|E|.\n$$\n\nThis is the remaining finite dependent-weight expectation inequality. It must average the raw retained edge mass and the ordered X/Y collision count over the same affine parameters. The literal bucket's Z-count, fiber-degree, and supported-mix closure properties are established separately. The statement never deletes Z-collisions and contains no tensor realization.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--271: dependent averaging over affine q=6 hash parameters, modulus M=4*choose(N,G)^2+1, retained edge expectation, and ordered repeated-X/Y-block collision estimate; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_primary_hash_bucket
import Theorems.Thm_mme_3AP_free_no_collision

open MME

noncomputable local instance q6BucketAveragingExactAddressDecidableEq
    (N L G : ℕ) : DecidableEq (CWQ6ExactCoupledAddress N L G) :=
  Classical.decEq _

theorem mme_CW_q6_primary_hash_bucket_collision_budget_averaging :
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
          ∃ b0 : ZMod Mmod,
            ∃ w : Fin (2 * N) → ZMod Mmod,
              ∃ H : ℕ,
                let E := cwQ6PrimaryHashBucket N L G Xcount S b0 w
                0 < H ∧
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
