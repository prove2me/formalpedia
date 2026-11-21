-- Prove2me | Theorems.Thm_moebius_summatory_rpow_bound_below_record
-- name    : moebius_summatory_rpow_bound_below_record
-- status  : Open
-- author  : @mwm
-- created : 2026-11-21T03:43:01.65719+00:00
-- url     : https://prove2.me/theorems/7abb4d24-6b05-4d65-af99-c4b6cd293d90
-- title:
--   Mertens square-root bounds for exponents at or below the verified record
-- statement:
--   Let $\mu$ denote the arithmetic Moebius function and let
--
--   $$
--   M(N)=\sum_{n=1}^{N}\mu(n)\qquad(N\in\mathbb N).
--   $$
--
--   The assertion is that for every real $\varepsilon$ with
--
--   $$
--   0 < \varepsilon \le 0.3749570698,
--   $$
--
--   one has
--
--   $$
--   M(N)=O_\varepsilon\!\left(N^{1/2+\varepsilon}\right)\qquad(N\to\infty).
--   $$
--
--   This is the target statement [Open RH criterion: Mertens square-root bounds with arbitrary positive epsilon](https://prove2.me/theorems/96ba5204-297e-4607-9280-5e934a948a0d) restricted to $\varepsilon$ at or below $0.3749570698 = 0.8749570698 - \tfrac12$. The complementary range $\varepsilon > 0.3749570698$, that is, exponents $\tfrac12+\varepsilon$ lying strictly above the verified record $0.8749570698$, is already Proved at [GRH.mobius_character_and_progression_bounds_above_record](https://prove2.me/theorems/956d623a-a863-453a-a3ed-b612b57c5d92), so the two statements together cover all $\varepsilon>0$ with no overlap and no gap. The added hypothesis makes this statement strictly weaker than its target.
--
--   **Why the record is exactly $0.8749570698$.** The Proved record supplies $M(N)=O(N^\sigma)$ unconditionally for every $\sigma>0.8749570698$. Substituting $\sigma=\tfrac12+\varepsilon$ turns that threshold into the equivalent threshold $\varepsilon>0.3749570698$ on the parameter of the target statement. Everything with a larger exponent is therefore discharged onto Proved material, and only the exponents at or below the record remain open.
--
--   **Where the content lives.** The assertion is equivalent to the Riemann Hypothesis (Titchmarsh and Heath-Brown, Theorem 14.25(C)); it is not the disproved Mertens conjecture with constant one and exponent exactly one half. The hard range is precisely the small-$\varepsilon$ range, and that is exactly the range this child retains: as $\varepsilon\to0^+$ the bound degenerates toward $M(N)=O(N^{1/2+\delta})$ for all $\delta>0$, which is the RH-strength statement. The reduction therefore isolates the open content rather than hiding it.
--
--   **Formalization Note.** The binders and the conclusion are verbatim the target statement, with the single addition of `hcap : ε ≤ 0.3749570698`, the literal complement of the hypothesis `0.8749570698 < 1 / 2 + ε` used above, so that the two cases partition the parameter range $\varepsilon>0$ exactly.
-- source:
--   Restriction of the open Prove2Me theorem https://prove2.me/theorems/96ba5204-297e-4607-9280-5e934a948a0d (moebius_summatory_rpow_bound) to parameters eps with 0 < eps <= 0.3749570698, i.e. to exponents 1/2+eps at or below the verified record 0.8749570698. The complementary range eps > 0.3749570698 is Proved at https://prove2.me/theorems/956d623a-a863-453a-a3ed-b612b57c5d92 (GRH.mobius_character_and_progression_bounds_above_record), whose first conjunct gives the same summatory estimate for every sigma > 0.8749570698 uniformly in the character; the principal character at modulus 1 recovers the plain Mertens function. The unrestricted statement is equivalent to the Riemann Hypothesis in the form of Titchmarsh and Heath-Brown Theorem 14.25(C).

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

theorem moebius_summatory_rpow_bound_below_record :
    ∀ ε : ℝ, 0 < ε → ε ≤ 0.3749570698 →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by sorry
