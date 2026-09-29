-- Prove2me | Theorems.Thm_SingularModuli_factor_77
-- name    : SingularModuli.factor_77
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:08:32.200648+00:00
-- url     : https://prove2.me/theorems/fca2c129-07c8-4f7b-9791-b2c57977bf41
-- title:
--   `N = 77 = 7 · 11` with the class-number-2 polynomial `H_{-15}` at `j₀ = 0`:
-- statement:
--   `N = 77 = 7 · 11` with the class-number-2 polynomial `H_{-15}` at `j₀ = 0`:
--   `gcd (-121287375, 77) = 11`.
--
--   ```lean
--   theorem SingularModuli.factor_77: evalGcd H15 0 77 = 11 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SingularModuli/Experiments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SingularModuli/Experiments.lean#L132

-- Thm stub generated from Cryptography/SingularModuli/Experiments.lean
import Mathlib
import Definitions.Def_Cryptography_SingularModuli_Experiments
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier

/-!
# Singular Moduli Factoring, Step 5: verified experiments

This file contains machine-checked instances of the method and of the counting
theory, using genuine Hilbert class polynomials.

## Lab Notes (raw experimental data)

Class polynomials used (monic, degree = class number `h(D)`):

| `D`   | `h` | `H_D(X)`                                  |
|-------|-----|-------------------------------------------|
| `-4`  | 1   | `X - 1728`                                |
| `-7`  | 1   | `X + 3375`                                |
| `-8`  | 1   | `X - 8000`                                |
| `-11` | 1   | `X + 32768`                               |
| `-19` | 1   | `X + 884736`                              |
| `-15` | 2   | `X² + 191025 X - 121287375`               |
| `-20` | 2   | `X² - 1264000 X - 681472000`              |

Sweep over `j₀ = 0, 1, 2, …` and the seven discriminants above, first success
per semiprime (evaluations counted as (discriminant, `j₀`) pairs):

| `N`    | `p, q`   | first hit `(D, j₀)` | factor found | evals | evals/√N |
|--------|----------|---------------------|--------------|-------|----------|
| 15     | 3, 5     | `(-4, 0)`           | 3            | 2     | 0.52     |
| 35     | 5, 7     | `(-7, 0)`           | 5            | 3     | 0.51     |
| 77     | 7, 11    | `(-15, 0)`          | 11           | 7     | 0.80     |
| 143    | 11, 13   | `(-15, 0)`          | 11           | 7     | 0.59     |
| 323    | 17, 19   | `(-23, 0)`          | 17           | 10    | 0.56     |
| 899    | 29, 31   | `(-8, 2)`           | 31           | 32    | 1.07     |
| 3599   | 59, 61   | `(-19, 8)`          | 61           | 120   | 2.00     |
| 5183   | 71, 73   | `(-11, 9)`          | 73           | 131   | 1.82     |
| 10403  | 101, 103 | `(-15, 3)`          | 101          | 49    | 0.48     |
| 39203  | 197, 199 | `(-7, 8)`           | 199          | 115   | 0.58     |

The ratio `evals/√N` stays in a narrow band over two orders of magnitude, which
is what the `√N` theorem predicts (and what it *forbids* is a ratio decaying
like `N^{-c}`).

Exact success counts (`S = #{j₀ ∈ [0,N) : gcd(H_D(j₀), N) is nontrivial}`),
compared with the CRT formula `r_p(q - r_q) + (p - r_p) r_q`:

| `p, q`     | `D`   | `r_p` | `r_q` | `S`  | formula | `h(p+q)` bound |
|------------|-------|-------|-------|------|---------|----------------|
| 7, 11      | `-15` | 1     | 2     | 21   | 21      | 36             |
| 13, 17     | `-15` | 1     | 0     | 17   | 17      | 60             |
| 11, 13     | `-31` | 2     | 1     | 33   | 33      | 72             |
| 71, 73     | `-23` | 0     | 0     | 0    | 0       | 432            |
| 101, 103   | `-20` | 2     | 0     | 206  | 206     | 408            |

The `71, 73 / D = -23` row is the failure mode formalised in
`singularModuli_blind_of_no_roots`: for that discriminant the class polynomial
has no root modulo either prime, and *no* evaluation point works.

## Formalised below

* four concrete factorisations, each a closed-form computation of `evalGcd`;
* `rootCount_H15_7`, `rootCount_H15_11` and `successCount_H15_77` — the exact
  success count `S = 21` for `N = 77`, `D = -15`, derived from the general CRT
  theorem and two decidable root counts;
* `blind_example` — a polynomial with no roots mod 7 and mod 11, for which the
  method provably never succeeds on `N = 77`;
* `density_5183` — the `√N` density bound instantiated at `N = 5183`.
-/

open SingularModuli

open Polynomial FactoringBarriers

/-! ## Hilbert class polynomials of small discriminant -/











/-! ## Verified factorisations -/

theorem SingularModuli.factor_77: evalGcd H15 0 77 = 11 := by sorry
