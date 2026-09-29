-- Prove2me | Definitions.Def_Novelty_RamanujanRhoMockTheta
-- name    : Novelty_RamanujanRhoMockTheta
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:38:09.318189+00:00
-- url     : https://prove2.me/theorems/af3daa37-52e1-47f3-ad73-0862af4e185c
-- title:
--   Aether Catalog definitions — Novelty_RamanujanRhoMockTheta
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.RamanujanRhoMockTheta`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/RamanujanRhoMockTheta.lean by skeleton subtraction
import Mathlib

/-!
# Coefficients of Ramanujan's third order mock theta function ρ(q): a finite sign law

Ramanujan's third order mock theta function is
$$ \rho(q) \;=\; \sum_{m\ge 0} \frac{q^{2m(m+1)}}{\prod_{k=0}^{m}\bigl(1+q^{2k+1}+q^{4k+2}\bigr)}
   \;=\; \sum_{n\ge 0} r(n)\,q^{n}. $$

The conjectured **exact sign law** states that for every `n`,
`r(3n) > 0`, `r(3n+1) ≤ 0`, and `r(3n+2) ≤ 0`, and that the only vanishing
coefficients in the two negative residue classes are
`r(2) = r(4) = r(8) = r(11) = r(20) = 0`.  The asymptotic version (all large `n`)
is known; the exact finite statement is open.

This file gives a **fully rigorous computable model** of the coefficient sequence
`r(n)` and a **machine-checked verification of the sign law and the exact zero set
for all `n ≤ 150`**.

## The computable model

We work with truncated power series over `ℤ` represented as coefficient lists
(index = degree, truncated at degree `N`).  The key simplification, justified by
the factorization proved in `RamanujanRhoFactorization.lean`
(`RamanujanRho.factor_cube_identity`,
`(1 - q^{2k+1})(1 + q^{2k+1} + q^{4k+2}) = 1 - q^{6k+3}`), is the closed form for
each factor's reciprocal:
$$ \frac{1}{1+q^{2k+1}+q^{4k+2}} \;=\; \frac{1-q^{2k+1}}{1-q^{6k+3}}
   \;=\; (1-q^{2k+1})\sum_{j\ge0} q^{(6k+3)j}. $$
Thus no general power-series inversion is needed: `factorInv` multiplies the
sparse polynomial `1 - q^{2k+1}` by the geometric series `Σ_j q^{(6k+3)j}`.  The
partial denominators nest, so their reciprocals nest too (`invProd`), and `ρ` is
assembled as `Σ_m q^{2m(m+1)} · invProd m` (`rhoSeries`).

Because every series is truncated at degree `N`, the coefficient of `q^n` for
`n ≤ N` receives all of its (finitely many) contributions, so `(rhoSeries N)`
reproduces `r(0), …, r(N)` exactly.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the finite sign law holds with a tiny sporadic zero
set `{2,4,8,11,20}` confined to the negative classes, and no zeros occur in the
class `n ≡ 0 (mod 3)`.

Experiment (Experimenter): implemented truncated power series over ℤ with a
closed-form reciprocal per factor (avoiding general inversion, which is hard to
run under `native_decide`).  Cross-checked the first 60 coefficients against an
independent Python computation: perfect agreement
(`1,-1,0,1,0,-1,1,-1,0,1,-1,0,2,…`).  Verified the sign law and the exact zero
list for all `n ≤ 150` by `native_decide`.

Analysis (Analyst): the sign law is "true but hard" — it is an exact-arithmetic
strengthening of a known asymptotic theorem.  The modulus 3 originates in the
factor `1 + q^{2k+1} + q^{4k+2}`, whose three exponents `0, 2k+1, 4k+2` cover
`{0, a, 2a} (mod 3)`; when `a ≠ 0` this is a full residue system mod 3.  The zero
set is genuinely sporadic (last zero at `n = 20`), matching the phenomenon that
the negative classes only "just barely" fail to be strictly negative early on.

Critique (Critic): the finite results are computational (`native_decide`); they
do not by themselves prove the infinite conjecture.  Their role is to (a) pin the
*exact* zero set (a finite, decidable fact) and (b) extend the verified range.
The insight-bearing algebraic content — the telescoping denominator
factorization that explains the modulus 3 — is proved in full generality in
`RamanujanRhoFactorization.lean` and reused here to justify the reciprocal model.

Synthesis (PI): definition + finite verification here, general factorization in
the companion file; the exact infinite sign law is promoted to a bold conjecture
in `FUTURE_DIRECTIONS.md`.
-/

namespace RamanujanRho

/-- Truncated multiplication of power series (coefficient lists) up to degree `N`. -/
def psMul (N : ℕ) (a b : List ℤ) : List ℤ :=
  (List.range (N+1)).map (fun n =>
    (List.range (n+1)).foldl (fun acc i => acc + a.getD i 0 * b.getD (n-i) 0) 0)

/-- The two-term polynomial `1 - q^s` as a truncated series. -/
def oneMinus (N s : ℕ) : List ℤ :=
  (List.range (N+1)).map (fun n => if n = 0 then (1:ℤ) else if n = s then -1 else 0)

/-- The geometric series `Σ_{j≥0} q^{s j}` truncated at degree `N` (needs `s ≥ 1`). -/
def geom (N s : ℕ) : List ℤ :=
  (List.range (N+1)).map (fun n => if n % s = 0 then (1:ℤ) else 0)

/-- Reciprocal of the `k`-th denominator factor `1 + q^{2k+1} + q^{4k+2}`,
using the closed form `(1 - q^{2k+1}) · Σ_j q^{(6k+3)j}`. -/
def factorInv (N k : ℕ) : List ℤ := psMul N (oneMinus N (2*k+1)) (geom N (6*k+3))

/-- Reciprocal of the partial denominator `∏_{k=0}^{m} (1 + q^{2k+1} + q^{4k+2})`. -/
def invProd (N m : ℕ) : List ℤ :=
  (List.range (m+1)).foldl (fun acc k => psMul N acc (factorInv N k))
    ((List.range (N+1)).map (fun n => if n = 0 then (1:ℤ) else 0))

/-- The series `ρ(q)` truncated at degree `N`:
`Σ_{m : 2m(m+1) ≤ N} q^{2m(m+1)} · invProd m`. -/
def rhoSeries (N : ℕ) : List ℤ :=
  (List.range (N+1)).foldl (fun acc m =>
    let sh := 2*m*(m+1)
    if sh > N then acc else
      let ip := invProd N m
      (List.range (N+1)).map (fun n =>
        acc.getD n 0 + (if n < sh then 0 else ip.getD (n - sh) 0)))
    (List.replicate (N+1) (0:ℤ))

/-- Working precision for the finite verification. -/
abbrev prec : ℕ := 150

/-- The coefficient `r(n)` of `ρ(q)`, for `n ≤ prec`. -/
def r (n : ℕ) : ℤ := (rhoSeries prec).getD n 0





end RamanujanRho


