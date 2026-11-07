-- Prove2me | Theorems.Thm_ZKSheafPCP_lemma_8_16
-- name    : ZKSheafPCP.lemma_8_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:14:02.456666+00:00
-- url     : https://prove2.me/theorems/d88e93c0-b193-4e75-9aa6-3383d619f6c0
-- title:
--   Lemma 8.16 — $\mathcal R\cup\mathcal K$ tests the curve code
-- statement:
--   Fix $\hat k$. There is a constant $c$ such that, for every bivariate Reed-Muller sheaf code as in Definition 8.1 with parameter $\hat k$ and with $d_X+d_Y|L_0|\le|L|/8$, the set $\mathcal R\cup\mathcal K$, with a uniform row with probability $1/2$ and a uniform column with probability $1/2$, is a $c$-testable cover for the local code $F_T$.
--
--   This is the low-degree test behind the PCPP, following Polishchuk–Spielman and Ben-Sasson–Sudan.
--
--   **Formalization Note** The construction of Theorem 8.18 uses $\hat k=1$.
--
--   Differences from the source:
--   - reading: "For each i ∈ [n], R ∪ K is a 1-testable cover for C_i", a "constant" (App. C) with k̂ fixed by "Let k̂ ≥ 0" in the proof of Theorem 8.15 → c depends on k̂ alone, not on F, L, d_X, d_Y; reason: no c is uniform in k̂: corrupting a quarter of T off L′₀ gives mean row and column distance about 2^{−k̂−3} and Δ(f|_T, F_T) = 1/4, matching Eq. (11)
--   - reading: C_i in RS+ (Definition 8.14), i.e. degree at most |L|/8 → 8(d_X + d_Y|L₀|) ≤ |L| as a hypothesis; reason: App. C proves it for elements of RS+ only
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Lemma 8.16, p.41; proof of Theorem 8.15, p.41; App. C, pp.48–50

import Mathlib
import Definitions.Def_ZKSheafPCP_RMParams

namespace ZKSheafPCP

open Classical

/-- Lemma 8.16, p.41 (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission (manuscript sha256 ac5e528f…)): `ℛ ∪ 𝒦` is a `1`-testable cover for `C_i`, the local code `F_T` of the Reed-Muller sheaf code, with the distribution
of App. C (a uniform row with probability `1/2`, a uniform column with probability `1/2`).

**Formalization Note** "`1`-testable" is a `c`-testable cover (Definition 5.2). `c` depends only on `k̂`, which the proof of Theorem 8.15 fixes first ("Let `k̂ ≥ 0`", p.41), and which is `1` in
Construction 8.17. No `c` is uniform in `k̂`: App. C's ratio `|L_β|/|L₀| = 2^{k̂+3}` (Eq. (11), p.50) is constant only for fixed `k̂`, and corrupting a quarter of the curve off `L′₀` gives a mean row and column distance of about
`2^{-k̂-3}` while `Δ(f|_T, F_T) = 1/4`. `C_i` is an element of `RS+`, so `d_X + d_Y · |L₀| ≤ |L|/8` (Definition 8.14). -/
theorem lemma_8_16 (khat : ℕ) : ∃ c : ℕ, ∀ (F : Type) [Field F] [Fintype F] [CharP F 2] (R : RMParams F) (dX dY : ℕ),
    R.khat = khat → R.Valid dX → 8 * (dX + dY * R.L0.card) ≤ 2 ^ R.k →
    IsTestableCover (R.codes dX dY) R.space c R.curve (R.rows ∪ R.cols) R.rowColLaw := by sorry

end ZKSheafPCP
