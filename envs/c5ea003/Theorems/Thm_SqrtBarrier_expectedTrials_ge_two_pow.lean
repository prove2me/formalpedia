-- Prove2me | Theorems.Thm_SqrtBarrier_expectedTrials_ge_two_pow
-- name    : SqrtBarrier.expectedTrials_ge_two_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:51:49.728907+00:00
-- url     : https://prove2.me/theorems/864d301a-afe2-48a5-8e3c-4f48f05ea217
-- title:
--   Exponential in the bit size.
-- statement:
--   **Exponential in the bit size.**  If `N ≥ 2^(2k)` then the expected number
--   of evaluations is at least `2^k / (3d)`.
--
--   ```lean
--   theorem SqrtBarrier.expectedTrials_ge_two_pow(Rp : Finset (ZMod p)) (Rq : Finset (ZMod q)) (d k : ℕ)
--       (hdp : Rp.card ≤ d) (hdq : Rq.card ≤ d) (hd : 0 < d)
--       (hpq : p ≤ q) (hbal : q ≤ 2 * p) (hG : 0 < (goodPairs Rp Rq).card)
--       (hN : 2 ^ (2 * k) ≤ p * q) :
--       (2 : ℝ) ^ k / (3 * d) ≤ expectedTrials Rp Rq := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/SingularModuliBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/SingularModuliBarrier.lean#L211

-- Thm stub generated from Geometry/SingularModuliBarrier.lean
import Mathlib
import Definitions.Def_Geometry_SingularModuliBarrier
/-
# The √N Barrier for Structured-Set Factoring (abstract layer)

Companion to `SingularModuliCore.lean`.  That file shows that for a semiprime
`N = p q` and an integer polynomial `f` (e.g. a Hilbert class polynomial `H_D`)
the evaluation point `j₀` factors `N` **iff** its CRT coordinates lie in the
"exclusive-or" set

    G = { (a,b) : a ∈ R_p, b ∉ R_q } ∪ { (a,b) : a ∉ R_p, b ∈ R_q },

where `R_m` is the root set of `f` mod `m`.  Here we forget the polynomial
entirely and analyse this configuration for *arbitrary* subsets
`R_p ⊆ ZMod p`, `R_q ⊆ ZMod q` with `|R_p|, |R_q| ≤ d`.  This is the honest
level of generality: the only feature of singular moduli the method exploits is
that `H_D` has few roots (`h(D) = deg H_D`) modulo each prime.

Main results.

* `SqrtBarrier.card_goodPairs` — the exact count `r_p (q - r_q) + (p - r_p) r_q`.
* `SqrtBarrier.expectedTrials_ge` — **lower bound**: for balanced primes
  (`p ≤ q ≤ 2p`) and root counts `≤ d`, the expected number of uniformly random
  evaluation points before a factor is found is at least `√N / (3 d)`.
* `SqrtBarrier.expectedTrials_le` — **matching upper bound**: if both root
  counts equal `h ≥ 1` and `4h ≤ p`, the expectation is at most `√N / h`.
  Hence the method is `Θ(√N / h)` — it *works*, and it is *exponential in the
  bit size of N*, quantified in `SqrtBarrier.expectedTrials_ge_two_pow`.
* `SqrtBarrier.exists_bad_shift` and `SqrtBarrier.exists_bad_shift_of_small`
  — **the circularity barrier**, in an adversarial (not merely probabilistic)
  form: a translation-averaging argument shows that *any* fixed query set of
  size below `√N / (3 d)` is defeated by some translate of the structured set.
  Knowing that the target set is "structured" is worth nothing unless one knows
  *where* it is, which is exactly the information `p` encodes.

Note on the informal claim `√N/(4h)` in the source note: the exact count below
gives expectation `pq / (h (p + q - 2h))`, i.e. `≈ √N / (2h)` for balanced
primes, not `√N/(4h)`.  The heuristic there double-counts the two primes; the
corrected constant is proved in `expectedTrials_balanced_eq`.
-/

open SqrtBarrier

open Finset

variable {p q : ℕ} [NeZero p] [NeZero q]

/-! ## The exclusive-or configuration and its exact size -/









/-! ## Expected number of evaluations -/

theorem SqrtBarrier.expectedTrials_ge_two_pow(Rp : Finset (ZMod p)) (Rq : Finset (ZMod q)) (d k : ℕ)
    (hdp : Rp.card ≤ d) (hdq : Rq.card ≤ d) (hd : 0 < d)
    (hpq : p ≤ q) (hbal : q ≤ 2 * p) (hG : 0 < (goodPairs Rp Rq).card)
    (hN : 2 ^ (2 * k) ≤ p * q) :
    (2 : ℝ) ^ k / (3 * d) ≤ expectedTrials Rp Rq := by sorry
