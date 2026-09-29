-- Prove2me | Theorems.Thm_SqrtBarrier_exists_bad_shift_adaptive
-- name    : SqrtBarrier.exists_bad_shift_adaptive
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:51:36.965266+00:00
-- url     : https://prove2.me/theorems/dd6e57e7-e9f5-4cc5-a008-60c979909e0e
-- title:
--   Adaptivity does not help.
-- statement:
--   **Adaptivity does not help.**  An adaptive search is a sequence of
--   evaluation points `a 0, a 1, …` where `a n` may depend on the outcomes of the
--   earlier queries; but as long as no factor has been found, all those outcomes are
--   the single answer "failure", so the queried sequence is a *fixed* sequence.
--   Hence the translation-averaging bound applies verbatim: below `√N / (3d)`
--   queries, some translate of the structured set defeats the whole run.
--
--   ```lean
--   theorem SqrtBarrier.exists_bad_shift_adaptive(Rp : Finset (ZMod p)) (Rq : Finset (ZMod q))
--       (T : ℕ) (a : ℕ → ZMod p × ZMod q) (d : ℕ)
--       (hdp : Rp.card ≤ d) (hdq : Rq.card ≤ d) (hd : 0 < d)
--       (hpq : p ≤ q) (hbal : q ≤ 2 * p)
--       (hsmall : (T : ℝ) * (3 * d) < Real.sqrt (p * q)) :
--       ∃ t : ZMod p × ZMod q, ∀ i < T, t + a i ∉ goodPairs Rp Rq := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/SingularModuliBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/SingularModuliBarrier.lean#L441

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








/-! ## Random search: a rigorous success-probability bound

`expectedTrials` above is the mean of the geometric distribution.  To avoid
leaning on that interpretation, this section proves the corresponding statement
purely by counting: among all `N^T` sequences of `T` independent uniform
evaluation points, the proportion on which *every* point fails is
`(1 - |G|/N)^T`, and hence the success probability of a `T`-point random search
is at most `3 d T / √N`.  Below `√N/(6d)` points it is less than one half. -/




/-! ## The circularity barrier: averaging over translates -/

theorem SqrtBarrier.exists_bad_shift_adaptive(Rp : Finset (ZMod p)) (Rq : Finset (ZMod q))
    (T : ℕ) (a : ℕ → ZMod p × ZMod q) (d : ℕ)
    (hdp : Rp.card ≤ d) (hdq : Rq.card ≤ d) (hd : 0 < d)
    (hpq : p ≤ q) (hbal : q ≤ 2 * p)
    (hsmall : (T : ℝ) * (3 * d) < Real.sqrt (p * q)) :
    ∃ t : ZMod p × ZMod q, ∀ i < T, t + a i ∉ goodPairs Rp Rq := by sorry
