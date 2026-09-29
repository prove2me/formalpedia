-- Prove2me | Theorems.Thm_Talagrand_certifiable_concentration
-- name    : Talagrand.certifiable_concentration
-- status  : Open
-- author  : @raver1975
-- created : 2026-09-11T00:10:11.117985+00:00
-- url     : https://prove2.me/theorems/5cd79ba1-4fd3-4874-b3c3-a0bfa9c0143a
-- title:
--   Talagrand's inequality for certifiable functionals.
-- statement:
--   **Talagrand's inequality for certifiable functionals.**  Let `f` be `1`-Lipschitz
--   for the plain (unweighted) Hamming metric, let `f ≤ b` on `A`, and suppose every
--   point `x` of `S` carries a *certificate*: a set `J` of at most `K` coordinates such
--   that every point agreeing with `x` on `J` satisfies `f ≥ m`.  Then
--
--   `mass A * mass S ≤ exp (-(m - b)² / (4 K))`.
--
--   The certificate is allowed to depend on `x`, and the deviation `m - b` is measured
--   on the scale `√K` of the certificate size — this is the gain over the
--   bounded-differences inequality, whose scale is `√n`.
--
--   ```lean
--   theorem Talagrand.certifiable_concentration{p : Fin n → α → ℝ} (hp0 : ∀ i a, 0 ≤ p i a)
--       (hp1 : ∀ i, ∑ a, p i a = 1) {f : (Fin n → α) → ℝ}
--       (hLip : ∀ z y : Fin n → α, f z ≤ f y + ∑ i, hamm (z i) (y i))
--       (A S : Finset (Fin n → α)) (hA : A.Nonempty) {b m K : ℝ} (hK : 0 < K) (hbm : b ≤ m)
--       (hAle : ∀ y ∈ A, f y ≤ b)
--       (hcert : ∀ x ∈ S, ∃ J : Finset (Fin n), ((J.card : ℝ)) ≤ K ∧
--         ∀ y : Fin n → α, (∀ i ∈ J, y i = x i) → m ≤ f y) :
--       mass p A * mass p S ≤ Real.exp (-((m - b) ^ 2 / (4 * K))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TalagrandCertifiable.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TalagrandCertifiable.lean#L174

-- Thm stub generated from Probability/TalagrandCertifiable.lean
import Mathlib
import Definitions.Def_Probability_TalagrandCertifiable
import Definitions.Def_Probability_TalagrandDefs
import Definitions.Def_Probability_TalagrandHypercube
import Definitions.Def_Probability_TalagrandProduct

/-!
# Talagrand's inequality for certifiable functionals

The corollary `Talagrand.lipschitz_concentration` uses the Lipschitz hypothesis
only to produce, for each far point `x`, a *witness weight vector* certifying
that `x` is far from `A` in a weighted Hamming metric.  Because the convex
distance dominates *every* admissible weighted Hamming distance
(`Talagrand.dHamming_sq_le_dTsq` holds for an arbitrary `w`), the witness is
allowed to depend on `x`.  This is exactly the extra freedom that makes
Talagrand's inequality strictly stronger than the bounded-differences
(Azuma–Hoeffding) inequality, and it is what the notion of a *certifiable*
functional exploits.

## Main results

* `Talagrand.certifiable_concentration` — let `f` be `1`-Lipschitz for the plain
  Hamming metric.  Suppose that every `x ∈ S` admits a *certificate* `J x`, a set
  of at most `K` coordinates such that *any* point agreeing with `x` on `J x`
  already satisfies `f ≥ m`.  If `f ≤ b` on `A` and `b ≤ m`, then
  `mass A * mass S ≤ exp (-(m - b)² / (4 K))`.
  Note that the deviation is measured on the scale `√K`, the size of a
  certificate, and **not** on the scale `√n`.
* `Talagrand.cube_ones_count_concentration` — the resulting sharpened
  concentration for the (unnormalised) number-of-ones functional on a product of
  arbitrary independent coins: the tail scale is `√m` rather than `√n`, so the
  bound is nontrivial for level sets of size `m = o(n)` where the weighted
  Lipschitz form gives nothing.
-/

open Talagrand

open Finset Real

variable {α : Type*} [Fintype α] [DecidableEq α]


variable {n : ℕ}

theorem Talagrand.certifiable_concentration{p : Fin n → α → ℝ} (hp0 : ∀ i a, 0 ≤ p i a)
    (hp1 : ∀ i, ∑ a, p i a = 1) {f : (Fin n → α) → ℝ}
    (hLip : ∀ z y : Fin n → α, f z ≤ f y + ∑ i, hamm (z i) (y i))
    (A S : Finset (Fin n → α)) (hA : A.Nonempty) {b m K : ℝ} (hK : 0 < K) (hbm : b ≤ m)
    (hAle : ∀ y ∈ A, f y ≤ b)
    (hcert : ∀ x ∈ S, ∃ J : Finset (Fin n), ((J.card : ℝ)) ≤ K ∧
      ∀ y : Fin n → α, (∀ i ∈ J, y i = x i) → m ≤ f y) :
    mass p A * mass p S ≤ Real.exp (-((m - b) ^ 2 / (4 * K))) := by sorry
