-- Prove2me | Theorems.Thm_GradedTransitivity_hilbertSeq_rational_of_fixedPoint_growth
-- name    : GradedTransitivity.hilbertSeq_rational_of_fixedPoint_growth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:39:28.696797+00:00
-- url     : https://prove2.me/theorems/13636226-8bb4-4ae6-9d6c-f5a546396ac5
-- title:
--   Fixed-point growth criterion.
-- statement:
--   **Fixed-point growth criterion.**  If, for every `g â G`, the number of
--   injective `r`-tuples of `Y_n` fixed by `g` is eventually a polynomial in `n` of
--   degree `â¤ r`, then `â_n t_r(Y_n) qâ¿` is rational with denominator dividing
--   `(1-q)^{r+1}` â with no transitivity assumption whatsoever.
--
--   ```lean
--   theorem GradedTransitivity.hilbertSeq_rational_of_fixedPoint_growth(r N : ℕ) (p : G → ℚ[X])
--       (hdeg : ∀ g, (p g).natDegree ≤ r)
--       (hfix : ∀ g : G, ∀ n ≥ N,
--         (Nat.card (MulAction.fixedBy (Fin r ↪ Y n) g) : ℚ) = (p g).eval (n : ℚ)) :
--       ∃ P : ℚ[X], (1 - PowerSeries.X) ^ (r + 1) *
--           gen (fun n => (torbits G (Y n) r : ℚ)) = (P : PowerSeries ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/Burnside.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/Burnside.lean#L44

-- Thm stub generated from Shared/GradedTransitivity/Burnside.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_GSet
import Definitions.Def_Shared_GradedTransitivity_PolyClassification

/-!
# A Burnside bridge: fixed-point growth forces a rational Hilbert series

The main theorem of the cluster uses transitivity to control `t_r(Y_n)`.
Burnside's orbit-counting lemma provides a completely different, quantitative
route: `t_r(Y_n)` is the average over `g ∈ G` of the number of injective
`r`-tuples fixed by `g`.  Hence *polynomial growth of fixed-point counts*
already forces the Hilbert series to be rational with denominator dividing
`(1-q)^{r+1}` — no transitivity needed.

This is the cross-domain half of the picture: group actions (Burnside)
feeding the formal power series machine of `FiniteDifference`.

## Main results

* `torbits_burnside` : Burnside's formula for `t_r`.
* `hilbertSeq_rational_of_fixedPoint_growth` : polynomial fixed-point growth
  gives denominator `(1-q)^{r+1}`.
-/

open GradedTransitivity

open Polynomial



variable {G : Type*} [Group G] [Fintype G] {Y : ℕ → Type*} [∀ n, MulAction G (Y n)]
  [∀ n, Finite (Y n)]

theorem GradedTransitivity.hilbertSeq_rational_of_fixedPoint_growth(r N : ℕ) (p : G → ℚ[X])
    (hdeg : ∀ g, (p g).natDegree ≤ r)
    (hfix : ∀ g : G, ∀ n ≥ N,
      (Nat.card (MulAction.fixedBy (Fin r ↪ Y n) g) : ℚ) = (p g).eval (n : ℚ)) :
    ∃ P : ℚ[X], (1 - PowerSeries.X) ^ (r + 1) *
        gen (fun n => (torbits G (Y n) r : ℚ)) = (P : PowerSeries ℚ) := by sorry
