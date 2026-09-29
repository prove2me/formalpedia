-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_bell_eq_sum_stirlingSecond
-- name    : Geometry.KernelPatterns.bell_eq_sum_stirlingSecond
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:19:37.024599+00:00
-- url     : https://prove2.me/theorems/d3936326-17da-4a43-8c92-cc715b2d7a76
-- title:
--   `bell n = Σ_k S(n,k)`.
-- statement:
--   **`bell n = Σ_k S(n,k)`.**  Mathlib defines `Nat.bell` by the binomial
--   recursion and `Nat.stirlingSecond` by the triangle recursion; the two are
--   connected here through the common combinatorial model of kernel patterns.
--
--   ```lean
--   theorem Geometry.KernelPatterns.bell_eq_sum_stirlingSecond(n : ℕ) :
--       Nat.bell n = ∑ k ∈ range (n + 1), Nat.stirlingSecond n k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Synthesis.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Synthesis.lean#L23

-- Thm stub generated from Geometry/KernelPatterns/Synthesis.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_BellRecursion
import Definitions.Def_Geometry_KernelPatterns_BraidFlats

/-!
# Synthesis: one classification theorem, four counting corollaries

The three strands of `Geometry.KernelPatterns` meet here.

* Algebraic: kernel patterns classify the orbits of the diagonal symmetric
  group action (`orbit_card_eq_bell`).
* Combinatorial: they are the set partitions, counted with `k` blocks by the
  Stirling numbers and in total by the Bell numbers, giving the classical
  identity `bell n = Σ_k S(n,k)` (`bell_eq_sum_stirlingSecond`) — both sides of
  which are Mathlib definitions given purely by recursions.
* Geometric: they are the flats of the braid arrangement in `ℝ^n`, so the
  intersection lattice of the braid arrangement has `Nat.bell n` elements
  (`card_braidFlats_eq_bell`).
-/

open Geometry.KernelPatterns

open Finset

theorem Geometry.KernelPatterns.bell_eq_sum_stirlingSecond(n : ℕ) :
    Nat.bell n = ∑ k ∈ range (n + 1), Nat.stirlingSecond n k := by sorry
