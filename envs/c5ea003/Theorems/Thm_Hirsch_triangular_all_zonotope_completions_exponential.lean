-- Prove2me | Theorems.Thm_Hirsch_triangular_all_zonotope_completions_exponential
-- name    : Hirsch.triangular_all_zonotope_completions_exponential
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-21T19:02:14.911019+00:00
-- url     : https://prove2.me/theorems/7be0886c-9c8d-47a1-aa3f-367415e6830f
-- title:
--   A linear-size triangular H family forces exponential diameter in every compact zonotope completion
-- statement:
--   For every real 0<e<1/2 and natural n,m, define P in R^(n+1) by exactly 2(n+1) displayed original inequalities: the last coordinate lies in [0,1], and each earlier coordinate lies between e times the next coordinate and one minus that quantity. For any nonempty compact Q and any actual equality P+Q=sum_i[0,w_i], derive 2^n<=m and construct opposite actual extreme points u,v of the original completion such that every feasible-point walk between them through nondegenerate whole exposed segments has at least 2^n steps. The complete finite-hull representation of P, the family of 2^n genuine exposed original edges, and the distinctness of their unoriented directions are constructed rather than supplied. Q need not be convex. There is no supplied corner catalogue, direction matching, path or exponential-count oracle. This is a completion-diameter obstruction for an explicit linear-size H family, not an original-summand diameter lower bound or Polynomial Hirsch counterexample. It does not claim a formal facet-lattice count, the stronger count of all 2^(n+1)-1 directions, an asymptotic limit theorem, translation extension, or an optimal path theorem.
-- source:
--   Reuses the exact accepted namespace bodies from #280 (TriangularFamily, proof189b32df9e1c50c1c0b771bf6f43033094e06fea) and #319 (through Hirsch.CompletionDirections, proof7b1d1e7199de25855c5eadafe277a763796eaeb5). New affine-boundary hull reconstruction, recursively exposed free-last-coordinate edge family and normalized-direction injection instantiate the previously generic all-completion obstruction. Classical triangular/Klee-Minty geometry is credited to Gaertner, Helbling, Ota and Takahashi, Large Shadows from Sparse Inequalities, arXiv:1308.2495. No historical-priority claim.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.triangular_all_zonotope_completions_exponential (e : ℝ) (he : 0 < e) (he2 : e < 1/2) (n m : ℕ)
    (Q : Set (Fin (n+1) → ℝ)) (hQc : IsCompact Q) (hQne : Q.Nonempty)
    (w : Fin m → (Fin (n+1) → ℝ)) :
    let P : Set (Fin (n+1) → ℝ) := {x |
      (0 ≤ x (Fin.last n) ∧ x (Fin.last n) ≤ 1) ∧
      ∀ i : Fin n, e*x i.succ ≤ x i.castSucc ∧ x i.castSucc ≤ 1-e*x i.succ}
    let Z : Set (Fin (n+1) → ℝ) := {x | ∃ s : Fin m → ℝ,
      (∀ i, 0 ≤ s i ∧ s i ≤ 1) ∧ (∑ i : Fin m, s i • w i)=x}
    {z | ∃ x ∈ P, ∃ y ∈ Q, x+y=z}=Z →
    2^n ≤ m ∧ ∃ u v : Fin (n+1) → ℝ,
      u ∈ Z.extremePoints ℝ ∧ v ∈ Z.extremePoints ℝ ∧ u+v=∑ i : Fin m, w i ∧
      ∀ L : ℕ, ∀ p : Fin (L+1) → (Fin (n+1) → ℝ),
        p 0=u → p (Fin.last L)=v → (∀ i, p i ∈ Z) →
        (∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExposed ℝ Z (segment ℝ (p i.castSucc) (p i.succ))) → 2^n ≤ L := by sorry
