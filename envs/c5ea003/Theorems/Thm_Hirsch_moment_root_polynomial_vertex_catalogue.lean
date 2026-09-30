-- Prove2me | Theorems.Thm_Hirsch_moment_root_polynomial_vertex_catalogue
-- name    : Hirsch.moment_root_polynomial_vertex_catalogue
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T20:22:37.903867+00:00
-- url     : https://prove2.me/theorems/42f4500a-b696-4451-9d49-a13c7a2f98e5
-- title:
--   Exact root-polynomial catalogue of all original moment-polytope vertices
-- statement:
--   For any natural d<m and any injective real parameter map a on the m original labels, define the original mean-centered moment inequalities row_i(x)<=1 in dimension d. For EACH d-element subset S of the labels, construct the monic polynomial q_S(t)=product_(i in S)(t-a_i), its mean mu_S over ALL m labels, and the coefficient candidate v_S(j)=-coeff_(j+1)(q_S)/mu_S. Filter the entire family of d-element subsets by mu_S!=0 and q_S(a_i)/mu_S>=0 for all original labels. The candidates indexed by this explicit scalar test are injective, their image is EXACTLY the set of all actual Mathlib extreme points of the original H system, their tight labels are exactly their index set S, and their number is the number of accepted subsets and at most choose(m,d). No vertex list, feasible support, rank/inverse certificate, root factorization oracle, or catalogue-completeness assumption is supplied. The reverse proof derives nonzero mean from the actual vertex condition and active-kernel injectivity. Negative means are allowed and necessary. Dimension zero, unsorted labels, odd dimensions, and arbitrary real spacings are included. This is a complete finite reconstruction theorem, not a polynomial-time enumeration or a route-length/Polynomial Hirsch bound.
-- source:
--   Concrete all-vertex reconstruction following accepted #293 (Hirsch.moment_vertex_tight_row_criterion, theorem01977493-8c4e-45c5-957d-236e1d3fd475, source67cba0868eb70b992baf3579e90ac800e4e3a55a). The full 349-line accepted namespace prefix is reused byte-for-byte, omitting only its prior public root/print suffix. Source artifact10491383552 and all five frozen file hashes checked. Classical moment-curve polynomial geometry is credited; this is a formal project interface, not a historical-priority claim. Distinct from #296 consecutive-block routes and #297 generic cut-coordinate overcovers.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_root_polynomial_vertex_catalogue (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let q : Finset (Fin m) → Polynomial ℝ :=
      fun S => ∏ i ∈ S, (Polynomial.X - Polynomial.C (a i))
    let μ : Finset (Fin m) → ℝ := fun S => (∑ i : Fin m, (q S).eval (a i)) / (m : ℝ)
    let v : Finset (Fin m) → (Fin d → ℝ) := fun S j => -(q S).coeff (j.val+1) / μ S
    let F : Finset (Finset (Fin m)) :=
      (Finset.powersetCard d Finset.univ).filter
        (fun S => μ S ≠ 0 ∧ ∀ i : Fin m, 0 ≤ (q S).eval (a i) / μ S)
    Set.InjOn v F ∧
      (∀ x : Fin d → ℝ,
        x ∈ ({y | ∀ i, row y i ≤ 1}).extremePoints ℝ ↔ x ∈ F.image v) ∧
      (∀ S ∈ F, ∀ i : Fin m, row (v S) i = 1 ↔ i ∈ S) ∧
      (F.image v).card = F.card ∧ F.card ≤ Nat.choose m d := by sorry
