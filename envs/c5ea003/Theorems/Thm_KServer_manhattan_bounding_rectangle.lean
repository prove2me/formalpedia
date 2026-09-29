-- Prove2me | Theorems.Thm_KServer_manhattan_bounding_rectangle
-- name    : KServer.manhattan_bounding_rectangle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T17:25:38.317185+00:00
-- url     : https://prove2.me/theorems/652f0dae-bea4-465d-9f90-aad7d68cabb9
-- title:
--   A bounding rectangle in the city-block plane whose corners dominate every point
-- statement:
--   Let $S$ be a finite set of points of the **city-block plane** $\mathbb{R}^2_1$ — the plane with the metric $xy = |x_1-y_1| + |x_2-y_2|$. Then there is an axis-parallel rectangle $R$, with corners $x, z, y, t$ listed clockwise, containing $S$, such that:
--
--   * the two diagonals have the same length, $xy = zt$;
--   * **every** point $w$ of $R$ lies on both diagonals, in the sense that
--     $$xw + wy = xy \qquad\text{and}\qquad zw + wt = zt;$$
--   * for **any two** points $p, b$ of $R$ there is a corner $u$ with
--     $$pb + bu = pu,$$
--     that is, $b$ lies on a geodesic from $p$ to $u$.
--
--   ## Role
--
--   This is the one place where the geometry of the city-block plane enters the analysis of the Work Function Algorithm for three servers, and it is what makes that plane special. Its consequence, used repeatedly, is that in an expression of the form $pb - w(b,b')$ the free point $b$ may be pushed out to a corner of the rectangle: writing $pb = pu - bu$ and applying the Lipschitz property $w(u,b') \le w(b,b') + bu$ gives
--
--   $$pb - w(b,b') \;=\; pu - bu - w(b,b') \;\le\; pu - w(u,b').$$
--
--   Iterating, every free point in the definitions of the auxiliary potentials $\Lambda$ and $\Gamma$ may be assumed to be one of four points, at which point the comparison $\Lambda, \Gamma \le \Psi$ becomes a finite case analysis over the corners. That comparison is exactly the hypothesis under which the Work Function Algorithm is $3$-competitive.
--
--   The second bullet is what supplies the identities $py = xy - xp$ and $qt = zt - qz$ used to move a term from one diagonal to the other; the first says the two diagonals may be interchanged.
--
--   **Formalization note.** The rectangle is not taken to be the tight bounding box: a square $[-A,A]^2$ with $A$ any bound on the coordinates of $S$ is enough, and this avoids the empty case and the extraction of extrema. The conclusion quantifies over a finite superset $T$ of $S$ containing the four corners, so that the corners themselves also enjoy the stated properties — which the case analyses need.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 4, the geometric step opening the proofs of Lemmas 5 and 6: 'Let R be a rectangle with corners x, z, y, t (ordered clockwise) that contains all points in formula (6). Point b must be located between p and some corner of R, say y, that is, pb = py - by.'

import Mathlib

namespace KServer

theorem manhattan_bounding_rectangle (S : Finset (PiLp 1 fun _ : Fin 2 => ℝ)) :
    ∃ (T : Finset (PiLp 1 fun _ : Fin 2 => ℝ))
      (x z y t : PiLp 1 fun _ : Fin 2 => ℝ),
      S ⊆ T ∧ x ∈ T ∧ z ∈ T ∧ y ∈ T ∧ t ∈ T
      ∧ dist x y = dist z t
      ∧ (∀ w ∈ T, dist x w + dist w y = dist x y ∧ dist z w + dist w t = dist z t)
      ∧ (∀ p ∈ T, ∀ b ∈ T, ∃ u : PiLp 1 fun _ : Fin 2 => ℝ,
          (u = x ∨ u = z ∨ u = y ∨ u = t) ∧ dist p b + dist b u = dist p u) := by sorry

end KServer
