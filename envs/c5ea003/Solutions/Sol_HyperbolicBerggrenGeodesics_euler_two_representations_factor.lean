-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.euler_two_representations_factor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:29:36.524612+00:00
-- url     : https://prove2.me/submissions/de47db1c-cd87-4411-92bc-79647f7212a9

-- Sol generated from Geometry/HyperbolicBerggrenGeodesics.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Theorems.Thm_HyperbolicBerggrenGeodesics_repr_dot_lt

/-!
# Hyperbolic–Pythagorean Geodesics: the Berggren tree in the Poincaré half-plane

This file develops a rigorous bridge between three a-priori unrelated objects:

* the **Berggren ternary tree** of primitive Pythagorean triples (combinatorics /
  arithmetic),
* the **hyperbolic plane** in the Poincaré upper half-plane model `ℍ`
  (Riemannian geometry), and
* **integer factorization** via Euler's two-representation method (number theory).

## Main results

* `bStepL_triple`, `bStepM_triple`, `bStepR_triple` : the three Berggren matrices
  `B₁, B₂, B₃` acting on Pythagorean triples are conjugate, through the Euclid
  parametrisation `(m,n) ↦ (m²-n², 2mn, m²+n²)`, to the three linear maps
  `(m,n) ↦ (2m-n, m), (2m+n, m), (m+2n, n)` on Euclid seeds.
* `seed_step*_isSeed` : the three seed maps preserve the "primitive seed" conditions
  (`0 < n < m`, `gcd m n = 1`, opposite parity).
* `cosh_dist_hpoint_I` : the exact hyperbolic cosine of the distance from the base
  point `i` to the node point `z(m,n) = (n + i)/m`, namely `(m² + n² + 1)/(2m)`.
* `hyperbolic_dist_eq_half_log_hypotenuse` : **the logarithmic trajectory theorem.**
  For every Euclid seed with hypotenuse `c = m² + n²`,
  `|d_ℍ(i, z(m,n)) - ½ log c| ≤ log 2`.
  So *every* node of the Berggren tree, no matter how deep, sits at hyperbolic
  distance `½ log c + O(1)` from the root: the geodesic trajectory is
  logarithmic — sub-linear — in the size of the triple.
* `combDepth_hypotenuse` and `no_logarithmic_depth_bound` : by contrast the
  *combinatorial* depth is **not** logarithmic. The spine `(2,1) → (3,2) → (4,3) → …`
  has depth `k` and hypotenuse only `2k² + 6k + 5`, so depth is `Θ(√c)` there.
  Hence the hyperbolic metric compresses the tree exponentially.
* `hyperbolic_ball_volume_growth` : a **no-free-lunch** theorem. The number of
  Berggren nodes inside the hyperbolic ball of radius `R` around `i` grows like
  `e^{R}`, i.e. like the hypotenuse itself. A short geodesic does not make the
  search cheap.
* `geodesic_energy_lower_bound` : the Cauchy–Schwarz bound `E ≥ d²/k` relating the
  discrete energy of a `k`-step trajectory to the hyperbolic displacement, and
  `berggren_path_energy_lower_bound`, its specialisation to Berggren paths.
* `euler_two_representations_factor` : two essentially distinct representations
  `N = a² + b² = c² + d²` produce a **non-trivial divisor** `gcd(N, ac+bd)` of `N`.
* `berggren_collision_factors` : two distinct Berggren nodes sharing a hypotenuse
  `N` factor `N`.

## Design notes

Distances are Mathlib's genuine hyperbolic metric on `UpperHalfPlane` (`ℍ`), not a
hand-rolled surrogate; `UpperHalfPlane.cosh_dist'` is the only geometric input.
-/

open HyperbolicBerggrenGeodesics

open Real

noncomputable section

/-! ## Part 1. Euclid seeds and the Berggren tree in seed coordinates -/


















/-! ## Part 2. The hyperbolic embedding and the logarithmic trajectory theorem -/

open UpperHalfPlane








/-! ## Part 3. The spine: combinatorial depth is *not* logarithmic -/











/-! ## Part 4. Geodesic energy -/








/-! ## Part 5. From geometry to arithmetic: collisions factor the hypotenuse -/







/-! ## Part 6. Non-vacuity: explicit witnesses -/








/-! ## Part 7. Second cycle: quantitative shape of a collision -/






open HyperbolicBerggrenGeodesics in
theorem solution{a b c d N : ℕ} (ha : 0 < a)
    (hc : 0 < c) (hd : 0 < d) (h1 : a ^ 2 + b ^ 2 = N) (h2 : c ^ 2 + d ^ 2 = N)
    (hne1 : a * d ≠ b * c) (hne2 : a * c ≠ b * d) :
    1 < Nat.gcd N (a * c + b * d) ∧ Nat.gcd N (a * c + b * d) < N := by
  set P := a * c + b * d with hP
  set Q := a * d + b * c with hQ
  have hNpos : 0 < N := by nlinarith
  have hPpos : 0 < P := Nat.add_pos_left (Nat.mul_pos ha hc) _
  have hQpos : 0 < Q := Nat.add_pos_left (Nat.mul_pos ha hd) _
  have hPlt : P < N := repr_dot_lt h1 h2 hne1
  have hQlt : Q < N := repr_dot_lt h1 (by omega : d ^ 2 + c ^ 2 = N) hne2
  have hPQ : P * Q = N * (c * d + a * b) := by
    have hexp : P * Q = (a ^ 2 + b ^ 2) * (c * d) + (c ^ 2 + d ^ 2) * (a * b) := by
      rw [hP, hQ]; ring
    rw [h1, h2] at hexp
    rw [hexp]; ring
  have hdvd : N ∣ P * Q := ⟨c * d + a * b, hPQ⟩
  constructor
  · by_contra hcon
    push_neg at hcon
    have hgne : Nat.gcd N P ≠ 0 := by
      simp only [ne_eq, Nat.gcd_eq_zero_iff, not_and]
      omega
    have hcop : Nat.Coprime N P := by
      unfold Nat.Coprime; omega
    have : N ∣ Q := hcop.dvd_of_dvd_mul_left hdvd
    have := Nat.le_of_dvd hQpos this
    omega
  · have hle : Nat.gcd N P ≤ N := Nat.le_of_dvd hNpos (Nat.gcd_dvd_left _ _)
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hNP : N ∣ P := h ▸ Nat.gcd_dvd_right N P
      have := Nat.le_of_dvd hPpos hNP
      omega
