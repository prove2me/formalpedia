-- Prove2me | Theorems.Thm_modularity_semistable_elliptic
-- name    : modularity_semistable_elliptic
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-12T05:16:35.077303+00:00
-- url     : https://prove2.me/theorems/8c33b044-1880-4029-a6ab-fd02541f35ee
-- statement:
--   **Wiles's modularity theorem for semistable elliptic curves (1995).** Every semistable elliptic curve over ℚ is modular, i.e., is associated to a weight-2 newform. Applied to the Frey curve y² = x(x − aᵖ)(x + bᵖ) associated to a hypothetical FLT counterexample (a, b, c, p) with p ≥ 5 prime and pairwise coprime (a, b, c), the Frey curve is semistable (Frey–Mazur), hence modular. By Ribet's ε-conjecture (level-lowering), the associated newform has level dividing 2. But the space S₂(Γ₀(2)) of weight-2 cuspforms of level 2 is zero-dimensional — contradiction. This theorem is stated as a Black Box here; a full Lean 4 formalization would require the entire apparatus of abelian varieties, Galois representations, and the theory of modular forms — none of which is currently in Mathlib.
-- source:
--   https://doi.org/10.2307/2118559

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem modularity_semistable_elliptic (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) : False := by sorry
