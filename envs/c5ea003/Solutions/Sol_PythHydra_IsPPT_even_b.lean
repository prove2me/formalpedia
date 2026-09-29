-- Prove2me | solution 1 for PythHydra.IsPPT.even_b
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:37:21.514998+00:00
-- url     : https://prove2.me/submissions/10471551-0b57-44b6-888e-8292165af4f7

-- Sol generated from Geometry/PythagoreanHydra/BerggrenDescent.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent

/-!
# The Berggren descent: a complete classification of the Berggren tree

This file develops, from scratch but following the naming of the catalog module
`Catalog/Bridges/BerggrenTrees/BerggrenPythagoreanCore.lean` (definitions `IsPythag`,
`bergA`, `bergB`, `bergC`, `invA`, `invB`, `invC`), the *descent* half of the Berggren
theory, which that module leaves open (its `parent_exists` is commented out there
because the required case analysis was missing).

The main results are:

* `PythHydra.parent` — a single, uniform **parent map** `(a,b,c) ↦ (|u|, |v|, 3c-2a-2b)`
  with `u = a + 2b - 2c`, `v = 2a + b - 2c`.
* `PythHydra.parent_eq_inv` — the parent map *is* one of the three inverse Berggren
  moves `invA`, `invB`, `invC`; which one is decided by the signs of `u` and `v`.
* `PythHydra.parent_isPPT`, `PythHydra.parent_hyp_lt` — the parent of a primitive
  triple is primitive, with strictly smaller hypotenuse: the descent is well-founded.
* `PythHydra.reach_iff_isPPT` — **classification**: the Berggren tree rooted at
  `(3,4,5)` consists of exactly the primitive Pythagorean triples with odd first leg.
* `PythHydra.decidableReach` — consequently membership in the Berggren tree is
  *decidable* (by an elementary arithmetic test), which is the negative answer to the
  "Matiyasevich phenomenon on the tree" front of the research mission.
-/

open PythHydra












/-! ### Elementary consequences of primitivity -/






/-! ### The uniform parent map -/



















/-! ### Forward moves preserve the class -/




/-! ### The Berggren tree and its classification -/









example : Reach (7, 24, 25) := by decide


open PythHydra in
theorem solution{a b c : ℤ} (h : IsPPT a b c) : Even b := by
  by_contra hb
  rw [Int.not_even_iff_odd] at hb
  obtain ⟨m, hm⟩ := h.odd
  obtain ⟨n, hn⟩ := hb
  have hp := h.pyth
  unfold IsPythag at hp
  have hc2 : c ^ 2 = 4 * (m ^ 2 + m + n ^ 2 + n) + 2 := by subst hm hn; linarith [hp]; 
  rcases Int.even_or_odd c with ⟨p, hp'⟩ | ⟨p, hp'⟩
  · have : (2 * p) ^ 2 = 4 * (m ^ 2 + m + n ^ 2 + n) + 2 := by
      rw [← hc2, hp']; ring
    have h4 : 4 * p ^ 2 = 4 * (m ^ 2 + m + n ^ 2 + n) + 2 := by linarith [this]
    omega
  · have : (2 * p + 1) ^ 2 = 4 * (m ^ 2 + m + n ^ 2 + n) + 2 := by
      rw [← hc2, hp']
    have h4 : 4 * (p ^ 2 + p) + 1 = 4 * (m ^ 2 + m + n ^ 2 + n) + 2 := by linarith [this]
    omega
