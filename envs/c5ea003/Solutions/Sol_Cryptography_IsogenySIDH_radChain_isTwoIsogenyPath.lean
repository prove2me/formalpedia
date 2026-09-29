-- Prove2me | solution 1 for Cryptography.IsogenySIDH.radChain_isTwoIsogenyPath
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:10:52.072275+00:00
-- url     : https://prove2.me/submissions/b3249276-e01b-490e-a20b-9a1d39981684

-- Sol generated from Cryptography/IsogenySIDH/ModularTwoIsogeny.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
import Theorems.Thm_Cryptography_IsogenySIDH_jMont_radTwoParam
import Theorems.Thm_Cryptography_IsogenySIDH_modPoly2_jMont_jQuot
/-
# The radical Montgomery step is a genuine edge of the 2-isogeny graph

`RadicalMontgomeryFormula` produced an explicit rational map from `E_A` to a
generalized Montgomery curve with parameter `radTwoParam A α = (A+6)/(2α)`,
`α² = A + 2`.  That is a *local* verification: the formulas transport points.
This file supplies the *global* certificate that the construction really is a
2-isogeny, by checking it against the classical modular polynomial `Φ₂`.

The main results are:

* `jMont_radTwoParam` — the `j`-invariant of the target is
  `jQuot A = 16 (A²+12)³ / (A²-4)²`.  Remarkably the radical `α` cancels: the
  target `j` is a *rational* function of `A`.
* `jMont_model_independent` — the three Montgomery renormalisations of the
  quotient curve (obtained by moving each of its three two-torsion points to
  the origin, using the three radicals `√(A+2)`, `√(2-A)`, `√(A²-4)`) all have
  the same `j`-invariant `jQuot A`.  So the radical step is independent of the
  chosen model and of the sign of the radical.
* `modPoly2_jMont_jQuot` and `modPoly2_radical_step` — the pair
  `(j(E_A), j(E_{A'}))` is a zero of the level-2 modular polynomial `Φ₂`.  This
  is the definitive certificate of 2-isogeny, proved as a polynomial identity
  of degree 54 in `A`.
* `radChain_isTwoIsogenyPath` — an admissible radical walk traces a path in the
  2-isogeny graph, by induction along the walk.
* `two_isogeny_neighbours_card_le_three` — `Φ₂` is monic of degree three in each
  variable, so every vertex of the 2-isogeny graph has at most three neighbours;
  this bounds the branching of a radical walk and is what makes the walk a walk
  on a cubic (Ramanujan) graph.
-/

open Cryptography.IsogenySIDH

open Polynomial

variable {K : Type*} [Field K]

/-! ## `j`-invariants -/





/-! ## The three Montgomery models of the quotient -/








/-! ## The level-2 modular polynomial -/




/-- **Radical step certificate.**  The parameter produced by one radical
Montgomery step is 2-isogenous to the source, certified by `Φ₂`. -/
theorem modPoly2_radical_step {A α : K} (htwo : (2 : K) ≠ 0) (hα : α ≠ 0)
    (hsq : α ^ 2 = A + 2) (hd : A ^ 2 - 4 ≠ 0) :
    modPoly2 (jMont A) (jMont (radTwoParam A α)) = 0 := by
  rw [jMont_radTwoParam htwo hα hsq hd]
  exact modPoly2_jMont_jQuot hd


/-! ## Radical walks are paths in the 2-isogeny graph -/






/-! ## Degree bound: the 2-isogeny graph is cubic -/






/-! ## How many Montgomery models does one `j`-invariant have? -/








theorem radChain_succ {K : Type*} [Field K] (r : ℕ → K) (A : K) (n : ℕ) : Cryptography.IsogenySIDH.radChain r A (n + 1) = Cryptography.IsogenySIDH.radTwoParam (Cryptography.IsogenySIDH.radChain r A n) (r n) := rfl
open Cryptography.IsogenySIDH in
theorem solution{r : ℕ → K} {A : K} (htwo : (2 : K) ≠ 0)
    (h : NonsingularWalk r A) :
    IsTwoIsogenyPath (fun n => jMont (radChain r A n)) := by
  intro n
  obtain ⟨hadm, hns⟩ := h
  obtain ⟨h0, hsq⟩ := hadm n
  simpa [radChain_succ] using modPoly2_radical_step htwo h0 hsq (hns n)
