-- Prove2me | Definitions.Def_Novelty_HopfInnerProductWitness
-- name    : Novelty_HopfInnerProductWitness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:28:35.891759+00:00
-- url     : https://prove2.me/theorems/ef3e069a-fe44-4ea1-9f32-647facc9b3aa
-- title:
--   Aether Catalog definitions — Novelty_HopfInnerProductWitness
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.HopfInnerProductWitness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/HopfInnerProductWitness.lean by skeleton subtraction
import Mathlib

/-!
# The Hermitian inner product reconstructs the complex Hopf fibre

This file addresses the **complex base case of Conjecture 1** of the
"Composition-Algebra Playground" research direction: a *single* algebraic device
— the Hermitian inner product `λ = z̄z' + w̄w'` of two unit vectors — recovers the
full fibre structure of the Hopf map `S³ → S²`.

Two unit vectors `a = (z, w)` and `b = (z', w')` in `ℂ²` lie on the same Hopf
fibre iff they are complex-proportional, `b = μ a` with `‖μ‖ = 1`.  We show the
inner-product witness `λ = ⟨a, b⟩` detects and reconstructs this:

* `abs_witness_le_one` : `‖λ‖ ≤ 1` always (Cauchy–Schwarz);
* `witness_of_proportional` : if `b = μ a` then `λ = μ`;
* `dist_sq_eq` : the key identity `‖z' - λz‖² + ‖w' - λw‖² = 1 - ‖λ‖²`;
* `reconstruct_fibre` : if `‖λ‖ = 1` then `b = λ a`, i.e. the two points are on
  the same fibre and the second is recovered from the first by the phase `λ`.
-/

open ComplexConjugate

namespace HopfWitness

/-- The Hermitian inner-product witness `λ = z̄z' + w̄w'`. -/
noncomputable def witness (z w z' w' : ℂ) : ℂ := conj z * z' + conj w * w'





end HopfWitness


