-- Prove2me | Definitions.Def_Evergreen_IdempotentCollapse2_QuantumCollapse
-- name    : Evergreen_IdempotentCollapse2_QuantumCollapse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:37:46.577996+00:00
-- url     : https://prove2.me/theorems/51da6c0f-6ac5-405b-b871-4de7706ab978
-- title:
--   Aether Catalog definitions — Evergreen_IdempotentCollapse2_QuantumCollapse
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.IdempotentCollapse2.QuantumCollapse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/IdempotentCollapse2/QuantumCollapse.lean by skeleton subtraction
import Mathlib

/-!
# Quantum Measurement as Idempotent Collapse

Measurement operators are orthogonal projections (P² = P, P* = P).
The Born rule emerges from the geometry of idempotent collapse.
-/

open Set Function

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A self-adjoint idempotent operator. -/
structure QProjection (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  toFun : V →L[ℝ] V
  idem : ∀ x, toFun (toFun x) = toFun x
  sa : ∀ x y, @inner ℝ V _ (toFun x) y = @inner ℝ V _ x (toFun y)

namespace QProjection

variable (P : QProjection V)



/-
PROBLEM
Projection decreases norm: ‖Px‖ ≤ ‖x‖.

PROVIDED SOLUTION
‖Px‖² = ⟨Px,Px⟩ = ⟨x, P²x⟩ = ⟨x, Px⟩ ≤ ‖x‖‖Px‖ by Cauchy-Schwarz. So ‖Px‖ ≤ ‖x‖.
-/

/-
PROBLEM
Pythagorean: ‖x‖² = ‖Px‖² + ‖x - Px‖².

PROVIDED SOLUTION
x = Px + (x - Px). Inner product ⟨Px, x-Px⟩ = ⟨Px, x⟩ - ⟨Px, Px⟩ = ⟨x, Px⟩ - ⟨x, P²x⟩ = 0. Then ‖x‖² = ‖Px + (x-Px)‖² = ‖Px‖² + ‖x-Px‖² by Pythagorean theorem.
-/


/-
PROBLEM
Iterating n ≥ 1 times = one application.

PROVIDED SOLUTION
Induction on hn : 1 ≤ n. Base: n=1, trivial. Step: f^[n+1] x = f(f^[n] x) = f(f x) by IH = f x by idem. Use Nat.le.step case and iterate_succ'.
-/

end QProjection

/-- A projection-valued measure models a quantum observable. -/
structure PVM (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (n : ℕ) where
  proj : Fin n → QProjection V
  orthogonal : ∀ i j, i ≠ j → ∀ x, (proj i).toFun ((proj j).toFun x) = 0
  complete : ∀ x, ∑ i : Fin n, (proj i).toFun x = x

/-
PROBLEM
Born rule: ∑ ‖Pᵢ ψ‖² = ‖ψ‖².

PROVIDED SOLUTION
Use M.complete: x = ∑ Pᵢ x. Then ‖x‖² = ‖∑ Pᵢ x‖². Since Pᵢ are mutually orthogonal (Pᵢ Pⱼ = 0 for i≠j), and each Pᵢ is self-adjoint, ⟨Pᵢ x, Pⱼ x⟩ = ⟨x, Pᵢ(Pⱼ x)⟩ = 0 for i≠j. So ‖∑ Pᵢ x‖² = ∑ ‖Pᵢ x‖² by Pythagorean theorem for mutually orthogonal vectors.
-/


end


