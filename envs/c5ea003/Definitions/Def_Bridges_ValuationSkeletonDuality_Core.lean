-- Prove2me | Definitions.Def_Bridges_ValuationSkeletonDuality_Core
-- name    : Bridges_ValuationSkeletonDuality_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:26.035432+00:00
-- url     : https://prove2.me/theorems/d4848f1b-53b4-4ee8-8f86-3636b176b1fc
-- title:
--   Aether Catalog definitions — Bridges_ValuationSkeletonDuality_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ValuationSkeletonDuality.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ValuationSkeletonDuality/Core.lean by skeleton subtraction
import Mathlib

/-!
# Valuation-Skeleton Margin Duality for p-adic Rational Networks — Core

This file establishes a valuation-theoretic margin theory for arithmetic rational
networks over non-Archimedean fields, connecting Berkovich-style skeleton decompositions
to certified ML robustness, tropical piecewise-linearization, and post-quantum
complexity proxies.

## Mathematical Domains Bridged
1. **Non-Archimedean Analytic Geometry** ↔ **Certified ML Robustness**
2. **Tropical Geometry** ↔ **Arithmetic Operadic Networks**
3. **Berkovich Skeleta** ↔ **Post-Quantum / Lattice Complexity**

Bridge: connects non-Archimedean analytic geometry to certified robustness in ML,
tropical piecewise-linearization to arithmetic operadic networks, and Berkovich
skeleta to post_quantum_security / lattice-style complexity proxies.
-/

open Finset Function Classical

noncomputable section

attribute [local instance] Classical.propDecidable

namespace ValuationSkeleton

/-! ## §1. Extended Valuation Codomain and HasIntValuation Typeclass -/

/-- Extended integer valuation type.
    Bridge: connects p-adic valuation theory to tropical semiring geometry. -/
abbrev EVal := WithTop ℤ

/-- `HasIntValuation`: Typeclass for fields with an integer non-Archimedean valuation.
    Bridge: connects non-Archimedean number theory to certified_robustness
    and post_quantum_security via discrete valuation arithmetic. -/
class HasIntValuation (K : Type*) [Field K] where
  v : K → EVal
  map_zero : v 0 = ⊤
  map_one : v 1 = (0 : ℤ)
  map_mul : ∀ x y, v (x * y) = v x + v y
  map_add_le_min : ∀ x y, min (v x) (v y) ≤ v (x + y)

variable {K : Type*} [Field K] [HasIntValuation K]
variable {α : Type*}

/-! ## §2. Primitive Valuation Lemmas -/



/-
Valuation of negation equals valuation.
    Bridge: connects additive symmetry to tropical geometry invariance.
-/

/-
The valuation of a nonzero element is finite.
    Bridge: connects field non-degeneracy to tropical finiteness.
-/

/-
Inversion negates valuation away from zero.
    Bridge: connects field inversion to tropical negation.
-/

/-
Strict dominance: if v(x) < v(y), then v(x+y) = v(x).
    Bridge: connects strict ultrametric inequality to tropical monomial selection.
-/

/-! ## §3. Threshold Margin and Label Definitions -/

/-- `thresholdMargin`: Valuation-theoretic margin of `f` at `x` relative to threshold `t`.
    Bridge: connects p-adic analytic margin to certified_robustness. -/
def thresholdMargin (f : α → K) (t : K) (x : α) : EVal :=
  HasIntValuation.v (f x - t)

/-- `valuationLabel`: Binary classification by valuation comparison.
    Bridge: connects tropical geometry to neural_network classification. -/
def valuationLabel (f₀ f₁ : α → K) (x : α) : Prop :=
  HasIntValuation.v (f₀ x) ≤ HasIntValuation.v (f₁ x)


/-- `PoleFreeOn`: A function is pole-free on a set.
    Bridge: connects algebraic geometry to certified_robustness. -/
def PoleFreeOn (f : α → K) (s : Set α) : Prop :=
  ∀ x ∈ s, f x ≠ 0

/-! ## §4. Skeleton Cell and Finite Cover Structures -/

/-- `SkeletonCell`: A cell in a Berkovich-style skeleton decomposition.
    Bridge: connects Berkovich analytic geometry to thermodynamic phase
    classification and lattice complexity. -/
structure SkeletonCell (α : Type*) where
  carrier : Set α
  chartDim : ℕ
  chart : α → Fin chartDim → ℤ

/-- `FiniteSkeletonCover`: A finite covering of a type by skeleton cells.
    Uses a natural-number indexed family for cleaner Finset-free API.
    Bridge: connects Berkovich skeleton theory to post_quantum_security complexity. -/
structure FiniteSkeletonCover (α : Type*) where
  numCells : ℕ
  cell : Fin numCells → SkeletonCell α
  covers : ∀ x : α, ∃ i : Fin numCells, x ∈ (cell i).carrier

/-- `skeletonComplexity`: Number of cells in a skeleton cover.
    Bridge: connects Berkovich geometry to arithmetic_complexity. -/
def skeletonComplexity (S : FiniteSkeletonCover α) : ℕ := S.numCells

/-- `CellConst`: A function is constant on a skeleton cell.
    Bridge: connects tropical constancy to certified_robustness. -/
def CellConst {β : Type*} (φ : α → β) (C : SkeletonCell α) : Prop :=
  ∃ b, ∀ x ∈ C.carrier, φ x = b

/-- `IsAffineOnCell`: A ℤ-valued function is affine on a cell.
    Bridge: connects tropical piecewise-linear geometry to neural_network
    decision boundary analysis. -/
def IsAffineOnCell (φ : α → ℤ) (C : SkeletonCell α) : Prop :=
  ∃ (a : Fin C.chartDim → ℤ) (b : ℤ),
    ∀ x ∈ C.carrier, φ x = ∑ i : Fin C.chartDim, a i * C.chart x i + b

/-- `mixedLabelCellCount`: Cells on which a label takes both values.
    Bridge: connects combinatorial complexity to VC-dimension. -/
def mixedLabelCellCount (S : FiniteSkeletonCover α) (lbl : α → Bool) : ℕ :=
  Finset.card (Finset.univ.filter fun i : Fin S.numCells =>
    (∃ x ∈ (S.cell i).carrier, lbl x = true) ∧
    (∃ y ∈ (S.cell i).carrier, lbl y = false))

/-- `HighMarginRegion`: Points where margin exceeds threshold γ.
    Bridge: connects margin theory to certified_robustness. -/
def HighMarginRegion (f : α → K) (t : K) (γ : ℤ) : Set α :=
  {x | (γ : EVal) ≤ thresholdMargin f t x}

/-! ## §5. Rational Gate Syntax -/

/-- `RationalGate`: Inductive syntax for rational arithmetic circuits.
    Bridge: connects operadic algebra to quantum circuit design
    and post_quantum_security arithmetic complexity. -/
inductive RationalGate (K : Type*) where
  | input : ℕ → RationalGate K
  | const : K → RationalGate K
  | add : RationalGate K → RationalGate K → RationalGate K
  | mul : RationalGate K → RationalGate K → RationalGate K
  | inv : RationalGate K → RationalGate K
  deriving Inhabited

namespace RationalGate

/-- Evaluation of a rational gate.
    Bridge: connects circuit semantics to p-adic function evaluation. -/
def eval [Field K] (σ : ℕ → K) : RationalGate K → K
  | input i => σ i
  | const c => c
  | add g h => g.eval σ + h.eval σ
  | mul g h => g.eval σ * h.eval σ
  | inv g => if g.eval σ = 0 then 0 else (g.eval σ)⁻¹

/-- Depth of a rational gate.
    Bridge: connects circuit complexity to post_quantum_security. -/
def depth : RationalGate K → ℕ
  | input _ => 0
  | const _ => 0
  | add g h => 1 + max g.depth h.depth
  | mul g h => 1 + max g.depth h.depth
  | inv g => 1 + g.depth

/-- Gate count.
    Bridge: connects circuit size to arithmetic_complexity. -/
def gateCount : RationalGate K → ℕ
  | input _ => 1
  | const _ => 1
  | add g h => 1 + g.gateCount + h.gateCount
  | mul g h => 1 + g.gateCount + h.gateCount
  | inv g => 1 + g.gateCount







end RationalGate

/-! ## §6. Counting and Complexity Theorems -/




/-! ## §7. Chart Evaluation Cost Model -/

/-- `chartEvalCost`: Cost of evaluating an affine chart function.
    Bridge: connects tropical geometry evaluation to arithmetic_complexity. -/
def chartEvalCost (C : SkeletonCell α) : ℕ := 2 * C.chartDim + 1



/-! ## §8. Refinement and Entropy -/


/-- `cellEntropy`: Entropy proxy for a skeleton cover.
    Bridge: connects Berkovich combinatorics to thermodynamic entropy. -/
def cellEntropy (S : FiniteSkeletonCover α) : ℕ := Nat.log 2 S.numCells


/-! ## §9. Valuation Lipschitz and Robustness -/

/-- `ValuationLipschitz`: Lipschitz in the valuation sense with constant L.
    v(f(x) - f(y)) ≥ v(x - y) - L for all x, y.
    Bridge: connects Lipschitz continuity to certified_robustness. -/
def ValuationLipschitz (f : K → K) (L : ℤ) : Prop :=
  ∀ x y, (HasIntValuation.v (x - y) : EVal) ≤ HasIntValuation.v (f x - f y) + (L : EVal)


/-- `latticeSecurityProxy`: Complexity proxy for post-quantum security.
    Bridge: connects Berkovich geometry to post_quantum_security. -/
def latticeSecurityProxy (S : FiniteSkeletonCover α) : ℕ := skeletonComplexity S


/-! ## §10. Gate Complexity Bound -/

/-- `gateComplexityBound`: Upper bound on skeleton complexity for a rational gate.
    Bridge: connects circuit structure to post_quantum_security complexity. -/
def gateComplexityBound : RationalGate K → ℕ
  | .input _ => 1
  | .const _ => 1
  | .add g h => gateComplexityBound g * gateComplexityBound h
  | .mul g h => gateComplexityBound g * gateComplexityBound h
  | .inv g => gateComplexityBound g + 1


/-
Gate complexity ≤ 2^(gateCount).
    Bridge: connects circuit depth to skeleton complexity.
-/



/-! ## §11. Tropical Margin Profile -/

/-- `TropicalMarginProfile`: Coefficients of an affine margin on a cell.
    Bridge: connects tropical geometry to neural_network decision boundary. -/
structure TropicalMarginProfile (d : ℕ) where
  slope : Fin d → ℤ
  intercept : ℤ

/-- Evaluate a tropical margin profile.
    Bridge: connects tropical affine evaluation to margin computation. -/
def TropicalMarginProfile.evalAt {d : ℕ} (p : TropicalMarginProfile d)
    (coords : Fin d → ℤ) : ℤ :=
  ∑ i : Fin d, p.slope i * coords i + p.intercept


/-! ## §12. High-Margin Label Constancy -/



/-! ## §13. Reparametrization and Symmetry -/

/-- `ChartEquivalence`: Two cells are chart-equivalent.
    Bridge: connects coordinate-free Berkovich geometry to computation. -/
def ChartEquivalence (C₁ C₂ : SkeletonCell α) : Prop :=
  C₁.carrier = C₂.carrier ∧ C₁.chartDim = C₂.chartDim




/-- `skeletonCellComplexity`: Complexity of a single cell.
    Bridge: connects cell complexity to quantum circuit width. -/
def skeletonCellComplexity (C : SkeletonCell α) : ℕ := C.chartDim


/-! ## §14. Robustness from Margin -/


/-! ## §15. Total Evaluation Cost -/


/-! ## §16. Quantified Existence Theorems -/


/-! ## §17. Addition and Multiplication Margin -/



/-! ## §18. Constant Gate Margin -/


/-! ## §19. Tropicalized Margin Is Min-Plus Affine -/


/-! ## §20. Security Proxy Monotonicity -/


/-! ## §21. Label Change Cells Finite -/


/-! ## §22. Affine Constancy on Cells -/


/-! ## §23. Depth-Zero Gates Have Trivial Complexity -/



/-! ## §24. HighMarginRegion Monotonicity -/


/-! ## §25. Pole-Free Composition -/



/-! ## §26. Valuation Label Constancy -/


/-! ## §27. CellConst Implies No Mixed Labels -/


end ValuationSkeleton


