-- Prove2me | Definitions.Def_MachineLearning_TropicalNTK
-- name    : MachineLearning_TropicalNTK
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:16.40699+00:00
-- url     : https://prove2.me/theorems/4ee69744-fb96-4f11-b391-0d538ec55508
-- title:
--   Aether Catalog definitions — MachineLearning_TropicalNTK
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TropicalNTK`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TropicalNTK.lean by skeleton subtraction
import Mathlib
/-
# Tropical Neural Tangent Kernel as Polyhedral Linearization

This file formalizes the **tropical NTK** — a polyhedral kernel arising from
min-plus neural networks — and proves its structural rigidity on strict argmin
cells. The main results are:

1. A tropical network (inf of affine forms) equals the active branch on a strict cell.
2. The combinatorial parameter gradient is determined by the active branch.
3. The tropical NTK equals ⟨x, y⟩ + 1 when both inputs share a strict cell.
4. The tropical network output is constant along flat directions.
5. The tropical NTK has the form ⟨x, y⟩ + 1 along flat perturbations.

These theorems give the precise **lazy/feature-learning dichotomy**: inside a
tropical flat cell the kernel formula is frozen (lazy regime); crossing a tropical
wall changes the active branch (feature learning).
-/


open Finset BigOperators Classical

noncomputable section

/-! ## Definitions -/

/-- Affine score of hidden unit `i` on input `x`:  W_i · x + b_i -/
def affineScore {d m : ℕ}
    (W : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (i : Fin m) (x : Fin d → ℝ) : ℝ :=
  (∑ k : Fin d, W i k * x k) + b i

/-- Tropical network: pointwise inf of affine scores over a nonempty set S -/
def tropicalNet {d m : ℕ}
    (S : Finset (Fin m)) (hS : S.Nonempty)
    (W : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  S.inf' hS (fun i => affineScore W b i x)


/-- The argmin of affine scores over S: the element of S minimizing the score at x. -/
noncomputable def argminScore {d m : ℕ}
    (S : Finset (Fin m)) (hS : S.Nonempty)
    (W : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (x : Fin d → ℝ) : Fin m :=
  (Finset.exists_min_image S (fun i => affineScore W b i x) hS).choose




/-- Tropical parameter gradient: gradient of the active branch at argmin.
    Weight gradient at argmin unit = x, bias gradient = 1; all others = 0. -/
def tropicalParamGrad
    {d m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty)
    (W : Fin m → (Fin d → ℝ)) (b : Fin m → ℝ)
    (x : Fin d → ℝ) : (Fin m → Fin d → ℝ) × (Fin m → ℝ) :=
  let i0 := argminScore S hS W b x
  ( fun i k => if i = i0 then x k else 0,
    fun i => if i = i0 then 1 else 0 )

/-- Tropical NTK: inner product of tropical parameter gradients -/
def tropicalNTK
    {d m : ℕ}
    (S : Finset (Fin m)) (hS : S.Nonempty)
    (W : Fin m → (Fin d → ℝ)) (b : Fin m → ℝ)
    (x y : Fin d → ℝ) : ℝ :=
  let gx := tropicalParamGrad S hS W b x
  let gy := tropicalParamGrad S hS W b y
  (∑ i : Fin m, ∑ k : Fin d, gx.1 i k * gy.1 i k) +
  (∑ i : Fin m, gx.2 i * gy.2 i)

/-! ## Theorem 1: Tropical network equals active branch on strict cell -/


/-! ## Theorem 2: Parameter gradient on strict cell -/


/-! ## Theorem 3: Tropical NTK = ⟨x, y⟩ + 1 on common strict cell -/

/-
When both x and y lie in the same strict argmin cell for i₀,
    the tropical NTK equals ⟨x, y⟩ + 1. This is the first real theorem
    that deserves the phrase "tropical NTK."
-/

/-! ## Theorem 4: Tropical network output is constant along flat directions -/

/-
Along a flat direction v (W_{i₀} · v = 0) that preserves the strict cell,
    the tropical network output is constant. This is the prediction-level
    characterization of the lazy regime: no change in output without
    crossing a tropical wall.
-/

/-! ## Theorem 5: NTK formula ⟨x+tv, y⟩ + 1 on flat perturbation -/

/-
Along a flat direction v preserving the strict cell, the tropical NTK
    at (x+tv, y) equals ⟨x+tv, y⟩ + 1 — the same linear kernel formula
    but evaluated at the displaced point. The kernel TYPE (linear + bias)
    is preserved; only the input changes.
-/

/-! ## Corollary: Lazy/Feature-Learning Dichotomy -/

/-
**Lazy regime characterization**: On a strict argmin cell, the tropical
    network is affine and the tropical NTK is the standard linear kernel ⟨·,·⟩ + 1.
    Feature learning occurs exactly when crossing a tropical wall changes the
    active branch, and hence the kernel formula.
-/

end


