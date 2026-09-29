-- Prove2me | Definitions.Def_Logic_Rademacher_Massart
-- name    : Logic_Rademacher_Massart
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:21.699686+00:00
-- url     : https://prove2.me/theorems/d5390788-1319-43ff-9960-651af2fa4161
-- title:
--   Aether Catalog definitions — Logic_Rademacher_Massart
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Rademacher.Massart`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Rademacher/Massart.lean by skeleton subtraction
import Mathlib
/-
# Massart's finite class lemma

If a hypothesis class restricted to a sample of size `n` consists of `N` vectors, each
of Euclidean length at most `r`, then its empirical Rademacher complexity is at most

  `r * √(2 log N) / n`.

The proof is the classical Chernoff/MGF argument:

* Jensen's inequality moves the expectation inside the exponential;
* a maximum is bounded by a sum, and the moment generating function of a Rademacher
  sum factorises into hyperbolic cosines, `𝔼 exp(λ⟨σ,v⟩) = ∏ cosh(λ vᵢ)`;
* `cosh t ≤ exp(t²/2)` gives the sub-Gaussian bound `exp(λ²r²/2)`;
* optimising over `λ` yields `√(2 log N)`.

Combined with `Massart` for the class of all `±1` patterns, this shows the bound is
tight up to the absolute constant `√(2 log 2) ≈ 1.177`; see `rad_cube` and
`massart_cube_tight` at the end of the file.

This file is self-contained.
-/

namespace RademacherMassart

open Finset

variable {n : ℕ}

/-- The sign vector attached to a boolean vector: `true ↦ 1`, `false ↦ -1`. -/
def sgn (ε : Fin n → Bool) (i : Fin n) : ℝ := if ε i then 1 else -1

/-- The linear functional `v ↦ (1/n) ∑ σ i * v i` associated with a sign vector. -/
noncomputable def signAvg (ε : Fin n → Bool) (v : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, sgn ε i * v i

/-- The empirical Rademacher complexity of a class `F` of vectors. -/
noncomputable def rad (F : Set (Fin n → ℝ)) : ℝ :=
  (∑ ε : Fin n → Bool, sSup (signAvg ε '' F)) / 2 ^ n

/-! ### Elementary facts about sign patterns -/





/-! ### The two analytic ingredients -/




/-! ### Massart's lemma -/

/-- The unnormalised maximum correlation of the class `F` with the sign pattern `ε`. -/
noncomputable def maxCorr (F : Finset (Fin n → ℝ)) (hne : F.Nonempty) (ε : Fin n → Bool) : ℝ :=
  F.sup' hne (fun v => ∑ i, sgn ε i * v i)






/-! ### Tightness: the full sign cube -/

/-- The class of all `±1` patterns on the sample. -/
noncomputable def cube (n : ℕ) : Finset (Fin n → ℝ) := by
  classical
  exact (Finset.univ : Finset (Fin n → Bool)).image (fun ε => sgn ε)




end RademacherMassart


