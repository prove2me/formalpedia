-- Prove2me | Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra
-- name    : Algebra_PGLQuotient_VolumeAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:33:24.823427+00:00
-- url     : https://prove2.me/theorems/09e3a71f-e27e-4ef9-b898-62a446f9b0a2
-- title:
--   Aether Catalog definitions — Algebra_PGLQuotient_VolumeAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PGLQuotient.VolumeAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PGLQuotient/VolumeAlgebra.lean by skeleton subtraction
import Mathlib

/-!
# The algebraic core of the general-rank vertex volume

This file contains the purely algebraic input for the closed product form of the vertex volume
of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))` in **arbitrary rank**.

The building-theoretic side (see `Algebra.PGLQuotient.TwistedWeight` and
`Algebra.PGLQuotient.VertexVolumeGeneral`) produces a two-parameter family of *twisted masses*
`M(n,c,j)` (rank `n+1`, twist parameters `c` and `j`) satisfying a row-peeling recursion.  The
solution of that recursion is

`M(n,c,j) = NumV q n c j / DenV q n c j`,

where

* `NumV q n c j = ∑_{i=0}^{n} q^{ci} (∏_{k<i} (q^{n-k}-1)) (∏_{s<n-i}(q^{s+1+j}-1))`,
* `DenV q n c j = (∏_{s<n+1}(q^{s+1+j}-1)) (∏_{k<n}(q^{k+1}-1)) (∏_{k<n}(q^{c+k+1}-1))`.

The main result here is the **cut-set recursion** `NumV_rec`:

`q^{m+1} · NumV q (m+1) c j = (q^{m+1}-1)(q^{c+1}-1) · NumV q m (c+1) (j+1) + Jfac q (m+1) (j+1)`,

proved by an Abel summation whose term-by-term input is a pair of product identities.
Specialising `c = j = 0` collapses `NumV` to `(n+1)·Pfac q n`, which is what produces the
closed product form `d/(P(d)P(d-1))` of the vertex volume.
-/

namespace PGLQuotient

open Finset

section VolumeAlgebra

variable (q : ℝ)

/-- `Gpoly q n i = ∏_{k<i} (q^{n-k} - 1)`, the "descending" product. -/
noncomputable def Gpoly (n i : ℕ) : ℝ := ∏ k ∈ range i, (q ^ (n - k) - 1)

/-- `Jfac q r j = ∏_{s=1}^{r} (q^{s+j} - 1)`. -/
noncomputable def Jfac (r j : ℕ) : ℝ := ∏ s ∈ range r, (q ^ (s + 1 + j) - 1)

/-- `Pfac q n = ∏_{k=1}^{n} (q^k - 1)`, the classical `P(n)`. -/
noncomputable def Pfac (n : ℕ) : ℝ := ∏ k ∈ range n, (q ^ (k + 1) - 1)

/-- `Cfac q n c = ∏_{k=1}^{n} (q^{c+k} - 1)`. -/
noncomputable def Cfac (n c : ℕ) : ℝ := ∏ k ∈ range n, (q ^ (c + k + 1) - 1)

/-- The numerator of the closed form of the twisted mass in rank `n+1`. -/
noncomputable def NumV (n c j : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1), q ^ (c * i) * (Gpoly q n i * Jfac q (n - i) j)

/-- The denominator of the closed form of the twisted mass in rank `n+1`. -/
noncomputable def DenV (n c j : ℕ) : ℝ := Jfac q (n + 1) j * Pfac q n * Cfac q n c

variable {q}

















section Positivity

variable (hq : 1 < q)
include hq







end Positivity

end VolumeAlgebra

end PGLQuotient


