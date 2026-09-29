-- Prove2me | Definitions.Def_mme_CW_tensor
-- name    : mme_CW_tensor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-31T17:29:54.709671+00:00
-- url     : https://prove2.me/theorems/af48d436-ff3f-4ade-b915-6edc7a895770
-- statement:
--   **The Coppersmith–Winograd tensor `T_q`** (the algebraic centerpiece of CW 1990).
--
--   For a parameter $q \geq 0$, the CW tensor lives in three copies of $\mathbb{F}^{q+2}$, with basis indexed by $\{0, 1, \ldots, q, q{+}1\}$. Writing $e_a$ for the $a$-th standard basis vector,
--
--   $$T_q \;=\; \sum_{i=1}^{q} \bigl(e_0 \otimes e_i \otimes e_i \;+\; e_i \otimes e_0 \otimes e_i \;+\; e_i \otimes e_i \otimes e_0\bigr) \;+\; \bigl(e_0 \otimes e_0 \otimes e_{q+1} \;+\; e_0 \otimes e_{q+1} \otimes e_0 \;+\; e_{q+1} \otimes e_0 \otimes e_0\bigr).$$
--
--   The index convention is `0` for the "left boundary", `{1, …, q}` for the "middle" indices, and `q+1` for the "right boundary".
--
--   **Why it matters.** This is the canonical low-border-rank tensor with a "rich" combinatorial structure that the laser method can exploit: the rank-one support is naturally 3-graded (by which subset of $\{\{0\}, \{1,\ldots,q\}, \{q{+}1\}\}$ each factor index belongs to), and the type-triples are exactly $\{(0,1,1), (1,0,1), (1,1,0), (0,0,2), (0,2,0), (2,0,0)\}$. CW 1990 showed that this combinatorial profile lets one extract a large direct sum of matrix-multiplication subtensors from $T_q^{\otimes 2N}$ after restricting to a Salem–Spencer subset of the block indices, ultimately yielding $\omega < 2.376$.
--
--   **Packaging.** This file exports `CWObj K q : TensorObj K 3` (the platform's order-3 tensor wrapper), together with helper definitions `CWSpace`, `CWMonom`, `CWTensor` and the necessary `AddCommGroup`/`Module`/`Module.Finite` instances on each mode. The tensor is CW-specific; the abstract framework that consumes it (`subrankCapacity`, `mme_omega_le_of_subrank_capacity`, the abstract laser theorem, …) is reusable across all later improvements (Stothers 2010, Vassilevska Williams 2012, Le Gall 2014, Alman–VW 2020).
-- source:
--   https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_mme_tensor

/-! # The Coppersmith–Winograd tensor `T_q`

The CW tensor of parameter `q ≥ 0` lives in three copies of `Fin (q+2) → K`:

  `T_q = ∑_{i=1}^{q} (e_0 ⊗ e_i ⊗ e_i + e_i ⊗ e_0 ⊗ e_i + e_i ⊗ e_i ⊗ e_0)
       + (e_0 ⊗ e_0 ⊗ e_{q+1} + e_0 ⊗ e_{q+1} ⊗ e_0 + e_{q+1} ⊗ e_0 ⊗ e_0)`

with the index convention `0` = left boundary, `1..q` = "middle" indices,
`q+1` = right boundary. We define the rank-one monomial `CWMonom q a b c`
(`= e_a ⊗ e_b ⊗ e_c`), the full tensor `CWTensor K q`, and the packaged
`TensorObj` `CWObj K q`.

CW 1990 (J. Symbolic Computation 9) proves that for this tensor the
matrix-multiplication exponent satisfies `ω < 2.376`, via the laser method.
The CW-specific contents stop at this definition; the abstract laser
framework lives in separate files and re-uses this definition through the
`TensorObj` API.
-/

universe u

open PiTensorProduct BigOperators

namespace MME

/-! ## Mode spaces

All three modes of `T_q` are `Fin (q+2) → K`. We follow the `MMSpace` pattern
of matching on the `Fin 3` index so that downstream `tprod` calls type-check
cleanly. -/

@[reducible] def CWSpace (K : Type u) (q : ℕ) : Fin 3 → Type u
  | ⟨0, _⟩ => Fin (q+2) → K
  | ⟨1, _⟩ => Fin (q+2) → K
  | ⟨2, _⟩ => Fin (q+2) → K

@[reducible] instance CWSpace_addCommGroup {K : Type u} [Field K] (q : ℕ) (i : Fin 3) :
    AddCommGroup (CWSpace K q i) :=
  match i with
  | ⟨0, _⟩ => Pi.addCommGroup
  | ⟨1, _⟩ => Pi.addCommGroup
  | ⟨2, _⟩ => Pi.addCommGroup

@[reducible] instance CWSpace_module {K : Type u} [Field K] (q : ℕ) (i : Fin 3) :
    Module K (CWSpace K q i) :=
  match i with
  | ⟨0, _⟩ => Pi.module _ _ _
  | ⟨1, _⟩ => Pi.module _ _ _
  | ⟨2, _⟩ => Pi.module _ _ _

instance CWSpace_finite {K : Type u} [Field K] (q : ℕ) (i : Fin 3) :
    Module.Finite K (CWSpace K q i) :=
  match i with
  | ⟨0, _⟩ => inferInstance
  | ⟨1, _⟩ => inferInstance
  | ⟨2, _⟩ => inferInstance

/-! ## Rank-one monomials and the CW tensor

`CWMonom q a b c = e_a ⊗ e_b ⊗ e_c` (a single rank-one term).

`CWTensor K q` is the sum of `3q + 3` such monomials forming `T_q`. -/

/-- The rank-one tensor `e_a ⊗ e_b ⊗ e_c` in `⨂ Fin (q+2) → K`. -/
noncomputable def CWMonom (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q+2)) :
    PiTensorProduct K (CWSpace K q) :=
  tprod K (fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single a 1 : Fin (q+2) → K)
    | ⟨1, _⟩ => (Pi.single b 1 : Fin (q+2) → K)
    | ⟨2, _⟩ => (Pi.single c 1 : Fin (q+2) → K))

/-- The Coppersmith–Winograd tensor `T_q`. -/
noncomputable def CWTensor (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct K (CWSpace K q) :=
  let O : Fin (q+2) := ⟨0, by omega⟩
  let T : Fin (q+2) := ⟨q+1, by omega⟩
  (∑ i : Fin q,
      let M : Fin (q+2) := ⟨i.val + 1, by omega⟩
      CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O)
  + CWMonom K q O O T + CWMonom K q O T O + CWMonom K q T O O

/-- The CW tensor packaged as a `TensorObj K 3`. The reusable target of the
abstract laser-method machinery in subsequent files. -/
noncomputable def CWObj (K : Type u) [Field K] (q : ℕ) : TensorObj K 3 where
  V := CWSpace K q
  t := CWTensor K q

end MME


