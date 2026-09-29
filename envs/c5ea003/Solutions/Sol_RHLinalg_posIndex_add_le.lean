-- Prove2me | solution 1 for RHLinalg.posIndex_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:48:02.328786+00:00
-- url     : https://prove2.me/submissions/f4731ef1-8dfa-43d5-8dec-21774ae88d90

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Theorems.Thm_RHLinalg_posDefOn_range_hermPosPart
import Theorems.Thm_RHLinalg_rank_specMap

-- from Zeta23.LinAlg.HermitianPosPart
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/

/-!
# Positive and negative parts of a Hermitian matrix

For a Hermitian matrix `Q` with spectral decomposition `Q = U diag(λ) Uᴴ`,
define `Q₊ := U diag(λ⁺) Uᴴ` and `Q₋ := U diag(λ⁻) Uᴴ` where
`λ⁺ = max(λ,0)`, `λ⁻ = max(−λ,0)`.

Then `Q = Q₊ − Q₋`, both are PSD, `Q₊ Q₋ = 0`, and `rank Q₊ = n₊(Q)`.

This is equivalent to the CFC `Q⁺`/`Q⁻` via `Matrix.IsHermitian.cfc_eq`, but
the direct spectral construction keeps the eigenvalue bookkeeping explicit,
which is what the rank–trace proof needs.
-/

noncomputable section

open Matrix Finset Unitary
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]



lemma specMap_id {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    specMap hA id = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

lemma specMap_sub {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    specMap hA (f - g) = specMap hA f - specMap hA g := by
  unfold specMap
  rw [← map_sub]
  congr 1
  simp only [← diagonal_sub, Pi.sub_apply, RCLike.ofReal_sub]







/-- `specMap hA f` is PSD whenever `f(λᵢ) ≥ 0` for all `i`. -/
lemma specMap_posSemidef {A : Matrix n n 𝕜} (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (specMap hA f).PosSemidef := by
  unfold specMap
  rw [conjStarAlgAut_apply]
  refine (PosSemidef.diagonal ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg (K := 𝕜) |>.mpr (hf i)

section PosNegPart

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)



lemma hermPosPart_sub_hermNegPart : hermPosPart hA - hermNegPart hA = A := by
  unfold hermPosPart hermNegPart
  rw [← specMap_sub, show ((·⁺) - (·⁻) : ℝ → ℝ) = id from
    funext fun x => posPart_sub_negPart x, specMap_id]


lemma hermNegPart_posSemidef : (hermNegPart hA).PosSemidef :=
  specMap_posSemidef hA fun _ => negPart_nonneg _




lemma rank_hermPosPart : (hermPosPart hA).rank = posIndex hA := by
  unfold hermPosPart posIndex
  rw [rank_specMap]
  congr 1; ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, posPart_eq_zero, not_le]






end PosNegPart

end RHLinalg
end
end

-- from Zeta23.LinAlg.Sylvester
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/

/-!
# Sylvester's law of inertia for Hermitian matrices (subspace bound)

We prove the key inequality: any subspace `W ⊆ 𝕜ⁿ` on which the Hermitian
form `x ↦ Re(xᴴAx)` is positive definite has dimension at most
`posIndex hA`.

The proof is short: `A = A₊ − A₋` with both parts PSD (`HermitianPosPart`).
If `A₊ · x = 0` for `x ∈ W ∖ {0}`, then `xᴴAx = −xᴴA₋x ≤ 0`, contradicting
positive-definiteness on `W`. So `(A₊ *ᵥ ·)|_W` is injective, hence
`dim W ≤ rank A₊ = posIndex hA`.

This is the engine behind `lem:inertia`: pulling back a Hermitian form
cannot increase its positive index.
-/

noncomputable section

open Matrix Finset Submodule
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]





omit [DecidableEq n] in
lemma hermForm_sub (A B : Matrix n n 𝕜) (x : n → 𝕜) :
    hermForm (A - B) x = hermForm A x - hermForm B x := by
  unfold hermForm
  simp [sub_mulVec, dotProduct_sub, map_sub]

omit [DecidableEq n] in
/-- `hermForm A x ≥ 0` when `A` is PSD. -/
lemma hermForm_nonneg_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (x : n → 𝕜) : 0 ≤ hermForm A x :=
  hA.re_dotProduct_nonneg x








/-- The dimension of `range A₊` is `posIndex hA`. -/
lemma finrank_range_hermPosPart {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Module.finrank 𝕜 (LinearMap.range (hermPosPart hA).mulVecLin) = posIndex hA := by
  rw [← rank_hermPosPart hA]; rfl

/-- **Sylvester's law of inertia (subspace characterization)**. -/
theorem posIndex_eq_max_finrank_posDefOn {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ W : Submodule 𝕜 (n → 𝕜), PosDefOn A W ∧
      Module.finrank 𝕜 W = posIndex hA :=
  ⟨_, posDefOn_range_hermPosPart hA, finrank_range_hermPosPart hA⟩

end RHLinalg
end
end

-- from Zeta23.LinAlg.Inertia
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/

/-!
# Inertia under pull-back (paper §3, `lem:inertia`)

For a Hermitian form `Q` on `ℂᵐ` and a linear map `𝒜 : U → ℂᵐ`, the positive
index of the pulled-back form `Q ∘ 𝒜` is at most the positive index of `Q`.

## Matrix formulation

If `Q : Matrix m m 𝕜` is Hermitian and `B : Matrix m d 𝕜` represents a linear
map `𝕜ᵈ → 𝕜ᵐ`, then `BᴴQB` is the matrix of the pulled-back form on `𝕜ᵈ`,
and `n₊(BᴴQB) ≤ n₊(Q)`.

## Proof

Via the subspace characterization of `posIndex` (`Sylvester.lean`):
- Let `Vp := range (BᴴQB)₊`, which has dimension `posIndex h(BᴴQB)` and on
  which `BᴴQB` is positive definite (`posDefOn_range_hermPosPart`).
- For `x ∈ Vp ∖ {0}`: `(Bx)ᴴQ(Bx) = xᴴ(BᴴQB)x > 0`, so `Bx ≠ 0`; hence
  `B|_{Vp}` is injective.
- `B(Vp) ⊆ 𝕜ᵐ` has dimension `= dim Vp` and `Q` is positive definite on it.
- By `finrank_le_posIndex_of_posDefOn hQ`, `dim B(Vp) ≤ posIndex hQ`.
-/

noncomputable section

open Matrix Finset Submodule
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d] [DecidableEq d]



end RHLinalg
end
open Matrix Finset Submodule
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d] [DecidableEq d]

theorem solution {Q₁ Q₂ : Matrix m m 𝕜}
    (hQ₁ : Q₁.IsHermitian) (hQ₂ : Q₂.IsHermitian) :
    posIndex (hQ₁.add hQ₂) ≤ posIndex hQ₁ + posIndex hQ₂ := by
  -- Any `(Q₁+Q₂)`-pos-def subspace `Vp` satisfies: `(Q₁)₊ + (Q₂)₊` is
  -- injective on it (same argument as the hard direction, with
  -- `P := (Q₁)₊ + (Q₂)₊` which dominates `Q₁+Q₂`). Hence
  -- `dim Vp ≤ rank((Q₁)₊ + (Q₂)₊) ≤ rank(Q₁)₊ + rank(Q₂)₊`.
  obtain ⟨Vp, hposV, hdimV⟩ := posIndex_eq_max_finrank_posDefOn (hQ₁.add hQ₂)
  rw [← hdimV]
  set P := hermPosPart hQ₁ + hermPosPart hQ₂
  set L : (m → 𝕜) →ₗ[𝕜] (m → 𝕜) := P.mulVecLin
  -- `P − (Q₁+Q₂) = (Q₁)₋ + (Q₂)₋` is PSD, so on `ker P`, `hermForm (Q₁+Q₂) ≤ 0`.
  have hPsub : P - (Q₁ + Q₂) = hermNegPart hQ₁ + hermNegPart hQ₂ := by
    simp only [P, ← hermPosPart_sub_hermNegPart hQ₁, ← hermPosPart_sub_hermNegPart hQ₂]
    abel
  have hPsub_psd : (P - (Q₁ + Q₂)).PosSemidef := by
    rw [hPsub]; exact (hermNegPart_posSemidef hQ₁).add (hermNegPart_posSemidef hQ₂)
  have hinj : Function.Injective (L.domRestrict Vp) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxV⟩ hxL
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hxL
    have hxL' : P *ᵥ x = 0 := hxL
    simp only [mem_bot]
    by_contra hne
    have hne' : x ≠ 0 := fun h => hne (Subtype.ext h)
    have hform_le : hermForm (Q₁ + Q₂) x ≤ 0 := by
      have : hermForm (Q₁ + Q₂) x = hermForm P x - hermForm (P - (Q₁ + Q₂)) x := by
        rw [hermForm_sub]; ring
      rw [this, show hermForm P x = 0 by unfold hermForm; rw [hxL']; simp]
      linarith [hermForm_nonneg_of_posSemidef hPsub_psd x]
    exact absurd (hposV x hxV hne') (not_lt.mpr hform_le)
  calc Module.finrank 𝕜 Vp
      = Module.finrank 𝕜 (LinearMap.range (L.domRestrict Vp)) :=
        (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ Module.finrank 𝕜 (LinearMap.range L) := by
        apply Submodule.finrank_mono
        rintro y ⟨⟨x, hxV⟩, rfl⟩; exact ⟨x, rfl⟩
    _ = P.rank := rfl
    _ ≤ (hermPosPart hQ₁).rank + (hermPosPart hQ₂).rank := by
        -- `rank(A+B) ≤ rank A + rank B` via `range(A+B) ⊆ range A ⊔ range B`.
        unfold Matrix.rank
        refine le_trans (Submodule.finrank_mono ?_)
          (Submodule.finrank_add_le_finrank_add_finrank _ _)
        rintro _ ⟨x, rfl⟩
        simp only [P, mulVecLin_apply, add_mulVec]
        exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
    _ = posIndex hQ₁ + posIndex hQ₂ := by rw [rank_hermPosPart, rank_hermPosPart]
