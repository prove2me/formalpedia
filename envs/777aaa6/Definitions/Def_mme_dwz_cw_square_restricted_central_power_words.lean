-- Prove2me | Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
-- name    : mme_dwz_cw_square_restricted_central_power_words
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T04:12:30.76326+00:00
-- url     : https://prove2.me/theorems/fa2d56f7-2541-48d9-9837-72e7af7672c6
-- title:
--   Prescribed central-channel words and Kronecker-power routers for the CW square
-- statement:
--   For the central 022 and 202 constituents of the square of the Coppersmith–Winograd tensor, this interface defines prescribed positionwise channel words and the recursive source and target vectors they name. A split pattern has three channel classes with multiplicities L, G, and L; each middle-class position is labeled by an ordered pair in [q] × [q]. Thus a prescribed word identifies actual canonical CW-square basis pairs at every tensor-power position, rather than only a subspace of the same dimension.\n\nThe interface also lifts any source-faithful one-letter router recursively through Kronecker powers. Its source vectors are built from canonical block projections, and its target vectors are the matching nested standard matrix-multiplication coordinates.\n\n**Formalization Note** This module supplies definitions only. The accompanying theorem proves that the public source-faithful 022/202 router maps the complete tensor powers and every prescribed word exactly.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 (PDF pp. 59–60 / printed pp. 58–59) and Appendix A, proof of Lemma 4.6(c) (PDF pp. 82–83 / printed pp. 81–82), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_cw_square_fine_central_channels
import Definitions.Def_mme_TypeGrading_kron

open TensorProduct

namespace MME.DWZFineChannel

universe u

set_option autoImplicit false

/-! ## Prescribed central-channel words -/

/-- The three DWZ channel classes occur with multiplicities `L,G,L`. -/
def centralSplitMultiplicity (L G : ℕ) : Fin 3 → ℕ := ![L, G, L]

/-- A placement of the two exceptional channel classes and the middle class. -/
def CentralSplitPattern (m L G : ℕ) :=
  {p : Fin m → Fin 3 // ∀ c,
    Fintype.card {r : Fin m // p r = c} = centralSplitMultiplicity L G c}

/-- A prescribed 022 word: a split pattern together with one ordered
`q × q` label at every middle-class position. -/
def CentralRestricted022Word (q m L G : ℕ) :=
  Σ p : CentralSplitPattern m L G,
    ({r : Fin m // p.1 r = (1 : Fin 3)} → Fin q × Fin q)

/-- The literal fine-channel word encoded by a prescribed split word. -/
def encodeCentralRestricted022Word {q m L G : ℕ}
    (w : CentralRestricted022Word q m L G) : Fin m → Fine022Channel q := fun r ↦
  if _h0 : w.1.1 r = (0 : Fin 3) then
    Sum.inl 0
  else if h1 : w.1.1 r = (1 : Fin 3) then
    Sum.inr (Sum.inl (w.2 ⟨r, h1⟩))
  else
    Sum.inr (Sum.inr 0)

/-! ## Canonical source blocks and their recursive routers -/

noncomputable def Central022Block (K : Type u) [Field K] (q : ℕ) :
    TensorObj K 3 :=
  (cwSquareCanonicalGrading K q).blockSubtensor (cwSquareBlockType 0 2 2)

noncomputable def Central202Block (K : Type u) [Field K] (q : ℕ) :
    TensorObj K 3 :=
  (cwSquareCanonicalGrading K q).blockSubtensor (cwSquareBlockType 2 0 2)

/-- Lift any one-letter 022 router recursively through Kronecker powers. -/
noncomputable def central022PowerMapsFrom
    (K : Type u) [Field K] (q : ℕ)
    (base : ∀ s : Fin 3,
      (Central022Block K q).V s →ₗ[K] (MMObj K 1 1 (q ^ 2 + 2)).V s) :
    ∀ m : ℕ, ∀ s : Fin 3,
      ((Central022Block K q).kronPow m).V s →ₗ[K]
        ((MMObj K 1 1 (q ^ 2 + 2)).kronPow m).V s
  | 0, _ => LinearMap.id
  | m + 1, s => TensorProduct.map (base s)
      (central022PowerMapsFrom K q base m s)

/-- Lift any one-letter 202 router recursively through Kronecker powers. -/
noncomputable def central202PowerMapsFrom
    (K : Type u) [Field K] (q : ℕ)
    (base : ∀ s : Fin 3,
      (Central202Block K q).V s →ₗ[K] (MMObj K (q ^ 2 + 2) 1 1).V s) :
    ∀ m : ℕ, ∀ s : Fin 3,
      ((Central202Block K q).kronPow m).V s →ₗ[K]
        ((MMObj K (q ^ 2 + 2) 1 1).kronPow m).V s
  | 0, _ => LinearMap.id
  | m + 1, s => TensorProduct.map (base s)
      (central202PowerMapsFrom K q base m s)

/-! ## Exact source and target word vectors -/

noncomputable def central022SourceVec
    (K : Type u) [Field K] (q : ℕ)
    (c : Fine022Channel q) (s : Fin 3) :
    (Central022Block K q).V s :=
  (cwSquareCanonicalGrading K q).blockProj s
    (cwSquareBlockType 0 2 2 s)
    (cwSquareCanonicalBasis K q s (fine022SourcePair q c s))

noncomputable def central202SourceVec
    (K : Type u) [Field K] (q : ℕ)
    (c : Fine202Channel q) (s : Fin 3) :
    (Central202Block K q).V s :=
  (cwSquareCanonicalGrading K q).blockProj s
    (cwSquareBlockType 2 0 2 s)
    (cwSquareCanonicalBasis K q s (fine202SourcePair q c s))

/-- The nested pure tensor in the canonical 022 source block power named by
a literal word of fine channels. -/
noncomputable def central022SourceWordVec
    (K : Type u) [Field K] (q : ℕ) :
    ∀ m : ℕ, (Fin m → Fine022Channel q) → ∀ s : Fin 3,
      ((Central022Block K q).kronPow m).V s
  | 0, _, _ => (1 : K)
  | m + 1, w, s =>
      central022SourceVec K q (w 0) s ⊗ₜ[K]
        central022SourceWordVec K q m (fun r => w r.succ) s

/-- The matching nested standard-MM vector in the 022 power. -/
noncomputable def central022MMWordVec
    (K : Type u) [Field K] (q : ℕ) :
    ∀ m : ℕ, (Fin m → Fine022Channel q) → ∀ s : Fin 3,
      ((MMObj K 1 1 (q ^ 2 + 2)).kronPow m).V s
  | 0, _, _ => (1 : K)
  | m + 1, w, s =>
      fine022MMVec K q (fine022ChannelEquiv q (w 0)) s ⊗ₜ[K]
        central022MMWordVec K q m (fun r => w r.succ) s

noncomputable def central202SourceWordVec
    (K : Type u) [Field K] (q : ℕ) :
    ∀ m : ℕ, (Fin m → Fine202Channel q) → ∀ s : Fin 3,
      ((Central202Block K q).kronPow m).V s
  | 0, _, _ => (1 : K)
  | m + 1, w, s =>
      central202SourceVec K q (w 0) s ⊗ₜ[K]
        central202SourceWordVec K q m (fun r => w r.succ) s

/-- The matching nested standard-MM vector in the 202 power. -/
noncomputable def central202MMWordVec
    (K : Type u) [Field K] (q : ℕ) :
    ∀ m : ℕ, (Fin m → Fine202Channel q) → ∀ s : Fin 3,
      ((MMObj K (q ^ 2 + 2) 1 1).kronPow m).V s
  | 0, _, _ => (1 : K)
  | m + 1, w, s =>
      fine202MMVec K q (fine202ChannelEquiv q (w 0)) s ⊗ₜ[K]
        central202MMWordVec K q m (fun r => w r.succ) s

end MME.DWZFineChannel


