-- Prove2me | Definitions.Def_mme_stothers_phi125_cyclic_hash_data
-- name    : mme_stothers_phi125_cyclic_hash_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-03T00:19:47.128692+00:00
-- url     : https://prove2.me/theorems/7cc133df-1644-4b18-90c1-34020a51ed1e
-- title:
--   Five-grade affine hash data for cyclic phi_125 profiles
-- statement:
--   For the six-label symmetric φ₁₂₅ profile, this definition introduces coordinatewise support for mixed exact words, the three cyclic support tests, and the source-faithful affine five-grade hash. The coefficient code is deliberately shared with the already formalized φ₂₃₃ hash because both constructions use words over grades 0,…,4 and the local support equation x+y+z=4. It also supplies concrete finite enumerations of exact words and cyclic exact edges. Marginal uniqueness for φ₁₂₅ means the exact target is its own ambient same-marginal family, eliminating the exceptional completion-ratio layer required for φ₂₃₃.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Lemma 5.1(ii), pp. 359–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.ZMod.Basic
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash

namespace MME.StothersFourth.Phi125

set_option autoImplicit false

def CoordinatewiseSupported
    {N alpha beta gamma : ℕ}
    (x y z : ExactProfileWord N alpha beta gamma) : Prop :=
  ∀ j : Fin (2 * N), ∃ r : Fin 6,
    pattern r 0 = modeWord x.1 0 j ∧
    pattern r 1 = modeWord y.1 1 j ∧
    pattern r 2 = modeWord z.1 2 j

def CyclicCoordinatewiseSupported
    {N alpha beta gamma : ℕ}
    (x y z : CyclicExactEdge N alpha beta gamma) : Prop :=
  CoordinatewiseSupported x.1 y.1 z.1 ∧
    CoordinatewiseSupported y.2.1 z.2.1 x.2.1 ∧
    CoordinatewiseSupported z.2.2 x.2.2 y.2.2

abbrev cyclicHashModeCode
    (p N : ℕ) (i : Fin 3) (u : CyclicModeWord N) :
    Fin 3 → Fin (2 * N) → ZMod p :=
  MME.StothersFourth.Phi233.cyclicHashModeCode p N i u

def cyclicAffineHash
    (p N alpha beta gamma : ℕ)
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e : CyclicExactEdge N alpha beta gamma) : ZMod p :=
  shift + match i with
  | ⟨0, _⟩ =>
      Phi233.doubledXHash (2 * offset) (w 0) (modeWord e.1.1 0) +
        4 * Phi233.doubledZHash 0 (w 1) (modeWord e.2.1.1 2) -
        2 * Phi233.doubledYHash offset (w 2) (modeWord e.2.2.1 1)
  | ⟨1, _⟩ =>
      Phi233.doubledYHash (2 * offset) (w 0) (modeWord e.1.1 1) -
        2 * Phi233.doubledXHash 0 (w 1) (modeWord e.2.1.1 0) +
        4 * Phi233.doubledZHash offset (w 2) (modeWord e.2.2.1 2)
  | ⟨2, _⟩ =>
      Phi233.doubledZHash (2 * offset) (w 0) (modeWord e.1.1 2) +
        Phi233.doubledYHash 0 (w 1) (modeWord e.2.1.1 1) +
        Phi233.doubledXHash offset (w 2) (modeWord e.2.2.1 0)
  | ⟨r + 3, h⟩ => absurd h (by omega)

noncomputable def exactProfileWordFintype
    (N alpha beta gamma : ℕ) :
    Fintype (ExactProfileWord N alpha beta gamma) :=
  @Subtype.fintype _ _ (Classical.decPred _) Pi.instFintype

noncomputable def cyclicExactEdgeFintype
    (N alpha beta gamma : ℕ) :
    Fintype (CyclicExactEdge N alpha beta gamma) := by
  letI := exactProfileWordFintype N alpha beta gamma
  unfold CyclicExactEdge
  infer_instance

noncomputable def targetFinset
    (N alpha beta gamma : ℕ) :
    Finset (CyclicExactEdge N alpha beta gamma) := by
  letI := cyclicExactEdgeFintype N alpha beta gamma
  exact Finset.univ

end MME.StothersFourth.Phi125


