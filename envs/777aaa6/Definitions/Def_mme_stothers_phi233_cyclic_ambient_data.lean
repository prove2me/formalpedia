-- Prove2me | Definitions.Def_mme_stothers_phi233_cyclic_ambient_data
-- name    : mme_stothers_phi233_cyclic_ambient_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T22:34:09.670285+00:00
-- url     : https://prove2.me/theorems/b1a2644f-5738-4f5b-b2c7-f1cd44715782
-- title:
--   Cyclic exact and same-marginal edge data for $\varphi_{233}$
-- statement:
--   For a fixed length-$2N$ profile $(\alpha,\beta,\gamma,\delta)$, this module defines the three-copy cyclic hypergraph used in the exceptional $\varphi_{233}$ extraction. Its ambient edges are triples of all supported words with the prescribed three mode marginals, while its exact edges are triples with the selected ten joint multiplicities. It supplies the injective exact-to-ambient inclusion, the three cyclic vertex projections, coordinatewise mixed support, and the canonical construction of a same-marginal mixed address.
--
--   These objects isolate the precise point at which $\varphi_{233}$ differs from the other fourth-power constituents: target joint counts need not be determined by the three marginals, so the ambient completion family is genuinely larger.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Lemma 5.1(v), pp. 356--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data

open MME

namespace MME.StothersFourth.Phi233

set_option autoImplicit false

/-- Three cyclic copies of the full same-marginal completion family. -/
def CyclicAmbientEdge
    (N alpha beta gamma delta : ℕ) : Type :=
  MarginalAddress N alpha beta gamma delta ×
    (MarginalAddress N alpha beta gamma delta ×
      MarginalAddress N alpha beta gamma delta)

/-- Three cyclic copies of the selected exact-profile family. -/
def CyclicExactEdge
    (N alpha beta gamma delta : ℕ) : Type :=
  ExactProfileAddress N alpha beta gamma delta ×
    (ExactProfileAddress N alpha beta gamma delta ×
      ExactProfileAddress N alpha beta gamma delta)

/-- Forget exact joint counts while retaining the three marginal addresses. -/
def exactToAmbient
    {N alpha beta gamma delta : ℕ} :
    CyclicExactEdge N alpha beta gamma delta →
      CyclicAmbientEdge N alpha beta gamma delta :=
  fun e ↦ (e.1.1, (e.2.1.1, e.2.2.1))

theorem exactToAmbient_injective
    {N alpha beta gamma delta : ℕ} :
    Function.Injective
      (exactToAmbient (N := N) (alpha := alpha) (beta := beta)
        (gamma := gamma) (delta := delta)) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun e ↦ e.1) h
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun e ↦ e.2.1) h
    · apply Subtype.ext
      exact congrArg (fun e ↦ e.2.2) h

/-- The inclusion of exact cyclic edges into ambient cyclic edges. -/
def exactEmbedding
    (N alpha beta gamma delta : ℕ) :
    CyclicExactEdge N alpha beta gamma delta ↪
      CyclicAmbientEdge N alpha beta gamma delta where
  toFun := exactToAmbient
  inj' := exactToAmbient_injective

/-- A vertex records one mode word from each of the three cyclic copies. -/
def CyclicModeWord (N : ℕ) : Type :=
  (Fin (2 * N) → Fin 5) ×
    ((Fin (2 * N) → Fin 5) × (Fin (2 * N) → Fin 5))

/-- The three cyclic vertex projections. -/
def cyclicModeWord
    {N alpha beta gamma delta : ℕ}
    (e : CyclicAmbientEdge N alpha beta gamma delta) :
    Fin 3 → CyclicModeWord N
  | ⟨0, _⟩ => (e.1.1 0, (e.2.1.1 2, e.2.2.1 1))
  | ⟨1, _⟩ => (e.1.1 1, (e.2.1.1 0, e.2.2.1 2))
  | ⟨2, _⟩ => (e.1.1 2, (e.2.1.1 1, e.2.2.1 0))
  | ⟨n + 3, h⟩ => absurd h (by omega)

/-- Form a three-mode address by taking mode zero from `x`, mode one from
`y`, and mode two from `z`. -/
def mixedAddress
    {N alpha beta gamma delta : ℕ}
    (x y z : MarginalAddress N alpha beta gamma delta) : ProfileAddress N
  | ⟨0, _⟩, j => x.1 0 j
  | ⟨1, _⟩, j => y.1 1 j
  | ⟨2, _⟩, j => z.1 2 j
  | ⟨n + 3, h⟩, _ => absurd h (by omega)

/-- Coordinatewise support of the three cyclic mixed completions. -/
def CyclicCoordinatewiseSupported
    {N alpha beta gamma delta : ℕ}
    (x y z : CyclicAmbientEdge N alpha beta gamma delta) : Prop :=
  CoordinatewiseSupported (mixedAddress x.1 y.1 z.1) ∧
    CoordinatewiseSupported (mixedAddress y.2.1 z.2.1 x.2.1) ∧
    CoordinatewiseSupported (mixedAddress z.2.2 x.2.2 y.2.2)

/-- A supported modewise mixture of three same-marginal addresses is again a
same-marginal address. -/
def mixedMarginalAddress
    {N alpha beta gamma delta : ℕ}
    (x y z : MarginalAddress N alpha beta gamma delta)
    (hsupport : CoordinatewiseSupported (mixedAddress x y z)) :
    MarginalAddress N alpha beta gamma delta := by
  refine ⟨mixedAddress x y z, hsupport, ?_⟩
  intro i k
  fin_cases i
  · simpa only [mixedAddress] using x.2.2 (0 : Fin 3) k
  · simpa only [mixedAddress] using y.2.2 (1 : Fin 3) k
  · simpa only [mixedAddress] using z.2.2 (2 : Fin 3) k

end MME.StothersFourth.Phi233


