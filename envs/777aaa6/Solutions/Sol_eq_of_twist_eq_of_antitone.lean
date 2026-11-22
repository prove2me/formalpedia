-- Prove2me | solution 1 for eq_of_twist_eq_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:20:51.800212+00:00
-- url     : https://prove2.me/submissions/36151f3b-3845-4940-b65c-2e6b2c881e97

import Definitions.Def_BruhatTits_Cartan_Existence
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Cartan_Uniqueness

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable {k : ℕ+}
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
variable {ϖ : R} {hϖ : Irreducible ϖ}
theorem _root_.solution (f g : Fin k → ℤ) (σ : Equiv.Perm (Fin k))
    (hf : Antitone f) (hg : Antitone g) (h : f = g ∘ σ) :
    f = g := by
  subst h
  have : g = g ∘ Equiv.refl _ := rfl
  rw [this] at hg
  nth_rw 2 [this]
  exact Tuple.unique_antitone hf hg
