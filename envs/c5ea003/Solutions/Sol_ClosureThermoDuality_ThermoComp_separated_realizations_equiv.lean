-- Prove2me | solution 1 for ClosureThermoDuality.ThermoComp.separated_realizations_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T01:13:56.619934+00:00
-- url     : https://prove2.me/submissions/7a9a9af2-6f57-45b2-be7d-455256571d79

import Mathlib
import Definitions.Def_Bridges_HilbertSpace_ClosureThermodynamicComputationDuality
open ClosureThermoDuality in
theorem solution {n : ℕ}
    {S₁ S₂ : Type*} [Fintype S₁] [DecidableEq S₁] [Fintype S₂] [DecidableEq S₂]
    (T₁ : ThermoComp S₁ n) (T₂ : ThermoComp S₂ n) (D : DissipData n)
    (hsep₁ : T₁.Separated) (hsep₂ : T₂.Separated)
    (hR₁ : T₁.Realizes D) (hR₂ : T₂.Realizes D) :
    ∃ f : T₁.ClosedSetType → T₂.ClosedSetType,
      Function.Bijective f ∧
      ∀ p, T₁.closedProfile p = T₂.closedProfile (f p) := by
  -- a separated realization labels closed sets bijectively
  have hb₁ : Function.Bijective hR₁.map := by
    refine ⟨fun p q h => Subtype.ext (hsep₁ p.1 q.1 p.2 q.2 ?_), hR₁.map_surj⟩
    have hp := hR₁.map_compat p
    have hq := hR₁.map_compat q
    rw [h] at hp
    exact hp.trans hq.symm
  have hb₂ : Function.Bijective hR₂.map := by
    refine ⟨fun p q h => Subtype.ext (hsep₂ p.1 q.1 p.2 q.2 ?_), hR₂.map_surj⟩
    have hp := hR₂.map_compat p
    have hq := hR₂.map_compat q
    rw [h] at hp
    exact hp.trans hq.symm
  set e₂ := Equiv.ofBijective hR₂.map hb₂
  refine ⟨fun p => e₂.symm (hR₁.map p), e₂.symm.bijective.comp hb₁, fun p => ?_⟩
  -- both profiles equal the data profile of the common label
  rw [hR₁.map_compat p, hR₂.map_compat (e₂.symm (hR₁.map p))]
  congr 1
  exact (Equiv.ofBijective_apply_symm_apply hR₂.map hb₂ _).symm
