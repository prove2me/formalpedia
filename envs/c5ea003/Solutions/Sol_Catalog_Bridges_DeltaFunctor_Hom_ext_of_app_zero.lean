-- Prove2me | solution 1 for Catalog.Bridges.DeltaFunctor.Hom.ext_of_app_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T02:18:45.628153+00:00
-- url     : https://prove2.me/submissions/93c067a7-ce87-4588-afa9-125ee67c9b39

import Mathlib
import Definitions.Def_Bridges_ExtDeltaFunctor

universe w v u

set_option maxHeartbeats 1000000 in
open Catalog.Bridges CategoryTheory Category Limits Abelian in
theorem solution {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {T S : DeltaFunctor.{w} C} (hT : T.Effaceable)
    (φ ψ : T.Hom S) (h0 : φ.app 0 = ψ.app 0) : ∀ n, φ.app n = ψ.app n := by
  -- the canonical embedding `0 → Y → I → I/Y → 0` is short exact
  have hse : ∀ Y : C, (DeltaFunctor.injectiveEmbedding Y).ShortExact := by
    intro Y
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact ShortComplex.exact_cokernel (Injective.ι Y)
    · exact Injective.ι_mono Y
    · exact coequalizer.π_epi
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    refine NatTrans.ext (funext fun Y => ?_)
    -- `T.F (n+1)` kills the injective middle term, so the connecting map is epi
    have hzero : IsZero ((T.F (n + 1)).obj (DeltaFunctor.injectiveEmbedding Y).X₂) :=
      hT (Injective.under Y) (Injective.injective_under Y) n
    have hg0 : (T.F (n + 1)).map (DeltaFunctor.injectiveEmbedding Y).f = 0 :=
      hzero.eq_zero_of_tgt _
    have hδ : Epi (T.δ (hse Y) n) := (T.exact₁ (hse Y) n).epi_f hg0
    -- both morphisms have the same composite with that epi
    have h1 := φ.comm (hse Y) n
    have h2 := ψ.comm (hse Y) n
    rw [ih] at h1
    exact (cancel_epi (T.δ (hse Y) n)).mp (h1.trans h2.symm)
