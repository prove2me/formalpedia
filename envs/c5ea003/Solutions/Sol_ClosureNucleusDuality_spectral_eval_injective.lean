-- Prove2me | solution 1 for ClosureNucleusDuality.spectral_eval_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T23:55:08.049932+00:00
-- url     : https://prove2.me/submissions/35de1872-6d0c-46e3-8236-8ae23bfb7ac1

import Mathlib
import Definitions.Def_Bridges_ClosureNucleusDuality

open Set Function
open ClosureNucleusDuality

variable {α : Type*}

theorem solution (cl : Set α → Set α) (nuc : Set α → Set α)
    (_hcl : IsClosureOperator cl)
    (hsep : PrimeSeparation cl nuc)
    (s t : Set α) (hs : ClosureNucleusDuality.IsClosed cl s)
    (ht : ClosureNucleusDuality.IsClosed cl t)
    (heq : spectralEval cl nuc s = spectralEval cl nuc t) :
    s = t := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxt
    obtain ⟨p, hp, htp, hxp⟩ := hsep t x ht hxt
    have he : (s ⊆ p) = (t ⊆ p) := congrFun heq ⟨p, hp⟩
    exact hxp ((he.mpr htp) hx)
  · intro x hx
    by_contra hxs
    obtain ⟨p, hp, hsp, hxp⟩ := hsep s x hs hxs
    have he : (s ⊆ p) = (t ⊆ p) := congrFun heq ⟨p, hp⟩
    exact hxp ((he.mp hsp) hx)
