-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIsomorphism.goodMaps_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:09.569328+00:00
-- url     : https://prove2.me/submissions/5f7647b6-0e7a-464b-9513-1f8402dc60e4

import Definitions.Def_Kourovka_Certificates_ComputableIsomorphism
import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_eval_substitute
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_wellFormed
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_append
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_singleton_false
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_valid_append
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_valid_getD
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_valid_substitute

attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIsomorphism
open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism
theorem _root_.solution (p q : PresentationCode) (hp : WellFormed p) (hq : WellFormed q)
    (e : GroupOf p ≃* GroupOf q) :
    ∃ fg : Maps, validMaps ((p, q), fg) ∧ GoodMaps (p, q) fg := by
  classical
  choose f hf using fun i : Fin p.1 => PresentedGroup.mk_surjective (relations q) (e (PresentedGroup.of i))
  choose g hg using fun i : Fin q.1 => PresentedGroup.mk_surjective (relations p) (e.symm (PresentedGroup.of i))
  let F := encodeImages f
  let G := encodeImages g
  have hF : WellFormed (q.1, F) := encodeImages_wellFormed f
  have hG : WellFormed (p.1, G) := encodeImages_wellFormed g
  have hf' : ∀ i : Fin p.1, PresentedGroup.mk (relations q)
      (interpretWord q.1 (F.getD i.val [])) = e (PresentedGroup.of i) := by
    intro i; simpa only [F, interpret_encodeImages_getD] using hf i
  have hg' : ∀ i : Fin q.1, PresentedGroup.mk (relations p)
      (interpretWord p.1 (G.getD i.val [])) = e.symm (PresentedGroup.of i) := by
    intro i; simpa only [G, interpret_encodeImages_getD] using hg i
  refine ⟨(F, G), ⟨hp, hq, encodeImages_length f, encodeImages_length g, hF, hG⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨⟨hq, valid_substitute q.1 F hF w⟩, ?_⟩
    rw [eval_substitute p q e.toMonoidHom F hf' w (hp w hw)]
    rw [PresentedGroup.one_of_mem (List.mem_map.mpr ⟨w, hw, rfl⟩)]
    exact MonoidHom.map_one _
  · intro w hw
    refine ⟨⟨hp, valid_substitute p.1 G hG w⟩, ?_⟩
    rw [eval_substitute q p e.symm.toMonoidHom G hg' w (hq w hw)]
    rw [PresentedGroup.one_of_mem (List.mem_map.mpr ⟨w, hw, rfl⟩)]
    exact MonoidHom.map_one _
  · intro i hi
    have hvi : ValidWord p.1 [(i, false)] := by intro z hz; simpa using List.mem_singleton.mp hz ▸ hi
    refine ⟨⟨hp, valid_append (valid_substitute p.1 G hG _) hvi⟩, ?_⟩
    rw [interpret_append, map_mul, interpret_singleton_false p.1 i hi, map_inv,
      eval_substitute q p e.symm.toMonoidHom G hg' _ (valid_getD q.1 F hF i),
      hf' ⟨i, hi⟩]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, PresentedGroup.of, mul_inv_cancel]
  · intro i hi
    have hvi : ValidWord q.1 [(i, false)] := by intro z hz; simpa using List.mem_singleton.mp hz ▸ hi
    refine ⟨⟨hq, valid_append (valid_substitute q.1 F hF _) hvi⟩, ?_⟩
    rw [interpret_append, map_mul, interpret_singleton_false q.1 i hi, map_inv,
      eval_substitute p q e.toMonoidHom F hf' _ (valid_getD p.1 G hG i),
      hg' ⟨i, hi⟩]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, PresentedGroup.of, mul_inv_cancel]
end Kourovka.MetabelianEnumeration.ComputableIsomorphism
