-- Prove2me | solution 1 for AlmostLossless.decode_never_wrong
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:46:40.437377+00:00
-- url     : https://prove2.me/submissions/574064f3-17d9-4445-a061-c4cdf686a486

import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
open AlmostLossless in
theorem solution {α : Type*} {M : ℕ} {L : List α} {H : α → Fin M} {x y : α}
    (hx : x ∈ L) (h : (decode L H (H x)).1 = some y) : y = x := by
  have hscan : ∀ (d : Fin M) (L : List α),
      (scan H d L).1 = L.filter (fun y => decide (H y = d)) := by
    intro d L
    induction L with
    | nil => rfl
    | cons a t ih =>
      simp only [scan, List.filter_cons, ih]
      split_ifs <;> simp_all
  unfold decode at h
  simp only at h
  split at h
  next v' heq =>
    have hv : v' = y := Option.some.inj h
    subst hv
    rw [hscan] at heq
    have hmem : x ∈ L.filter (fun z => decide (H z = H x)) := List.mem_filter.mpr ⟨hx, by simp⟩
    rw [heq] at hmem
    exact (List.mem_singleton.mp hmem).symm
  next => simp at h
